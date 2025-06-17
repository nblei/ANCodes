from pyverilog.vparser.parser import parse
import pyverilog.vparser.ast as vast
import sys, json, re
from z3 import *
from sympy import primerange


BVURem = globals().get("BVURem", URem)
CELL2FUNC = {
    "BUF":   lambda A:  A,
    "CLKBUF":lambda A:  A,
    "INV":   lambda A:  Not(A),
    "AND2":  lambda A1, A2: And(A1, A2),
    "AND3":  lambda A1, A2, A3: And(A1, A2, A3),
    "AOI21": lambda A, B1, B2: Not(Or(A, And(B1, B2))),
    "AOI211":lambda A, B, C1, C2: Not(Or(A, Or(B, And(C1, C2)))),
    "AOI22": lambda A1, A2, B1, B2: Not(Or(And(A1, A2), And(B1, B2))),
    "AOI221":lambda A, B1, B2, C1, C2: Not(Or(Or(A, And(C1, C2)), And(B1, B2))),
    "NAND2": lambda A1, A2: Not(And(A1, A2)),
    "NAND3": lambda A1, A2, A3: Not(And(A1, A2, A3)),
    "NAND4": lambda A1, A2, A3, A4: Not(And(A1, A2, A3, A4)),
    "NOR2":  lambda A1, A2: Not(Or(A1, A2)),
    "NOR3":  lambda A1, A2, A3: Not(Or(A1, A2, A3)),
    "NOR4":  lambda A1, A2, A3, A4: Not(Or(A1, A2, A3, A4)),
    "OAI21": lambda A, B1, B2: Not(And(Or(B1, B2), A)),
    "OAI211":lambda A, B, C1, C2: Not(And(B, And(A, Or(C1, C2)))),
    "OAI22": lambda A1, A2, B1, B2: Not(And(Or(A1, A2), Or(B1, B2))),
    "OAI33": lambda A1, A2, A3, B1, B2, B3: Not(And(Or(A1,A2,A3), Or(B1,B2,B3))),
    "OR2":   lambda A1, A2: Or(A1, A2),
    "OR3":   lambda A1, A2, A3: Or(A1, A2, A3),
    "XOR2":  lambda A, B: Xor(A, B),
    "XNOR2": lambda A, B: Not(Xor(A, B)),
}

for name in list(CELL2FUNC):
    for drv in ("_X1", "_X2", "_X4", "_X8"):
        CELL2FUNC[name + drv] = CELL2FUNC[name]

OUTPUT_PORTS = ("Y","ZN","Z")
primary_inputs = { f"a[{i}]" for i in range(64) } | { f"b[{i}]" for i in range(64) } | {"carry_in"}
primary_outputs = { f"s[{i}]" for i in range(64) } | {"carry_out"}


def build_z3_from_verilog(*vg_files):
    ast, _ = parse(list(vg_files))
    nets, gates, flips = {}, {}, {}

    def pin_name(obj):
        if isinstance(obj, vast.Pointer): return f"{obj.var}[{obj.ptr}]"
        if isinstance(obj, vast.IntConst):
            print("**")
            return obj.value
        if obj is None: return "1'b0"  # Port left open ➜ treat as 0

        if isinstance(obj, vast.Partselect):
            msb, lsb = int(obj.msb), int(obj.lsb)
            bits = [net(f"{obj.var}[{i}]") for i in range(msb, lsb-1, -1)]
            return Concat(*map(as_bv1, bits))     
        return str(obj)

    def net(name):
        if name in ("1'b0", "1’b0", "0", "1’b0 "):
            return BoolVal(False)
        if name in ("1'b1", "1’b1", "1", "1’b1 "):
            return BoolVal(True)
        if name in nets:
            return nets[name]

        if name in primary_inputs or name in primary_outputs:
            raw = Bool(name)
            nets[name] = (raw, raw)       # faulty == raw
            return nets[name]

        raw   = Bool(f"raw_{name}")       # golden value
        flip  = Bool(f"flip_{name}")      # fault enable (added to flips dict)
        faulty= Xor(raw, flip)            # observed value downstream
        nets[name] = (raw, faulty)        # store the pair
        flips[name] = flip                # remember the enable
        return nets[name]

    for mod in ast.description.definitions:
        if mod.__class__.__name__ != "ModuleDef": continue
        for item in mod.items:
            if item.__class__.__name__ != "InstanceList": continue
            if item.module not in CELL2FUNC:
                raise ValueError(f"Unknown gate: {item.module}")
            fn = CELL2FUNC[item.module]
            for inst in item.instances:
                conn    = {p.portname: pin_name(p.argname) for p in inst.portlist}
                out_pin = next(p for p in OUTPUT_PORTS if p in conn)
                ordered = [p for p in sorted(conn) if p != out_pin]

                out_raw, out_faulty = net(conn[out_pin])
                args_faulty         = [ net(conn[p])[1] for p in ordered ]  # take faulty version of inputs
                gates[inst.name] = out_raw == CELL2FUNC[item.module](*args_faulty)
    return nets, list(gates.values()), flips

def as_bv1(b):
    return If(b, BitVecVal(1, 1), BitVecVal(0, 1))

def bus(nets, base, width, idx=1, big_endian=True):
    """
    Return a concatenation of 'width' single-bit nets.
      idx = 0  → raw (golden) signals
      idx = 1  → faulty-after-flip signals   ← default, because most
                                              nets feed forward as 'faulty'
    """
    rng = range(width-1, -1, -1) if big_endian else range(width)
    bits = [ as_bv1(nets[f"{base}[{i}]"][idx]) for i in rng ]
    return Concat(*bits)

def bus_faulty(nets, name, width):
    # index 1 = faulty
    return Concat(*( as_bv1(nets[f"{name}[{i}]"][1]) for i in range(width-1, -1, -1) ))

def adder_checker(vg_file: str, one_hot: bool) -> None:
    nets, gates, flips = build_z3_from_verilog(vg_file)
    print("signals:", len(nets), "gates:", len(gates), flush=True)
    W = 64
    a = BitVec("a_eq", W)
    b = BitVec("b_eq", W)
    faulty_sum = bus_faulty(nets, "s", W)
    gold_sum   = a + b

    eq_solver = Solver()
    eq_solver.add(*gates)
    bus_a_raw = bus(nets, "a", W, idx=0)
    bus_b_raw = bus(nets, "b", W, idx=0)

    # constrain them to match your BitVecs
    eq_solver.add(bus_a_raw == a)
    eq_solver.add(bus_b_raw == b)

    # set carry_in to 0
    carry_raw, carry_faulty = nets["carry_in"]
    eq_solver.add(Not(carry_faulty))

    error = gold_sum - faulty_sum
    is_neg = Extract(W-1,W-1,error) == BitVecVal(1,1)
    abs_err = If(is_neg, -error, error)

    ############### TEMPORARY CONSTRAINTS ###############
    # non-zero inputs
    # eq_solver.add(a != 0) 
    # eq_solver.add(b != 0)
    # eq_solver.add(abs_err != BitVecVal(0, W)) # non-zero error
    # eq_solver.add((abs_err & (abs_err - BitVecVal(1, W))) != 0) # non-power-of-two error

    # fault injection
    flip_vars = list(flips.values())
    if one_hot:
        one_hot_sym = Sum(*(If(f, 1, 0) for f in flip_vars)) == 1
        eq_solver.add(one_hot_sym)
    else:
        for flip_var in flip_vars:
            eq_solver.add(Not(flip_var))

    # SAT when it differs
    eq_solver.add(faulty_sum != gold_sum)

    # prevent overflow
    eq_solver.add(Extract(63, 63, a) == BitVecVal(0, 1))
    eq_solver.add(Extract(63, 63, b) == BitVecVal(0, 1))

    res = eq_solver.check()
    if res == sat:
        model = eq_solver.model()
        print("❌ Equivalence FAILED!  Counterexample:")

        fired = [ name
                  for name, flip_sym in flips.items()
                  if model.evaluate(flip_sym) == True ]

        print("  active flip :", ", ".join(fired) or "-- none --")
        print("  a      =", model[a].as_long())
        print("  b      =", model[b].as_long())
        print("  faulty =", model.eval(faulty_sum).as_long())
        print("  golden =", model.eval(gold_sum).as_long())
        print("  abs_e  =", model.eval(abs_err).as_long())
        sys.exit(1)
    elif res == unsat:
        print("✅ Transformation is FUNCTIONALLY EQUIVALENT to a+b (no flips).")
    else:
        print("UNKNOWN")


def arithmetic_weight_int(val: int, width: int = 64) -> int:
    temp   = val & ((1 << width) - 1)
    weight = 0
    while temp & (temp >> 1): # replace with for loop in the bitvec
        run_loc = (temp & -temp).bit_length() - 1
        temp   += 1 << run_loc
        weight += 1
    return weight + temp.bit_count()

def popcount_bv(x: BitVecRef) -> ArithRef:
    w = x.size()
    # Sum_{i=0}^{w-1}  (x[i] ? 1 : 0)
    bits_as_ints = [
        If(Extract(i, i, x) == BitVecVal(1, 1), 1, 0)  # each term is an Int
        for i in range(w)
    ]
    return Sum(*bits_as_ints)

def arithmetic_weight_symbv(x):
    w       = x.size()
    xi      = ZeroExt(1, x)          # work in W+1 bits
    carries = IntVal(0)

    for _ in range(w):               # at most W carries needed
        two  = xi & (xi >> 1)        # bits where a run starts
        no   = (two == 0)
        lsb  = two & -two
        xi   = If(no, xi, xi + lsb)
        carries = If(no, carries, carries + 1)

    low_w  = Extract(w-1, 0, xi)     # drop guard bit
    pop    = popcount_bv(low_w)
    return carries + pop


def solver(vg_file: str) -> None:
    nets, gates, flips = build_z3_from_verilog(vg_file)
    print("signals:", len(nets), "gates:", len(gates), flush=True)
    W = 64
    a = BitVec("a_eq", W)
    b = BitVec("b_eq", W)
    e = BitVec("e_eq", W)
    ka = BitVec("ka_eq", W)
    kb = BitVec("kb_eq", W)
    ke = BitVec("ke_eq", W)
    faulty_sum = bus_faulty(nets, "s", W)
    gold_sum   = a + b

    eq_solver = Solver()
    eq_solver.add(*gates)
    bus_a_raw = bus(nets, "a", W, idx=0)
    bus_b_raw = bus(nets, "b", W, idx=0)

    # constrain them to match your BitVecs
    eq_solver.add(bus_a_raw == a)
    eq_solver.add(bus_b_raw == b)

    # set carry_in to 0
    carry_raw, carry_faulty = nets["carry_in"]
    eq_solver.add(Not(carry_faulty))

    # fault injection
    flip_vars = list(flips.values())
    one_hot_sym = Sum(*(If(f, 1, 0) for f in flip_vars)) == 1
    eq_solver.add(one_hot_sym)

    # SAT when error is a codeword
    error = gold_sum - faulty_sum
    is_neg = Extract(W-1,W-1,error) == BitVecVal(1,1)
    abs_err = If(is_neg, -error, error)
    eq_solver.add(e == abs_err)

    # prevent overflow
    eq_solver.add(Extract(63, 63, a) == BitVecVal(0, 1))
    eq_solver.add(Extract(63, 63, b) == BitVecVal(0, 1))

    # non-zero error
    eq_solver.add(abs_err != BitVecVal(0, W))

    # specify arithmetic weight
    ar_weight = 4
    eq_solver.add(arithmetic_weight_symbv(abs_err) == ar_weight)


    # eq_solver.add(a != 0)
    # eq_solver.add(b != 0)
    # eq_solver.add((abs_err & (abs_err - BitVecVal(1, W))) != 0)
    # TOP = (1 << 30) - 1                 # 0x3FFF FFFF
    # eq_solver.add( ULE(a, BitVecVal(TOP, 64)) )
    # eq_solver.add( ULE(b, BitVecVal(TOP, 64)) )


    LOWER = 63611 # 49999
    UPPER = 63612 # 50025
    A_list = list(primerange(LOWER, UPPER + 1)) # 63611

    for A in A_list:
        print(f"\n=== A = {A} ===", flush=True)
        eq_solver.push()

        # inputs and error are codewords
        B_max = (2**W - 1) // A
        eq_solver.add(a == ka * A)
        eq_solver.add(b == kb * A)
        eq_solver.add(e == ke * A)

        # ensures k's don't overflow
        eq_solver.add( ULE(ka, BitVecVal(B_max, W)) )
        eq_solver.add( ULE(kb, BitVecVal(B_max, W)) )
        eq_solver.add( ULE(ke, BitVecVal(B_max, W)) )

        # increase efficiency by constraining higher order bits 
        K_BITS = (W - A.bit_length())
        eq_solver.add(Extract(63, K_BITS, ka) == 0)
        eq_solver.add(Extract(63, K_BITS, kb) == 0)
        eq_solver.add(Extract(63, K_BITS, ke) == 0)

        # A_inv = pow(A, -1, 2**W)
        # eq_solver.add( ka == a * BitVecVal(A_inv, W),
        #         ULE(ka, BitVecVal(B_max, W)) )
        # eq_solver.add( kb == b * BitVecVal(A_inv, W),
        #         ULE(kb, BitVecVal(B_max, W)) )
        # eq_solver.add( ke == e * BitVecVal(A_inv, W),
        #         ULE(ke, BitVecVal(B_max, W)) )

        res = eq_solver.check()
        if res == sat:
            model = eq_solver.model()
            print(f"❌ Undetectable errors can happen with A = {A} and adder = {vg_file[6:-3]}", flush=True)
            fired = [ name
                    for name, flip_sym in flips.items()
                    if model.evaluate(flip_sym) == True ]

            print("  active flip :", ", ".join(fired) or "-- none --", flush=True)
            print("  a      =", model[a].as_long(), flush=True)
            print("  b      =", model[b].as_long(), flush=True)
            print("  faulty =", model.eval(faulty_sum).as_long(), flush=True)
            print("  golden =", model.eval(gold_sum).as_long(), flush=True)
            print("  abs_e  =", model.eval(abs_err).as_long(), flush=True)
            print("  AW(e)  =", arithmetic_weight_int(model.eval(abs_err).as_long()), flush=True)
            print("  ka     =", model[ka].as_long(), flush=True)
            print("  kb     =", model[kb].as_long(), flush=True)
            print("  ke     =", model[ke].as_long(), flush=True)
        elif res == unsat:
            print(f"✅ No Undetectable errors with A = {A}, ar_weight = {ar_weight}, adder = {vg_file[6:-3]}", flush=True)
        else:
            print("UNKNOWN", flush=True)

        eq_solver.pop()


def main():
    
    for vg_file in [ "synth/ripple_carry_adder.vg", "synth/carry_select_adder.vg", "synth/kogge_stone_adder.vg"]:
        print(f"===== Checking module {vg_file[6:-3]} =====", flush=True)
        # adder_checker(vg_file, one_hot=False)

        solver(vg_file)

    

    # def check(val):
    #     x  = BitVec('x', 64)
    #     wt = arithmetic_weight_symbv(x)

    #     s = Solver()
    #     s.add(x == BitVecVal(val, 64))
    #     assert s.check() == sat
    #     return s.model().evaluate(wt).as_long()

    # v = 6917529027641081856
    # print("int version :", arithmetic_weight_int(v))   # → 3
    # print("symb version:", check(v))   

   

if __name__ == "__main__":
    main()
