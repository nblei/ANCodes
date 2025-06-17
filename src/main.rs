#![feature(trait_alias)]

use std::{
    fmt::Write as _,
    fs::File,
    io::{self, BufWriter, Write},
    path::PathBuf,
    sync::{
        atomic::{AtomicBool, AtomicU64, Ordering},
        Arc, Mutex,
    },
    thread,
    time::{Duration, Instant},
    collections::BTreeMap,
};

use clap::{Parser, Subcommand, ValueEnum};

/// use an_macros::define_distance_fn;

// ADDED
/// Miller–Rabin
fn is_prime(n: u128) -> bool {
    // Small even / trivial cases first
    if n < 2 || n & 1 == 0 { return n == 2; }

    // Bases that make MR deterministic for n < 2^128
    // (Jaeschke 1993, Sorenson–Webster 2015)
    const BASES: &[u128] =
        &[2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37];

    // Write n-1 as d·2^s with d odd
    let s = (n - 1).trailing_zeros();
    let d = (n - 1) >> s;

    'next_base: for &a in BASES.iter() {
        if a >= n { break; }                 // all remaining a >= n are useless
        let mut x = modpow(a % n, d, n);
        if x == 1 || x == n - 1 { continue 'next_base; }
        for _ in 1..s {
            x = modmul(x, x, n);
            if x == n - 1 { continue 'next_base; }
        }
        return false;                        // definitely composite
    }
    true                                      // passed all bases ⇒ prime
}

/// (Montgomery-less) multiply-mod for u128 – shift/peasant algorithm
#[inline]
fn modmul(mut a: u128, mut b: u128, m: u128) -> u128 {
    let mut r = 0u128;
    while b != 0 {
        if b & 1 != 0 { r = (r + a) % m; }
        a = (a << 1) % m;
        b >>= 1;
    }
    r
}

/// Modular exponentiation
fn modpow(mut a: u128, mut e: u128, m: u128) -> u128 {
    let mut r = 1u128;
    while e != 0 {
        if e & 1 != 0 { r = modmul(r, a, m); }
        a = modmul(a, a, m);
        e >>= 1;
    }
    r
}

fn enumerate_errors(
    a: u64,
    bits: u64,
    max_weight: usize,
) -> Vec<(usize, u128, u32)> {
    let needed_bits = bits + f64::ceil(f64::log2(a as f64)) as u64;
    let mut out = Vec::new();
    for w in 1..=max_weight.max(1 << 5) {            // reasonable upper found weight
        let mut adg = ArithmeticDistanceGenerator::new(w, needed_bits as usize);
        adg.set_strict(true);
        let mut found = false;
        if needed_bits > 64 {
            for codeword in adg.iter::<u128>() {
                if codeword % a as u128 == 0 {
                    out.push((w, codeword, fast_arithmetic_weight(codeword) as u32));
                    found = true;
                }
            }
        } else {
            for codeword in adg.iter::<u64>() {
                if codeword % a == 0 {
                    let cw = codeword as u128;
                    out.push((w, cw, fast_arithmetic_weight(cw) as u32));
                    found = true;
                }
            }
        }
        if max_weight == 0 && found { break; }       // auto-stop
        if max_weight != 0 && w == max_weight { break; }
    }
    out
}


/// AN Codes Analysis Tool for error detection and correction
#[derive(Parser)]
#[command(name = "an_codes")]
#[command(author = "AN Codes Research Team")]
#[command(version)]
#[command(about = "Analyzes properties of AN codes for error detection and correction", long_about = None)]
struct Cli {
    /// Operation mode
    #[command(subcommand)]
    command: Command,

    /// Enable verbose output
    #[arg(short, long, global = true)]
    verbose: bool,
}

#[derive(Subcommand)]
enum Command {
    /// Run standard AN code analysis
    Analyze {
        /// Maximum value of 'a' to analyze (default: 2^20)
        #[arg(short, long, default_value_t = 1 << 20)]
        a_limit: u64,

        /// Number of bits in the pointer (default: 64)
        #[arg(short, long, default_value_t = 64)]
        bits: u64,

        /// Number of threads to use (default: available CPU cores)
        #[arg(short, long, default_value_t = num_cpus::get() as u64)]
        threads: u64,

        /// Output file for results
        #[arg(short, long, default_value = "results.txt")]
        output: PathBuf,
    },

    AnalyzeSingle {
        #[arg()]
        a: u64,
        #[arg(default_value_t = 64)]
        bits: u64,
    },

    /// Run misconstruction analysis
    Misconstruct {
        /// Type of misconstruction analysis to run
        #[arg(value_enum)]
        analysis_type: MisconstructionType,
    },

    /// Generate all un-detectable errors for a single A up to a given weight
    /// and print each witness together with its arithmetic weight.
    GenerateAllErrors {
        #[arg(short, long, default_value_t = 64)]
        bits: u64,

        // number of consecutive weight‐classes
        #[arg(short = 'n', long, default_value_t = 1)]
        num_weights: usize,

        #[arg(short, long, default_value = "all_errors.txt")]
        output: PathBuf,
        
        #[arg(short, long, default_value_t = num_cpus::get() as u64)]
        threads: u64,

        #[arg(long, default_value_t = 3_500)]
        min_a: u64,

        #[arg(long, default_value_t = 1u64 << 17)]
        max_a: u64,
    },
}

#[derive(Copy, Clone, PartialEq, Eq, ValueEnum)]
enum MisconstructionType {
    /// Two-bit error misconstructions
    TwoBit,
    /// Three-bit error misconstructions
    ThreeBit,
    /// Four-bit error misconstructions
    FourBit,
}
use num_traits::{
    cast::AsPrimitive,
    ops::wrapping::{WrappingAdd, WrappingNeg},
    PrimInt, WrappingShl,
};

trait Arithmetic =
    WrappingAdd + WrappingNeg + WrappingShl + PrimInt + Copy + 'static + AsPrimitive<u32> + Clone;

#[derive(Clone, Debug)]
struct ArithmeticDistanceGenerator {
    weight: usize,
    bitwidth: usize,
    strict: bool, // Turn on to ensure exactly `weight` weights are generated
}

#[derive(Clone, Debug)]
struct ArithmeticDistanceIterator<T: Arithmetic>
where
    u32: AsPrimitive<T>,
{
    weight: u32,
    bitwidth: usize,
    polarity: usize,
    loop_counters: Vec<u32>,
    total_count: usize,
    limit_count: usize,
    strict: bool, // Turn on to ensure exactly `weight` weights are generated
    bases: [[T; 128]; 2],
}

impl<T: Arithmetic> ArithmeticDistanceIterator<T>
where
    u32: AsPrimitive<T>,
{
    pub fn new(size: usize, bitwidth: usize) -> Self {
        Self {
            weight: size as u32,
            bitwidth,
            polarity: 0,
            loop_counters: (0u32..size as u32).collect(),
            total_count: 0,
            limit_count: Self::compute_limit_count(size, bitwidth),
            strict: true,
            bases: get_bases::<T>(),
        }
    }

    pub fn set_strict(&mut self, b: bool) {
        self.strict = b
    }

    fn compute_limit_count(size: usize, bitwidth: usize) -> usize {
        // Handle edge cases
        if size == 0 {
            return 1; // Only one way to choose 0 elements (empty set)
        }

        if size > bitwidth {
            return 0; // Can't choose more elements than available
        }

        // Calculate the number of ways to choose 'size' positions from 'bitwidth' positions
        // This is the binomial coefficient C(bitwidth, size)
        let mut combinations = 1;

        // Computing bitwidth choose size
        // prod_{i=1}^k \frac{n-(k-i)}{i}
        for i in 1..=size {
            combinations *= (bitwidth - (size - i)) / i;
        }

        // For each position combination, we have 2^size possible polarity combinations
        combinations * (1 << size)
    }

    fn increment_state(&mut self) {
        // Update for next iteration
        self.total_count += 1;

        // First increment the polarity
        self.polarity += 1;

        // If we've exhausted all polarities, move to the next position combination
        if self.polarity >= (1 << self.weight) {
            self.polarity = 0;

            // Increment positions like an odometer, ensuring they stay in ascending order
            // (i0 < i1 < i2 < ...)

            // Start from the last digit and try to increment it
            let mut pos = self.weight as usize - 1usize;

            // Try to increment current position
            loop {
                // Maximum value for this position
                let max_val = self.bitwidth - (self.weight as usize - 1 - pos);
                if max_val > 128 {
                    panic!("Cannot support total bitwidth > 128 bits");
                }

                // Increment this position
                self.loop_counters[pos] += 1;

                // If we can increment without overflow, we're done
                if self.loop_counters[pos] < max_val as u32 {
                    break;
                }

                // Otherwise, we need to carry and continue with the previous position
                if pos == 0 {
                    // We've exhausted all positions
                    // This will be the last element returned by the iterator
                    return; //  Some(sum);
                }

                // Move to previous position
                pos -= 1;
            }

            // Now reset all subsequent positions to their minimum values
            // (each position must be greater than the previous one)
            for i in (pos + 1)..(self.weight as usize) {
                self.loop_counters[i] = self.loop_counters[i - 1] + 1;
            }
        }
    }
}

impl<T: Arithmetic> Iterator for ArithmeticDistanceIterator<T>
where
    u32: AsPrimitive<T>,
{
    type Item = T;

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            if self.total_count >= self.limit_count {
                return None;
            }

            // Determine polarities of each variable and calculate sum
            let mut sum = T::zero();
            for alpha in 0..self.weight {
                let polarity = (self.polarity >> alpha) & 1;
                sum = sum.wrapping_add(
                    &self.bases[polarity][self.loop_counters[alpha as usize] as usize],
                );
            }
            self.increment_state();
            if fast_arithmetic_weight(sum) == T::from(self.weight).unwrap() || !self.strict {
                return Some(sum);
            }
        }
    }
}

impl ArithmeticDistanceGenerator {
    pub fn new(weight: usize, bitwidth: usize) -> Self {
        Self {
            weight,
            bitwidth,
            strict: true,
        }
    }

    pub fn iter<T: Arithmetic>(&self) -> ArithmeticDistanceIterator<T>
    where
        u32: AsPrimitive<T>,
    {
        ArithmeticDistanceIterator::<T>::new(self.weight, self.bitwidth)
    }

    pub fn set_strict(&mut self, b: bool) {
        self.strict = b
    }
}

struct ThreadProgress {
    current: AtomicU64,
    total: u64,
}

struct ProgressTracker {
    threads: Vec<ThreadProgress>,
    start_time: Instant,
    should_stop: AtomicBool,
}

impl ProgressTracker {
    fn new(num_threads: usize, thread_totals: Vec<u64>) -> Self {
        let threads = (0..num_threads)
            .map(|id| ThreadProgress {
                current: AtomicU64::new(0),
                total: thread_totals[id],
            })
            .collect();

        Self {
            threads,
            start_time: Instant::now(),
            should_stop: AtomicBool::new(false),
        }
    }

    fn display_progress(&self) {
        // Clear previous lines and move cursor to top
        print!("\x1B[2J\x1B[1;1H");

        // Calculate overall progress
        let total_progress: u64 = self
            .threads
            .iter()
            .map(|p| p.current.load(Ordering::Relaxed))
            .sum();
        let total_work: u64 = self.threads.iter().map(|p| p.total).sum();

        let percentage = (total_progress as f64 / total_work as f64 * 100.0) as u32;

        let elapsed = self.start_time.elapsed().as_secs();
        if elapsed > 0 {
            let items_per_sec = total_progress as f64 / elapsed as f64;
            let remaining_items = total_work - total_progress;
            let eta_secs = if items_per_sec > 0.0 {
                remaining_items as f64 / items_per_sec
            } else {
                0.0
            };

            println!(
                "Overall Progress: {}% [{}/{}]",
                percentage, total_progress, total_work
            );
            println!("Processing speed: {:.2} items/sec", items_per_sec);
            println!("Estimated time remaining: {:.2} minutes", eta_secs / 60.0);
        }

        // Per-thread progress
        println!("\nPer-thread progress:");
        for (i, progress) in self.threads.iter().enumerate() {
            let current = progress.current.load(Ordering::Relaxed);
            let thread_percentage = (current as f64 / progress.total as f64 * 100.0) as u32;
            println!(
                "Thread {}: {}% [{}/{}]",
                i, thread_percentage, current, progress.total
            );
        }

        io::stdout().flush().unwrap();
    }
}

fn get_bases<T: Arithmetic>() -> [[T; 128]; 2]
where
    u32: AsPrimitive<T>,
{
    let limit = if std::mem::size_of::<T>() <= 8 {
        64
    } else {
        128
    };
    [
        {
            let mut arr = [T::zero(); 128];
            let mut i = 0;
            while i < limit {
                arr[i] = T::one() << i;
                i += 1;
            }
            arr
        },
        {
            let mut arr = [T::zero(); 128];
            let mut i = 0;
            while i < limit {
                arr[i] = (!(T::one() << i)) + T::one();
                i += 1;
            }
            arr
        },
    ]
}

fn get_first_sequence<T: Arithmetic>(x: T) -> Option<T>
where
    u32: AsPrimitive<T>,
{
    // Find all positions where consecutive 1's exist
    let consecutive: T = x & (x >> 1);

    let zero: T = T::from(0u64).unwrap();
    if consecutive == zero {
        return None;
    }

    // Get the least significant position of a consecutive pair
    let ls_consecutive = consecutive & consecutive.wrapping_neg();

    // First 1 in the sequence will be at the same position as ls_consecutive
    let result: T = ls_consecutive.trailing_zeros().as_();
    Some(result)
}

fn fast_arithmetic_weight<T: Arithmetic>(mut x: T) -> T
where
    u32: AsPrimitive<T>,
{
    let mut result = 0;

    let one: T = T::from(1u64).unwrap();
    while let Some(start) = get_first_sequence(x) {
        x = x.wrapping_add(&one.wrapping_shl(start.as_()));
        result += 1;
    }

    // Add remaining 1 bits
    result += x.count_ones();
    result.as_()
}

#[derive(Debug, Clone)]
enum UncorrectableError {
    Count(u64),
    Errors(Vec<u128>),
}

impl UncorrectableError {
    pub fn len(&self) -> usize {
        match self {
            UncorrectableError::Count(x) => *x as usize,
            UncorrectableError::Errors(vec) => vec.len(),
        }
    }

    pub fn insert_error(&mut self, error: u128) {
        match self {
            UncorrectableError::Count(x) => {
                *x = *x + 1u64;
            }
            UncorrectableError::Errors(items) => {
                items.push(error);
            }
        }
    }

    pub fn to_count(&mut self) {
        *self = match self {
            UncorrectableError::Count(x) => UncorrectableError::Count(*x),
            UncorrectableError::Errors(items) => UncorrectableError::Count(items.len() as u64),
        };
    }
}

#[derive(Debug, Clone)]
struct AnCode {
    a: u64,
    bits: u64, // Number of bits in a Physical Pointer
    errors: Vec<UncorrectableError>,
    bailed_out: bool, // True if did not complete analysis
}

impl AnCode {
    const MAX_ERRORS: usize = 2400;

    fn to_csv_line(&self) -> String {
        let mut s = String::new();
        write!(&mut s, "{}", self.a).unwrap();

        for i in 0..=Self::MAX_ERRORS {
            if self.errors.len() > i {
                write!(
                    &mut s,
                    ",{}",
                    match &self.errors[i] {
                        UncorrectableError::Count(x) => (*x) as usize,
                        UncorrectableError::Errors(items) => items.len(),
                    }
                )
                .unwrap();
            } else {
                write!(&mut s, ",").unwrap();
            }
        }
        writeln!(&mut s, "").unwrap();
        s
    }

    fn new(a: u64, bits: u64) -> Self {
        let errors = vec![];
        let mut s = Self {
            a,
            bits,
            errors,
            bailed_out: false,
        };
        let needed_bits = bits + f64::ceil(f64::log2(a as f64)) as u64;
        let t128 = needed_bits > 64;
        let mut loop_count = 1;
        loop {
            let mut found = false;
            let adg = ArithmeticDistanceGenerator::new(loop_count, needed_bits as usize);
            if t128 {
                let a = a as u128;
                for codeword in adg.iter::<u128>() {
                    if codeword % a == 0 {
                        s.add_error(codeword, loop_count);
                        found = true;
                    }
                }
            } else {
                let a = a as u64;
                for codeword in adg.iter::<u64>() {
                    if codeword % a == 0 {
                        s.add_error(codeword as u128, loop_count);
                        found = true;
                    }
                }
            }
            if found {
                break;
            }
            loop_count += 1;
        }
        s
    }

    fn add_error(&mut self, witness: u128, weight: usize) {
        while self.errors.len() <= weight {
            self.errors.push(UncorrectableError::Errors(vec![]));
        }
        match &mut self.errors[weight] {
            UncorrectableError::Count(x) => *x += 1,
            UncorrectableError::Errors(vec) => {
                if vec.len() < Self::MAX_ERRORS {
                    vec.push(witness);
                } else {
                    self.errors[weight] = UncorrectableError::Count((Self::MAX_ERRORS + 1) as u64);
                }
            }
        }
    }

    fn get_errors_counts(&self) -> Vec<u64> {
        self.errors.iter().map(|e| e.len() as u64).collect()
    }
}

#[derive(Debug, Clone)]
struct Experiment {
    bits: u64,
    results: Vec<AnCode>,
}

impl Experiment {
    fn new(alimit: u64, bits: u64, num_threads: u64) -> Self {
        let min = 3;
        let max = alimit;
        let chunk = (max - min + 1) / num_threads;
        let results = Arc::new(Mutex::new(Vec::new()));

        // Calculate actual total work for each thread
        let mut thread_totals = Vec::new();
        for i in 0..num_threads {
            let start = ((min + chunk * i) / 2) * 2 + 1;
            let end = if i == num_threads - 1 {
                max
            } else {
                start + chunk
            };
            thread_totals.push((end - start + 1) / 2);
        }

        let progress = Arc::new(ProgressTracker::new(num_threads as usize, thread_totals));
        let mut handles = vec![];

        for i in 0..num_threads {
            let results = Arc::clone(&results);
            let progress = Arc::clone(&progress);
            let thread_id = i as usize;

            let handle = thread::spawn(move || {
                let mut thread_results = Vec::new();
                let mut items_processed = 0;
                let mut idx = min;

                while idx < max {
                    let a = idx + (thread_id * 2) as u64;
                    // ADDED
                    if a > 1 << 17 || !is_prime(a as u128){
                        idx += num_threads * 2;
                        continue;
                    }
                    let ac = AnCode::new(a, bits);
                    if ac.errors[0].len() == 0
                        && ac.errors[1].len() == 0
                        && ac.errors[2].len() == 0
                        && ac.errors[3].len() < 100
                    {
                        thread_results.push(ac);
                    }
                    idx += num_threads * 2;
                    items_processed += 1;

                    if items_processed % 0x03F == 0 {
                        progress.threads[thread_id]
                            .current
                            .store(items_processed, Ordering::Relaxed);
                    }
                }
                // Final progress update
                progress.threads[thread_id]
                    .current
                    .store(items_processed, Ordering::Relaxed);
                let mut results = results.lock().unwrap();
                results.extend(thread_results);
            });
            handles.push(handle);
        }

        // Start progress display thread
        let progress_clone = Arc::clone(&progress);
        let _progress_handle = thread::spawn(move || {
            while progress_clone.should_stop.load(Ordering::Relaxed) == false {
                thread::sleep(Duration::from_millis(500));
                progress_clone.display_progress();
            }
        });

        for handle in handles {
            handle.join().unwrap();
        }
        let results = Arc::try_unwrap(results).unwrap().into_inner().unwrap();
        Self { bits, results }
    }
}

// Want to count the number of 2-bit errors which are misconstrued as correctable
// one bit errors
fn two_bit_misconstrued() -> (u64, u64) {
    let mut total = 0;
    let mut misconstrued = 0;
    let bases = get_bases::<u64>();
    for alpha in 0..(1 << 2) {
        let a0 = (alpha >> 0) & 1;
        let a1 = (alpha >> 1) & 1;
        for i0 in 0..64 {
            let v0 = bases[a0][i0];
            for i1 in (i0 + 1)..64 {
                let v1 = bases[a1][i1];
                let v = v0.wrapping_add(v1);
                let v = v as u64;
                if fast_arithmetic_weight(v) == 1 {
                    misconstrued += 1;
                    println!("{v0:#b} + {v1:#b} = {v:#b}");
                }
                total += 1;
            }
        }
    }
    (total, misconstrued)
}

// Want to count the number of 2-bit errors which are misconstrued as correctable
// one bit errors
fn three_bit_misconstrued() -> (u64, u64, u64) {
    let mut total = 0;
    let mut misconstrued1 = 0;
    let mut misconstrued2 = 0;
    let bases = get_bases::<u64>();
    for alpha in 0..(1 << 3) {
        let a0 = (alpha >> 0) & 1;
        let a1 = (alpha >> 1) & 1;
        let a2 = (alpha >> 2) & 1;
        for i0 in 0..64 {
            let v0 = bases[a0][i0];
            for i1 in (i0 + 1)..64 {
                let v1 = bases[a1][i1];
                for i2 in (i1 + 1)..64 {
                    let v2 = bases[a2][i2];
                    let v = v0.wrapping_add(v1.wrapping_add(v2));
                    let v = v as u64;
                    if fast_arithmetic_weight(v) == 1 {
                        misconstrued1 += 1;
                        // println!("{v0:#b} + {v1:#b} = {v:#b}");
                    }
                    if fast_arithmetic_weight(v) == 2 {
                        misconstrued2 += 1;
                        // println!("{v0:#b} + {v1:#b} = {v:#b}");
                    }
                    total += 1;
                }
            }
        }
    }
    (total, misconstrued1, misconstrued2)
}

// Want to count the number of 2-bit errors which are misconstrued as correctable
// one bit errors
fn four_bit_misconstrued() -> (u64, u64) {
    let mut total = 0;
    let mut misconstrued = 0;
    let bases = get_bases::<u64>();
    for alpha in 0..(1 << 4) {
        let a0 = (alpha >> 0) & 1;
        let a1 = (alpha >> 1) & 1;
        let a2 = (alpha >> 2) & 1;
        let a3 = (alpha >> 3) & 1;
        for i0 in 0..64 {
            let v0 = bases[a0][i0];
            for i1 in (i0 + 1)..64 {
                let v1 = bases[a1][i1];
                let v = v0.wrapping_add(v1);
                for i2 in (i1 + 1)..64 {
                    let v2 = bases[a2][i2];
                    let v = v.wrapping_add(v2);
                    for i3 in (i2 + 1)..64 {
                        let v3 = bases[a3][i3];
                        let v = v.wrapping_add(v3);
                        let v = v as u64;
                        if fast_arithmetic_weight(v) == 1 {
                            misconstrued += 1;
                            // println!("{v0:#b} + {v1:#b} = {v:#b}");
                        }
                        total += 1;
                    }
                }
            }
        }
    }
    (total, misconstrued)
}

fn main() {
    let cli = Cli::parse();

    match &cli.command {
        Command::Analyze {
            a_limit,
            bits,
            threads,
            output,
        } => {
            if cli.verbose {
                println!("Starting AN code analysis...");
                println!("a_limit: {}", a_limit);
                println!("bits: {}", bits);
                println!("threads: {}", threads);
                println!("output: {}", output.display());
            }

            // Run the analysis
            let exp = Experiment::new(*a_limit, *bits, *threads);

            // Write results to the specified output file
            let f = File::create(output).expect("Unable to create output file");
            let mut f = BufWriter::new(f);
            for e in exp.results.iter() {
                f.write_all(format!("{}", e.to_csv_line()).as_bytes())
                    .expect("Unable to write");
            }

            if cli.verbose {
                println!("Analysis complete. Results written to {}", output.display());
            }
        }
        Command::AnalyzeSingle { a, bits } => {
            if cli.verbose {
                println!("Starting AN code analysis...");
                println!("a: {}", a);
                println!("bits: {}", bits);
            }
            let an = AnCode::new(*a, *bits);
            println!("{}", an.to_csv_line());
            println!("{:?}", an);
        }
        Command::Misconstruct { analysis_type } => match analysis_type {
            MisconstructionType::TwoBit => {
                if cli.verbose {
                    println!("Running two-bit error misconstruction analysis...");
                }
                let (total, misconstrued) = two_bit_misconstrued();
                println!("Two-bit errors analysis:");
                println!("Total combinations: {}", total);
                println!("Misconstrued as 1-bit errors: {}", misconstrued);
                println!(
                    "Percentage: {:.2}%",
                    (misconstrued as f64 / total as f64) * 100.0
                );
            }
            MisconstructionType::ThreeBit => {
                if cli.verbose {
                    println!("Running three-bit error misconstruction analysis...");
                }
                let (total, misconstrued1, misconstrued2) = three_bit_misconstrued();
                println!("Three-bit errors analysis:");
                println!("Total combinations: {}", total);
                println!("Misconstrued as 1-bit errors: {}", misconstrued1);
                println!("Misconstrued as 2-bit errors: {}", misconstrued2);
                println!(
                    "Percentage as 1-bit: {:.2}%",
                    (misconstrued1 as f64 / total as f64) * 100.0
                );
                println!(
                    "Percentage as 2-bit: {:.2}%",
                    (misconstrued2 as f64 / total as f64) * 100.0
                );
            }
            MisconstructionType::FourBit => {
                if cli.verbose {
                    println!("Running four-bit error misconstruction analysis...");
                }
                let (total, misconstrued) = four_bit_misconstrued();
                println!("Four-bit errors analysis:");
                println!("Total combinations: {}", total);
                println!("Misconstrued as 1-bit errors: {}", misconstrued);
                println!(
                    "Percentage: {:.2}%",
                    (misconstrued as f64 / total as f64) * 100.0
                );
            }
        }
        Command::GenerateAllErrors { bits, num_weights, threads, min_a, max_a, output } => {
            let bits       = *bits;
            let num_weights = *num_weights;
            let min_a      = *min_a;
            let max_a      = *max_a;
            let num_threads = *threads as usize;

            let upper = max_a;
            let start = if min_a % 2 == 0 { min_a + 1 } else { min_a };

            // Collect primes
            let primes: Vec<u64> = (start..=upper)
                .step_by(2)
                .filter(|&a| is_prime(a as u128))
                .collect();

            // Partition to threads evenly
            let chunk_size = (primes.len() + num_threads - 1) / num_threads;

            let f = File::create(output).expect("unable to create output file");
            let out = Arc::new(Mutex::new(BufWriter::new(f)));

            // Spawn one thread per chunk
            let handles: Vec<_> = primes
                .chunks(chunk_size)
                .map(|chunk| {
                    let chunk = chunk.to_vec();
                    let out = Arc::clone(&out);
                    thread::spawn(move || {
                        for a in chunk {
                            // 1) find minimal weight that has an undetectable error
                            let minimal = enumerate_errors(a, bits, 0);
                            if minimal.is_empty() { continue; }
                            let w0 = minimal[0].0;
                            // 2) find and enumerate errors up to cap weight
                            let cap = w0 + num_weights.saturating_sub(1);
                            let all_errs = enumerate_errors(a, bits, cap);
                            // 3) group
                            let mut groups: BTreeMap<usize, Vec<u128>> = BTreeMap::new();
                            for (w_rel, cw, _) in all_errs {
                                let w_abs = w_rel;
                                groups.entry(w_abs).or_default().push(cw);
                            }
                            // format one line
                            let mut line = format!("{}, ", a);
                            for (w, list) in groups {
                                let codes = list.iter()
                                    .map(|v| v.to_string())
                                    .collect::<Vec<_>>()
                                    .join(", ");
                                line.push_str(&format!("{}: {};", w, codes));
                                line.push(' ');
                            }
                            let mut guard = out.lock().unwrap();
                            writeln!(guard, "{}", line.trim_end()).unwrap();
                        }
                    })
                })
                .collect();

            // Wait for everyone
            for h in handles {
                h.join().unwrap();
            }
        },
    }
}