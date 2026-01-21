# PCFG Extraction and Uncertainty Metrics for Lean 4

This document describes how to build and use the Probabilistic Context-Free Grammar (PCFG) extraction tools for analyzing Lean 4 source code.

## Overview

The PCFG module extracts grammar rules from Lean syntax trees and computes various uncertainty metrics including:

- **Shannon entropy** - measures uncertainty in grammar choices
- **Rényi entropy** (α = 0, 2, ∞) - generalized entropy measures
- **KL divergence** - distance from uniform distribution
- **Jensen-Shannon divergence** - symmetric divergence measure
- **Confidence intervals** - Wilson score intervals for rule probabilities
- **Spectral analysis** - grammar production matrix eigenvalues
- **NSUI** - Normalized Structural Uncertainty Index

## Building

### Prerequisites

- CMake 3.16+
- C++ compiler with C++17 support
- Python 3 (for build scripts)
- **ccache** (highly recommended - speeds up rebuilds significantly)

### Build Commands

```bash
# Full build (first time only - takes 30-60+ minutes)
make -j -C build/release

# Build only stage1 (faster for development - 10-20 minutes)
make -j -C build/release stage1
```

### Build Time Considerations

> **Important:** The Lean 4 build is slow. Plan accordingly.

| Build Type | Approximate Time | When to Use |
|------------|-----------------|-------------|
| Full build | 30-60+ minutes | First time, or after major changes |
| Stage1 only | 10-20 minutes | After modifying src/Lean/ files |
| Incremental | 1-5 minutes | Small changes (with ccache) |

**Tips to minimize build time:**

1. **Install ccache** - Without it, every C file recompiles from scratch
   ```bash
   # macOS
   brew install ccache

   # Ubuntu
   sudo apt-get install ccache
   ```

2. **Only build stage1** - Stage2 is rarely needed for development
   ```bash
   make -j -C build/release stage1
   ```

3. **Use parallel jobs** - The `-j` flag uses all CPU cores

4. **Avoid full rebuilds** - See "What NOT to Do" below

### What NOT to Do

> **NEVER manually delete build directories** (`build/`, `stage0/`, `stage1/`).
> This forces a complete rebuild from scratch which takes 30+ minutes.

```bash
# DON'T DO THIS
rm -rf build/release/stage1  # WRONG - triggers full rebuild

# Instead, just run make again
make -j -C build/release stage1  # RIGHT - incremental build
```

If you accidentally break the build:
1. First try `make -j -C build/release stage1` again
2. If that fails, ask before deleting anything

### Linking with elan (optional)

For easier command-line access:

```bash
# Link stage1 as the lean4 toolchain
elan toolchain link lean4 build/release/stage1
elan toolchain link lean4-stage0 build/release/stage0
```

## Module Structure

```
src/Lean/PCFG/
├── Basic.lean       # Core types: Terminal, Symbol, ProductionRule, PCFG
├── Extract.lean     # Syntax tree traversal and rule extraction
├── Probability.lean # MLE probability estimation, Shannon entropy
├── Metrics.lean     # Advanced metrics (Rényi, KL, spectral, NSUI)
└── Main.lean        # CLI tool entry point
```

## Running the PCFG Tool

### Command-Line Interface

```bash
# Basic usage
lean --run src/Lean/PCFG/Main.lean <input-path> [options]

# Or if you have the built binary:
./build/release/stage1/bin/lean --run src/Lean/PCFG/Main.lean <input-path> [options]
```

### Options

| Option | Description |
|--------|-------------|
| `-v, --verbose` | Print verbose output during processing |
| `--top N` | Print top N rules per non-terminal |
| `--inspect NAME` | Print all rules for a specific non-terminal |
| `--entropy` | Print entropy statistics |
| `--smooth ALPHA` | Use Laplace smoothing with given alpha |
| `--metrics` | Compute and display all uncertainty metrics |
| `--spectral` | Include spectral analysis (can be slow) |
| `--confidence` | Show confidence intervals for rules |
| `--confidence-level FLOAT` | Confidence level (default: 0.95) |
| `-h, --help` | Print help message |

### Examples

```bash
# Extract PCFG from a single file
lean --run src/Lean/PCFG/Main.lean myfile.lean --entropy

# Extract from a directory of Lean files
lean --run src/Lean/PCFG/Main.lean src/Lean/ --verbose --top 5

# Full metrics with spectral analysis
lean --run src/Lean/PCFG/Main.lean src/Lean/ --metrics --spectral

# Inspect a specific non-terminal with confidence intervals
lean --run src/Lean/PCFG/Main.lean src/Lean/ --inspect Lean.Parser.Term.app --confidence
```

## Using PCFG Programmatically

### Basic Extraction

```lean
import Lean.PCFG

open Lean Lean.PCFG

-- Parse a file and extract PCFG
def extractFromFile (env : Environment) (path : System.FilePath) : IO PCFG := do
  let content ← IO.FS.readFile path
  let inputCtx := Parser.mkInputContext content path.toString
  let (stx, _, _) ← Parser.parseModule env inputCtx {}
  let counts := countProductions stx PCFGCounts.empty
  return computeProbabilities counts

-- With Laplace smoothing
def extractSmoothed (env : Environment) (path : System.FilePath) (alpha : Float) : IO PCFG := do
  let content ← IO.FS.readFile path
  let inputCtx := Parser.mkInputContext content path.toString
  let (stx, _, _) ← Parser.parseModule env inputCtx {}
  let counts := countProductions stx PCFGCounts.empty
  return computeProbabilitiesSmoothed counts alpha
```

### Computing Metrics

```lean
import Lean.PCFG

open Lean.PCFG

def analyzeGrammar (pcfg : PCFG) (counts : PCFGCounts) : IO Unit := do
  -- Basic entropy
  let avgH := averageEntropy pcfg
  let weightedH := grammarEntropy pcfg counts
  IO.println s!"Average entropy: {avgH} bits"
  IO.println s!"Weighted grammar entropy: {weightedH} bits"

  -- Full uncertainty metrics
  let metrics := computeUncertaintyMetrics pcfg counts (includeSpectral := true)
  printUncertaintyMetrics metrics

  -- Entropy for specific non-terminal
  let termH := entropyFor pcfg `Lean.Parser.Term.app
  IO.println s!"Term.app entropy: {termH} bits"
```

### Batch Processing Multiple Files

```lean
import Lean.PCFG

open Lean Lean.PCFG

def processDirectory (env : Environment) (dir : System.FilePath) : IO (PCFG × PCFGCounts) := do
  let mut counts := PCFGCounts.empty

  -- Find all .lean files
  for entry in ← dir.readDir do
    if entry.path.extension == some "lean" then
      IO.println s!"Processing: {entry.path}"
      let content ← IO.FS.readFile entry.path
      let inputCtx := Parser.mkInputContext content entry.path.toString
      match ← Parser.parseModule env inputCtx {} with
      | (stx, _, _) => counts := countProductions stx counts

  let pcfg := computeProbabilities counts
  return (pcfg, counts)
```

## Understanding the Output

### Grammar Summary

```
=== PCFG Summary ===
Non-terminals: 847
Terminals: 156
Production rules: 2341
Start symbols: [Lean.Parser.Module.module, ...]
```

### Entropy Statistics

```
=== Entropy Statistics ===
Average per-NT entropy:     1.234 bits
Weighted grammar entropy:   0.876 bits

--- Top 10 highest entropy (most diverse) ---
  Lean.Parser.Term.app: H=3.45 bits, 128 rules, 5420 occurrences

--- Top 10 lowest entropy (most predictable, >1 rule) ---
  Lean.Parser.Command.namespace: H=0.12 bits, 2 rules, 890 occurrences

Deterministic (single rule): 234 non-terminals
```

### Full Uncertainty Metrics

```
=== Grammar Complexity ===
  Non-terminals:       847
  Production rules:    2341
  Terminals:           156
  Avg rules per NT:    2.76
  Avg RHS length:      3.2
  Max branching:       128
  Has left recursion:  true
  Has right recursion: true

=== Entropy Metrics ===
  Shannon entropy:           1.234 bits
  Rényi entropy (α=0):       3.456 bits
  Rényi entropy (α=2):       0.987 bits
  Rényi entropy (α=∞):       0.543 bits
  KL div from uniform:       2.345 bits
  Weighted grammar entropy:  0.876 bits

=== Probability Distribution Stats ===
  Min:      0.0001
  Max:      0.8765
  Mean:     0.1234
  Std:      0.2345
  Skewness: 2.34
  Kurtosis: 5.67

=== Spectral Metrics ===
  Spectral radius: 1.234
  NT frequencies computed for 847 non-terminals

=== NSUI ===
  Normalized Structural Uncertainty Index: 0.456
```

## Running Tests

```bash
cd tests/lean/run

# Run individual tests
./test_single.sh pcfg_basic.lean
./test_single.sh pcfg_extract.lean
./test_single.sh pcfg_entropy.lean
./test_single.sh pcfg_metrics.lean
./test_single.sh pcfg_full_test.lean

# Run all PCFG tests
for f in pcfg_*.lean; do
  echo "Testing $f..."
  ./test_single.sh "$f"
done
```

## Interpretation Guide

### Entropy Values

| Entropy | Interpretation |
|---------|----------------|
| 0 bits | Deterministic (single rule) |
| 1 bit | Binary choice (50/50) |
| 2 bits | 4 equally likely choices |
| 3+ bits | High uncertainty/diversity |

### NSUI (Normalized Structural Uncertainty Index)

| NSUI | Interpretation |
|------|----------------|
| 0.0 | Completely deterministic grammar |
| 0.3-0.5 | Moderately structured |
| 0.7+ | Highly uncertain/flexible grammar |

### Spectral Radius

- **< 1**: Grammar contracts (derivations tend to terminate)
- **= 1**: Grammar is balanced
- **> 1**: Grammar expands (potential for infinite derivations)

## Development Workflow

### Recommended Workflow for Modifying PCFG Code

1. **Make your changes** to files in `src/Lean/PCFG/`

2. **Quick syntax check** using stage0 (no full rebuild needed):
   ```bash
   # Check if your file compiles (fast, ~1-2 seconds)
   ./build/release/stage0/bin/lean --root=. src/Lean/PCFG/YourFile.lean
   ```

3. **Build stage1** only if syntax check passes:
   ```bash
   make -j -C build/release stage1
   ```

4. **Run tests**:
   ```bash
   cd tests/lean/run
   ./test_single.sh pcfg_metrics.lean
   ```

### Quick Iteration Without Full Rebuild

For rapid development, you can check syntax without building:

```bash
# Fast syntax check (~1-2 seconds)
./build/release/stage0/bin/lean --root=. src/Lean/PCFG/Metrics.lean

# If errors, fix and repeat
# Only run make when syntax check passes
```

### Testing Changes

```bash
cd tests/lean/run

# Test a specific file
./test_single.sh pcfg_metrics.lean

# Test all PCFG-related tests
for f in pcfg_*.lean; do ./test_single.sh "$f" && echo "✓ $f"; done
```

## Troubleshooting

### Build Errors

If you encounter build errors after modifying PCFG files:

```bash
# Rebuild stage1 (don't delete build directories manually)
make -j -C build/release stage1
```

### Import Errors

Ensure the module is properly imported:

```lean
import Lean.PCFG           -- All PCFG modules
import Lean.PCFG.Metrics   -- Just metrics
import Lean.PCFG.Probability  -- Just probability/entropy
```

### Slow Spectral Analysis

For large grammars, spectral analysis can be slow. Use `--metrics` without `--spectral` for faster results:

```bash
lean --run src/Lean/PCFG/Main.lean large_codebase/ --metrics
```

Or programmatically:

```lean
let metrics := computeUncertaintyMetrics pcfg counts (includeSpectral := false)
```

### Common Errors and Fixes

#### "object file ... does not exist"

```
error: object file '.../Lean/PCFG/Metrics.olean' does not exist
```

**Cause:** Stage1 hasn't been built yet after adding new files.

**Fix:** Build stage1:
```bash
make -j -C build/release stage1
```

#### "unknown tactic 'ring'"

```
error: unknown tactic 'ring'
```

**Cause:** The `ring` tactic is from Mathlib, not core Lean.

**Fix:** Use `omega` for linear arithmetic or explicit rewrites:
```lean
-- Instead of: by ring
-- Use:
by omega  -- for linear arithmetic
-- or explicit steps
```

#### "unknown identifier 'mkArray'"

```
error: Unknown identifier `mkArray`
```

**Cause:** Lean core uses different naming conventions.

**Fix:** Use `.replicate` instead:
```lean
-- Instead of: Array.mkArray n 0.0
-- Use:
Array.replicate n 0.0
-- or
(.replicate n 0.0 : Array Float)
```

#### "Float.min/max not found"

```
error: Unknown constant `Float.min`
```

**Cause:** Float doesn't have `min`/`max` as methods.

**Fix:** Use inline conditionals:
```lean
-- Instead of: Float.min a b
-- Use:
if a < b then a else b
```

#### Build takes forever after small change

**Cause:** The build system may be rebuilding more than necessary.

**Fix:**
1. Make sure ccache is installed
2. Only modify files you need to change
3. Use stage0 for quick syntax checks before triggering builds

## Performance Considerations

### Memory Usage

- Large codebases can consume significant memory during PCFG extraction
- Spectral analysis creates an N×N matrix where N = number of non-terminals
- For grammars with 1000+ non-terminals, consider disabling spectral analysis

### Processing Time

| Codebase Size | Extraction Time | With Spectral |
|--------------|-----------------|---------------|
| Single file | < 1 second | < 1 second |
| 100 files | 5-10 seconds | 10-20 seconds |
| 1000+ files | 1-2 minutes | 5-10 minutes |

### Optimization Tips

1. **Process files in batches** rather than one at a time
2. **Disable spectral analysis** for initial exploration
3. **Use Laplace smoothing** (`--smooth 1.0`) to avoid zero probabilities
4. **Focus on specific non-terminals** with `--inspect`
