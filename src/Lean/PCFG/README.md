# PCFG Extraction for Lean

Extract Probabilistic Context-Free Grammars from Lean syntax trees and compute entropy metrics.

## Build

```bash
make -j -C build/release
```

## API Usage

```lean
import Lean.PCFG

open Lean.PCFG

-- Extract productions from syntax
def counts : PCFGCounts := countProductions stx PCFGCounts.empty

-- Compute probabilities (MLE)
def pcfg : PCFG := computeProbabilities counts

-- Or with Laplace smoothing (α=1.0)
def pcfgSmoothed : PCFG := computeProbabilitiesSmoothed counts 1.0

-- Entropy metrics
let h := entropyFor pcfg `term           -- Per-NT entropy (bits)
let avgH := averageEntropy pcfg          -- Mean entropy across all NTs
let weightedH := grammarEntropy pcfg counts  -- Frequency-weighted entropy
let ce := crossEntropy pcfg testCounts   -- Cross-entropy on test data
let pp := perplexity pcfg testCounts     -- 2^CE
```

## Key Types

```lean
Terminal     -- Abstracted terminals: keyword, symbol, ident, numLit, strLit, ...
Symbol       -- terminal | nonTerminal
PCFGCounts   -- HashMap-based rule counter
PCFG         -- Final grammar with weighted rules
```

## Entropy Functions

| Function | Description |
|----------|-------------|
| `entropyFor pcfg nt` | H(NT) = -Σ P(r\|NT) × log₂P(r\|NT) |
| `averageEntropy pcfg` | Unweighted mean of per-NT entropies |
| `grammarEntropy pcfg counts` | Frequency-weighted: Σ w(NT) × H(NT) |
| `crossEntropy pcfg testCounts` | -1/N × Σ log₂P(rule_i) on test data |
| `perplexity pcfg testCounts` | 2^crossEntropy |

## File Processing

```lean
-- Initialize environment
let env ← initEnvironment

-- Parse single file
let stx ← parseFile env "path/to/file.lean"
let counts := countProductions stx PCFGCounts.empty

-- Process directory recursively
let counts ← processDirectory env "src/" PCFGCounts.empty (verbose := true)
```

## Tests

```bash
./build/release/stage1/bin/lean tests/lean/run/pcfg_basic.lean
./build/release/stage1/bin/lean tests/lean/run/pcfg_extract.lean
./build/release/stage1/bin/lean tests/lean/run/pcfg_entropy.lean
./build/release/stage1/bin/lean tests/lean/run/pcfg_sanity.lean
```

## CLI (Main.lean)

```
Usage: pcfg-extract <input-path> [options]

Options:
  -v, --verbose    Print verbose output
  --top N          Print top N rules per non-terminal
  --inspect NAME   Print all rules for a specific non-terminal
  --entropy        Print entropy statistics
  --smooth ALPHA   Use Laplace smoothing (default: 0)
  -h, --help       Print help
```

## Module Structure

```
src/Lean/PCFG/
├── Basic.lean       -- Core types: Terminal, Symbol, PCFGCounts, PCFG
├── Extract.lean     -- Syntax tree traversal, production extraction
├── Probability.lean -- MLE, smoothing, entropy, reporting
└── Main.lean        -- CLI entry point
```
