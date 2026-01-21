/-
Real PCFG extraction test - extracts from actual Lean file and verifies results.
Tests the full pipeline: parse file -> extract rules -> compute metrics.
-/
import Lean.PCFG

open Lean Lean.PCFG

-- Extract from simple_defs.lean (in same directory)
def testExtraction : IO (PCFGCounts × PCFG) := do
  -- Initialize environment with Init module for parsing
  initSearchPath (← getBuildDir)
  let env ← importModules #[{module := `Init}] {} 0
  let path : System.FilePath := "simple_defs.lean"
  let stx ← parseFile env path
  let counts := countProductions stx PCFGCounts.empty
  let pcfg := computeProbabilities counts
  return (counts, pcfg)

-- Run extraction and verify with assertions
#eval show IO Unit from do
  let (counts, pcfg) ← testExtraction

  -- Basic sanity checks: extraction must have found rules
  unless counts.numRules > 0 do
    throw <| IO.userError s!"Expected rules to be extracted, got {counts.numRules}"
  unless counts.numNonTerminals > 0 do
    throw <| IO.userError s!"Expected non-terminals to be extracted, got {counts.numNonTerminals}"

  -- Check PCFG was computed correctly
  unless pcfg.numRules > 0 do
    throw <| IO.userError s!"Expected PCFG to have rules, got {pcfg.numRules}"

  -- Check entropy is non-negative (mathematical invariant)
  let avgH := averageEntropy pcfg
  unless avgH >= 0 do
    throw <| IO.userError s!"Average entropy should be non-negative, got {avgH}"

  -- Check grammar entropy is non-negative
  let wH := grammarEntropy pcfg counts
  unless wH >= 0 do
    throw <| IO.userError s!"Weighted grammar entropy should be non-negative, got {wH}"

  -- Check NSUI is in valid range [0,1]
  let nsui := computeNSUI pcfg counts false
  unless nsui >= 0 && nsui <= 1.001 do
    throw <| IO.userError s!"NSUI should be in [0,1], got {nsui}"

  -- Check grammar complexity metrics
  let complexity := computeGrammarComplexity pcfg
  unless complexity.numNonTerminals > 0 do
    throw <| IO.userError s!"Expected non-terminals in complexity, got {complexity.numNonTerminals}"
  unless complexity.numRules > 0 do
    throw <| IO.userError s!"Expected rules in complexity, got {complexity.numRules}"

  -- Verify we extracted a reasonable number of rules from simple_defs.lean
  -- simple_defs.lean has ~15 definitions, so we expect at least 20 rules
  unless counts.numRules >= 20 do
    throw <| IO.userError s!"Expected at least 20 rules from simple_defs.lean, got {counts.numRules}"

  -- Print summary for verification
  IO.println "Real PCFG extraction test passed:"
  IO.println s!"  Extracted {counts.numRules} rules from {counts.numNonTerminals} non-terminals"
  IO.println s!"  Average entropy: {avgH} bits"
  IO.println s!"  NSUI: {nsui}"
