/-
End-to-end integration test for PCFG extraction.
Tests the full pipeline: parse file -> extract rules -> compute metrics -> verify results.

This test exercises real code paths rather than simulating data structures.
-/
import Lean.PCFG

open Lean Lean.PCFG

-- Integration test: verify the full PCFG extraction pipeline works on real Lean code
#eval show IO Unit from do
  -- Initialize environment
  initSearchPath (← getBuildDir)
  let env ← importModules #[{module := `Init}] {} 0

  -- Parse and extract from simple_defs.lean
  let stx ← parseFile env "simple_defs.lean"
  let counts := countProductions stx PCFGCounts.empty
  let pcfg := computeProbabilities counts

  -- Verify extraction found real grammar structure
  if counts.numRules < 10 then
    throw <| IO.userError s!"Expected at least 10 rules, got {counts.numRules}"

  if counts.numNonTerminals < 5 then
    throw <| IO.userError s!"Expected at least 5 non-terminals, got {counts.numNonTerminals}"

  -- Verify we can iterate over the rules
  let mut totalRuleCount := 0
  for (_, rules) in pcfg.rules.toList do
    totalRuleCount := totalRuleCount + rules.size
  if totalRuleCount == 0 then
    throw <| IO.userError "Expected to iterate over non-empty rules"

  -- Test probability computations
  for (nt, rules) in pcfg.rules.toList do
    -- Check probabilities sum to approximately 1 for each non-terminal
    let probSum := rules.foldl (fun acc r => acc + r.probability) 0.0
    if (probSum - 1.0).abs > 0.01 then
      throw <| IO.userError s!"Probabilities for {nt} sum to {probSum}, expected 1.0"

    -- Check all probabilities are valid
    for r in rules do
      if r.probability < 0 || r.probability > 1 then
        throw <| IO.userError s!"Invalid probability {r.probability} for rule in {nt}"

  -- Test entropy calculations
  let avgH := averageEntropy pcfg
  if avgH < 0 then
    throw <| IO.userError s!"Average entropy should be non-negative, got {avgH}"

  -- Test per-NT entropy
  for (nt, _) in pcfg.rules.toList do
    let h := entropyFor pcfg nt
    if h < 0 then
      throw <| IO.userError s!"Entropy for {nt} should be non-negative, got {h}"

  -- Test full uncertainty metrics computation
  let metrics := computeUncertaintyMetrics pcfg counts false
  if metrics.nsui < 0 || metrics.nsui > 1.001 then
    throw <| IO.userError s!"NSUI out of bounds: {metrics.nsui}"

  if metrics.complexity.numRules != pcfg.numRules then
    throw <| IO.userError s!"Complexity rules mismatch: {metrics.complexity.numRules} vs {pcfg.numRules}"

  -- Test confidence intervals (Wilson score)
  for (nt, _) in pcfg.rules.toList.take 3 do
    let rulesWithCI := rulesWithConfidence pcfg counts nt
    for rwc in rulesWithCI do
      -- Lower <= center <= upper
      if rwc.confidence.lower > rwc.confidence.center then
        throw <| IO.userError s!"CI lower > center for rule in {nt}"
      if rwc.confidence.center > rwc.confidence.upper then
        throw <| IO.userError s!"CI center > upper for rule in {nt}"
      -- All in [0,1]
      if rwc.confidence.lower < 0 || rwc.confidence.upper > 1 then
        throw <| IO.userError s!"CI bounds out of [0,1] for rule in {nt}"

  -- Test distribution statistics
  let allProbs := collectAllProbabilities pcfg
  if allProbs.size == 0 then
    throw <| IO.userError "Expected non-empty probability distribution"

  let stats := computeDistributionStats allProbs
  if stats.min < 0 || stats.max > 1 then
    throw <| IO.userError s!"Distribution stats out of bounds: min={stats.min}, max={stats.max}"
  if stats.mean < stats.min || stats.mean > stats.max then
    throw <| IO.userError s!"Mean {stats.mean} outside [min, max]"

  -- Success output
  IO.println "Integration test passed:"
  IO.println s!"  Rules: {counts.numRules}"
  IO.println s!"  Non-terminals: {counts.numNonTerminals}"
  IO.println s!"  Average entropy: {avgH} bits"
  IO.println s!"  NSUI: {metrics.nsui}"
  IO.println s!"  Complexity: {metrics.complexity.numRules} rules, {metrics.complexity.numNonTerminals} NTs"
