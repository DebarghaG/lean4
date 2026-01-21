/-
Copyright (c) 2024 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DebarghaG
-/
import Lean.PCFG.Basic
import Lean.PCFG.Probability

namespace Lean.PCFG

/-! # Advanced Uncertainty Metrics for PCFG

This module provides a comprehensive suite of uncertainty measurements including:
- Rényi entropy (α = 0, 2, ∞)
- KL divergence and Jensen-Shannon divergence
- Confidence intervals (Wilson score method)
- Grammar complexity metrics
- Spectral analysis (power iteration)
- Normalized Structural Uncertainty Index (NSUI)
-/

/-- Grammar complexity metrics -/
structure GrammarComplexity where
  numNonTerminals : Nat
  numRules : Nat
  numTerminals : Nat
  avgRulesPerNt : Float
  avgRhsLength : Float
  maxBranchingFactor : Nat
  hasLeftRecursion : Bool
  hasRightRecursion : Bool
  deriving Repr, Inhabited

/-- Distribution statistics -/
structure DistributionStats where
  min : Float
  max : Float
  mean : Float
  std : Float
  skewness : Float
  kurtosis : Float
  deriving Repr, Inhabited

/-- Confidence interval -/
structure ConfidenceInterval where
  lower : Float
  upper : Float
  center : Float
  width : Float
  deriving Repr, Inhabited

/-- Entropy metrics collection -/
structure EntropyMetrics where
  shannonEntropy : Float
  renyiEntropy0 : Float      -- Max entropy (Hartley)
  renyiEntropy2 : Float      -- Collision entropy
  renyiEntropyInf : Float    -- Min entropy
  klDivergenceFromUniform : Float
  weightedGrammarEntropy : Float
  deriving Repr, Inhabited

/-- Spectral metrics -/
structure SpectralMetrics where
  spectralRadius : Float
  ntFrequencies : Std.HashMap NonTerminal Float
  deriving Inhabited

/-- Rule with confidence interval -/
structure RuleWithConfidence where
  rule : WeightedRule
  confidence : ConfidenceInterval
  deriving Repr, Inhabited

/-- Complete uncertainty metrics -/
structure UncertaintyMetrics where
  complexity : GrammarComplexity
  entropy : EntropyMetrics
  distribution : DistributionStats
  spectral : Option SpectralMetrics
  nsui : Float
  deriving Inhabited

/-! ## Statistical Primitives -/

/-- Compute the mean of an array of floats -/
def arrayMean (arr : Array Float) : Float :=
  if arr.isEmpty then 0
  else arr.foldl (· + ·) 0 / arr.size.toFloat

/-- Compute the variance of an array of floats -/
def arrayVariance (arr : Array Float) : Float :=
  if arr.size <= 1 then 0
  else
    let m := arrayMean arr
    let sumSqDiff := arr.foldl (init := 0) fun acc x =>
      acc + (x - m) * (x - m)
    sumSqDiff / (arr.size - 1).toFloat

/-- Compute the standard deviation of an array of floats -/
def arrayStd (arr : Array Float) : Float :=
  Float.sqrt (arrayVariance arr)

/-- Compute the skewness of a distribution.
    Skewness measures asymmetry: positive = right-tailed, negative = left-tailed -/
def arraySkewness (arr : Array Float) : Float :=
  if arr.size <= 2 then 0
  else
    let m := arrayMean arr
    let s := arrayStd arr
    if s <= 0 then 0
    else
      let n := arr.size.toFloat
      let sumCubed := arr.foldl (init := 0) fun acc x =>
        let z := (x - m) / s
        acc + z * z * z
      -- Sample skewness with bias correction
      let factor := n / ((n - 1) * (n - 2))
      factor * sumCubed

/-- Compute the kurtosis of a distribution.
    Kurtosis measures "tailedness": higher = heavier tails -/
def arrayKurtosis (arr : Array Float) : Float :=
  if arr.size <= 3 then 0
  else
    let m := arrayMean arr
    let s := arrayStd arr
    if s <= 0 then 0
    else
      let n := arr.size.toFloat
      let sumFourth := arr.foldl (init := 0) fun acc x =>
        let z := (x - m) / s
        acc + z * z * z * z
      -- Excess kurtosis (subtracting 3 to make normal distribution = 0)
      let k := sumFourth / n
      k - 3.0

/-- Compute comprehensive distribution statistics -/
def computeDistributionStats (probs : Array Float) : DistributionStats :=
  if probs.isEmpty then
    { min := 0, max := 0, mean := 0, std := 0, skewness := 0, kurtosis := 0 }
  else
    { min := probs.foldl (fun a b => if a < b then a else b) probs[0]!
      max := probs.foldl (fun a b => if a > b then a else b) probs[0]!
      mean := arrayMean probs
      std := arrayStd probs
      skewness := arraySkewness probs
      kurtosis := arrayKurtosis probs }

/-! ## Entropy Extensions -/

/-- Compute Rényi entropy of order α.
    - α = 0: Hartley entropy (log of support size)
    - α → 1: Shannon entropy (limit)
    - α = 2: Collision entropy
    - α = ∞: Min-entropy

    Formula: H_α(X) = (1/(1-α)) * log₂(Σᵢ pᵢ^α) for α ≠ 1
-/
def renyiEntropy (probs : Array Float) (alpha : Float) : Float :=
  if probs.isEmpty then 0
  else if alpha == 0 then
    -- Hartley entropy: log2 of the support size (number of non-zero probabilities)
    let support := probs.filter (· > 0) |>.size
    log2 support.toFloat
  else if alpha == 1 then
    -- Shannon entropy (limit as α → 1)
    entropyOfDistribution probs
  else if alpha >= 100 then
    -- Min-entropy (α → ∞): -log2(max(p))
    let maxP := probs.foldl (fun a b => if a > b then a else b) 0
    if maxP <= 0 then 0 else -log2 maxP
  else
    -- General case: H_α = (1/(1-α)) * log2(Σ p^α)
    let sumPowAlpha := probs.foldl (init := 0) fun acc p =>
      if p <= 0 then acc else acc + Float.pow p alpha
    if sumPowAlpha <= 0 then 0
    else (1 / (1 - alpha)) * log2 sumPowAlpha

/-- Compute KL divergence D(P||Q) = Σ p * log2(p/q)
    Returns infinity if any q_i = 0 where p_i > 0 -/
def klDivergence (p q : Array Float) : Float :=
  if p.size != q.size || p.isEmpty then 0
  else Id.run do
    let mut sum : Float := 0
    for i in [:p.size] do
      let pi := p[i]!
      let qi := q[i]!
      if pi > 0 then
        if qi <= 0 then
          return 1.0 / 0.0  -- Positive infinity
        else
          sum := sum + pi * log2 (pi / qi)
    return sum

/-- Compute KL divergence from the uniform distribution.
    D(P||U) = log2(n) - H(P) where n is the support size -/
def klDivergenceFromUniform (probs : Array Float) : Float :=
  if probs.isEmpty then 0
  else
    let n := probs.size.toFloat
    let maxEntropy := log2 n
    let entropy := entropyOfDistribution probs
    maxEntropy - entropy

/-- Compute Jensen-Shannon divergence.
    JSD(P||Q) = (D(P||M) + D(Q||M)) / 2 where M = (P+Q)/2
    JSD is symmetric and always finite (0 to 1 when using log2) -/
def jensenShannonDivergence (p q : Array Float) : Float :=
  if p.size != q.size || p.isEmpty then 0
  else
    -- Compute M = (P+Q)/2
    let m := (p.zip q).map fun (pi, qi) => (pi + qi) / 2
    -- JSD = (D(P||M) + D(Q||M)) / 2
    let dPM := klDivergence p m
    let dQM := klDivergence q m
    (dPM + dQM) / 2

/-! ## Confidence Intervals -/

/-- Compute Wilson score confidence interval for a proportion.
    This method is more accurate than normal approximation for small samples.

    Parameters:
    - successes: number of successes
    - n: total number of trials
    - z: z-score for confidence level (1.96 for 95%, 2.576 for 99%)
-/
def wilsonScoreInterval (successes n : Nat) (z : Float := 1.96) : ConfidenceInterval :=
  if n == 0 then
    { lower := 0, upper := 1, center := 0.5, width := 1 }
  else
    let nf := n.toFloat
    let phat := successes.toFloat / nf
    let z2 := z * z

    -- Wilson score formula
    let denominator := 1 + z2 / nf
    let center := (phat + z2 / (2 * nf)) / denominator
    let margin := z * Float.sqrt ((phat * (1 - phat) + z2 / (4 * nf)) / nf) / denominator

    let lower := if center - margin > 0 then center - margin else 0
    let upper := if center + margin < 1 then center + margin else 1

    { lower, upper, center, width := upper - lower }

/-- Z-score for common confidence levels -/
def zScoreForConfidence (confidence : Float) : Float :=
  if confidence >= 0.99 then 2.576
  else if confidence >= 0.95 then 1.96
  else if confidence >= 0.90 then 1.645
  else 1.0

/-- Compute rules with confidence intervals for a non-terminal -/
def rulesWithConfidence (pcfg : PCFG) (counts : PCFGCounts) (nt : NonTerminal)
    (z : Float := 1.96) : Array RuleWithConfidence := Id.run do
  let rules := pcfg.getRulesFor nt
  let totalCount := counts.lhsCounts.getD nt 0
  let mut result : Array RuleWithConfidence := #[]

  for wr in rules do
    let ci := wilsonScoreInterval wr.rule.count totalCount z
    result := result.push { rule := wr, confidence := ci }

  result

/-! ## Grammar Complexity -/

/-- Check if a non-terminal has direct left recursion.
    A -> A ... is left-recursive -/
def hasDirectLeftRecursion (pcfg : PCFG) (nt : NonTerminal) : Bool :=
  let rules := pcfg.getRulesFor nt
  rules.any fun wr =>
    wr.rule.rhs.size > 0 &&
    match wr.rule.rhs[0]! with
    | .nonTerminal rhsNt => rhsNt == nt
    | _ => false

/-- Check if a non-terminal has direct right recursion.
    A -> ... A is right-recursive -/
def hasDirectRightRecursion (pcfg : PCFG) (nt : NonTerminal) : Bool :=
  let rules := pcfg.getRulesFor nt
  rules.any fun wr =>
    wr.rule.rhs.size > 0 &&
    match wr.rule.rhs.back! with
    | .nonTerminal rhsNt => rhsNt == nt
    | _ => false

/-- Check if the grammar has any left recursion -/
def hasAnyLeftRecursion (pcfg : PCFG) : Bool :=
  pcfg.nonTerminals.toArray.any (hasDirectLeftRecursion pcfg)

/-- Check if the grammar has any right recursion -/
def hasAnyRightRecursion (pcfg : PCFG) : Bool :=
  pcfg.nonTerminals.toArray.any (hasDirectRightRecursion pcfg)

/-- Compute grammar complexity metrics -/
def computeGrammarComplexity (pcfg : PCFG) : GrammarComplexity := Id.run do
  let numNT := pcfg.nonTerminals.size
  let numRules := pcfg.numRules
  let numTerminals := pcfg.terminals.size

  -- Average rules per non-terminal
  let avgRulesPerNt := if numNT == 0 then 0 else numRules.toFloat / numNT.toFloat

  -- Average RHS length and max branching factor
  let mut totalRhsLength : Nat := 0
  let mut maxBranching : Nat := 0
  for (_, rules) in pcfg.rules do
    maxBranching := Nat.max maxBranching rules.size
    for wr in rules do
      totalRhsLength := totalRhsLength + wr.rule.rhs.size

  let avgRhsLength := if numRules == 0 then 0 else totalRhsLength.toFloat / numRules.toFloat

  { numNonTerminals := numNT
    numRules
    numTerminals
    avgRulesPerNt
    avgRhsLength
    maxBranchingFactor := maxBranching
    hasLeftRecursion := hasAnyLeftRecursion pcfg
    hasRightRecursion := hasAnyRightRecursion pcfg }

/-! ## Spectral Analysis

We use power iteration to estimate the spectral radius of the grammar's
production matrix without external dependencies.
-/

/-- Simple matrix type as array of arrays -/
abbrev Matrix := Array (Array Float)

/-- Build the production matrix (Jacobian) for the grammar.
    Entry (i,j) = sum of probabilities of rules where NT_i produces NT_j in RHS.
    Returns the matrix and the NT ordering. -/
def buildProductionMatrix (pcfg : PCFG) : Matrix × Array NonTerminal := Id.run do
  let nts := pcfg.nonTerminals.toArray
  let n := nts.size

  -- Build NT to index mapping
  let mut ntToIdx : Std.HashMap NonTerminal Nat := {}
  for i in [:n] do
    ntToIdx := ntToIdx.insert nts[i]! i

  -- Initialize n×n matrix with zeros
  let mut matrix : Matrix := .replicate n (.replicate n 0.0)

  -- Fill the matrix
  for i in [:n] do
    let nt := nts[i]!
    let rules := pcfg.getRulesFor nt
    for wr in rules do
      -- Count how many times each NT appears in RHS, weighted by probability
      for sym in wr.rule.rhs do
        match sym with
        | .nonTerminal rhsNt =>
          if let some j := ntToIdx.get? rhsNt then
            let row := matrix[i]!
            let newVal := row[j]! + wr.probability
            matrix := matrix.set! i (row.set! j newVal)
        | _ => pure ()

  (matrix, nts)

/-- Multiply matrix by vector -/
def matVecMul (m : Matrix) (v : Array Float) : Array Float :=
  m.map fun row =>
    (row.zip v).foldl (fun acc (a, b) => acc + a * b) 0

/-- Compute L2 norm of a vector -/
def vecNorm (v : Array Float) : Float :=
  Float.sqrt (v.foldl (fun acc x => acc + x * x) 0)

/-- Normalize a vector to unit length -/
def vecNormalize (v : Array Float) : Array Float :=
  let n := vecNorm v
  if n <= 0 then v else v.map (· / n)

/-- Power iteration to estimate the largest eigenvalue (spectral radius).
    Returns the estimated spectral radius. -/
def powerIteration (m : Matrix) (maxIter : Nat := 100) (tol : Float := 1e-6) : Float := Id.run do
  let n := m.size
  if n == 0 then return 0

  -- Start with a random-ish vector (all ones)
  let mut v : Array Float := .replicate n (1.0 / Float.sqrt n.toFloat)
  let mut eigenvalue : Float := 0

  for _ in [:maxIter] do
    -- Compute Mv
    let mv := matVecMul m v
    let mvNorm := vecNorm mv

    if mvNorm <= tol then
      -- Matrix is essentially zero
      return 0

    -- Update eigenvalue estimate (Rayleigh quotient approximation)
    let newEigenvalue := mvNorm / vecNorm v

    -- Check convergence
    if (newEigenvalue - eigenvalue).abs < tol then
      return newEigenvalue

    eigenvalue := newEigenvalue
    v := vecNormalize mv

  eigenvalue

/-- Compute the spectral radius of the grammar's production matrix -/
def spectralRadius (pcfg : PCFG) : Float :=
  let (matrix, _) := buildProductionMatrix pcfg
  powerIteration matrix

/-- Estimate non-terminal frequencies using the dominant eigenvector.
    This gives the stationary distribution of NT usage during derivation. -/
def estimateNtFrequencies (pcfg : PCFG) : Std.HashMap NonTerminal Float := Id.run do
  let (matrix, nts) := buildProductionMatrix pcfg
  let n := matrix.size

  if n == 0 then return {}

  -- Power iteration to find dominant eigenvector
  let mut v : Array Float := .replicate n (1.0 / Float.sqrt n.toFloat)

  for _ in [:100] do
    let mv := matVecMul matrix v
    let mvNorm := vecNorm mv
    if mvNorm <= 1e-10 then break
    v := vecNormalize mv

  -- Normalize to sum to 1 (probability distribution)
  let total := v.foldl (· + ·) 0
  let freqs := if total <= 0 then v else v.map (· / total)

  -- Build result map
  let mut result : Std.HashMap NonTerminal Float := {}
  for i in [:n] do
    result := result.insert nts[i]! freqs[i]!

  result

/-- Compute full spectral metrics -/
def computeSpectralMetrics (pcfg : PCFG) : SpectralMetrics :=
  { spectralRadius := spectralRadius pcfg
    ntFrequencies := estimateNtFrequencies pcfg }

/-! ## NSUI (Normalized Structural Uncertainty Index) -/

/-- Compute the maximum possible entropy for a grammar.
    This is the entropy if all rules had uniform probability. -/
def maxGrammarEntropy (pcfg : PCFG) (counts : PCFGCounts) : Float := Id.run do
  let mut totalOccurrences : Nat := 0
  for (_, count) in counts.lhsCounts do
    totalOccurrences := totalOccurrences + count

  if totalOccurrences == 0 then return 0

  let mut weightedMaxEntropy : Float := 0
  for (nt, ntCount) in counts.lhsCounts do
    let weight := ntCount.toFloat / totalOccurrences.toFloat
    let numRules := (pcfg.rules.getD nt #[]).size
    let maxH := if numRules > 0 then log2 numRules.toFloat else 0
    weightedMaxEntropy := weightedMaxEntropy + weight * maxH

  weightedMaxEntropy

/-- Compute the Normalized Structural Uncertainty Index (NSUI).
    NSUI = entropy_ratio * spectral_factor
    where:
    - entropy_ratio = weighted_grammar_entropy / max_entropy
    - spectral_factor = spectral_radius / (1 + spectral_radius)

    NSUI ∈ [0, 1] measures overall grammar uncertainty.
-/
def computeNSUI (pcfg : PCFG) (counts : PCFGCounts) (includeSpectral : Bool := true) : Float := Id.run do
  let wEntropy := grammarEntropy pcfg counts
  let maxEntropy := maxGrammarEntropy pcfg counts

  -- Entropy ratio (0 to 1)
  let entropyRatio := if maxEntropy <= 0 then 0 else wEntropy / maxEntropy

  if !includeSpectral then
    return entropyRatio

  -- Spectral factor (0 to 1)
  let sr := spectralRadius pcfg
  let spectralFactor := sr / (1 + sr)

  -- Combined NSUI
  entropyRatio * spectralFactor

/-! ## Entropy Metrics Collection -/

/-- Collect all probability values from the grammar -/
def collectAllProbabilities (pcfg : PCFG) : Array Float := Id.run do
  let mut probs : Array Float := #[]
  for (_, rules) in pcfg.rules do
    for wr in rules do
      probs := probs.push wr.probability
  probs

/-- Compute comprehensive entropy metrics -/
def computeEntropyMetricsStruct (pcfg : PCFG) (counts : PCFGCounts) : EntropyMetrics :=
  let probs := collectAllProbabilities pcfg
  { shannonEntropy := entropyOfDistribution probs
    renyiEntropy0 := renyiEntropy probs 0
    renyiEntropy2 := renyiEntropy probs 2
    renyiEntropyInf := renyiEntropy probs 100
    klDivergenceFromUniform := klDivergenceFromUniform probs
    weightedGrammarEntropy := grammarEntropy pcfg counts }

/-! ## Distribution Stats for All Rule Probabilities -/

/-- Compute distribution statistics for all rule probabilities -/
def computeProbabilityDistributionStats (pcfg : PCFG) : DistributionStats :=
  computeDistributionStats (collectAllProbabilities pcfg)

/-! ## Main Entry Point -/

/-- Compute all uncertainty metrics for a PCFG.
    Set includeSpectral to false for faster computation on large grammars. -/
def computeUncertaintyMetrics (pcfg : PCFG) (counts : PCFGCounts)
    (includeSpectral : Bool := true) : UncertaintyMetrics :=
  { complexity := computeGrammarComplexity pcfg
    entropy := computeEntropyMetricsStruct pcfg counts
    distribution := computeProbabilityDistributionStats pcfg
    spectral := if includeSpectral then some (computeSpectralMetrics pcfg) else none
    nsui := computeNSUI pcfg counts includeSpectral }

/-! ## Pretty Printing -/

/-- Round a float to a specified number of decimal places -/
def roundTo (x : Float) (decimals : Nat := 4) : Float :=
  let factor := Float.pow 10 decimals.toFloat
  Float.round (x * factor) / factor

/-- Print grammar complexity metrics -/
def printGrammarComplexity (c : GrammarComplexity) : IO Unit := do
  IO.println "\n=== Grammar Complexity ==="
  IO.println s!"  Non-terminals:       {c.numNonTerminals}"
  IO.println s!"  Production rules:    {c.numRules}"
  IO.println s!"  Terminals:           {c.numTerminals}"
  IO.println s!"  Avg rules per NT:    {roundTo c.avgRulesPerNt}"
  IO.println s!"  Avg RHS length:      {roundTo c.avgRhsLength}"
  IO.println s!"  Max branching:       {c.maxBranchingFactor}"
  IO.println s!"  Has left recursion:  {c.hasLeftRecursion}"
  IO.println s!"  Has right recursion: {c.hasRightRecursion}"

/-- Print distribution statistics -/
def printDistributionStats (d : DistributionStats) : IO Unit := do
  IO.println "\n=== Probability Distribution Stats ==="
  IO.println s!"  Min:      {roundTo d.min}"
  IO.println s!"  Max:      {roundTo d.max}"
  IO.println s!"  Mean:     {roundTo d.mean}"
  IO.println s!"  Std:      {roundTo d.std}"
  IO.println s!"  Skewness: {roundTo d.skewness}"
  IO.println s!"  Kurtosis: {roundTo d.kurtosis}"

/-- Print entropy metrics -/
def printEntropyMetricsStruct (e : EntropyMetrics) : IO Unit := do
  IO.println "\n=== Entropy Metrics ==="
  IO.println s!"  Shannon entropy:           {roundTo e.shannonEntropy} bits"
  IO.println s!"  Rényi entropy (α=0):       {roundTo e.renyiEntropy0} bits"
  IO.println s!"  Rényi entropy (α=2):       {roundTo e.renyiEntropy2} bits"
  IO.println s!"  Rényi entropy (α=∞):       {roundTo e.renyiEntropyInf} bits"
  IO.println s!"  KL div from uniform:       {roundTo e.klDivergenceFromUniform} bits"
  IO.println s!"  Weighted grammar entropy:  {roundTo e.weightedGrammarEntropy} bits"

/-- Print spectral metrics -/
def printSpectralMetrics (s : SpectralMetrics) : IO Unit := do
  IO.println "\n=== Spectral Metrics ==="
  IO.println s!"  Spectral radius: {roundTo s.spectralRadius}"
  IO.println s!"  NT frequencies computed for {s.ntFrequencies.size} non-terminals"

/-- Print full uncertainty metrics -/
def printUncertaintyMetrics (m : UncertaintyMetrics) : IO Unit := do
  printGrammarComplexity m.complexity
  printEntropyMetricsStruct m.entropy
  printDistributionStats m.distribution
  if let some spectral := m.spectral then
    printSpectralMetrics spectral
  IO.println "\n=== NSUI ==="
  IO.println s!"  Normalized Structural Uncertainty Index: {roundTo m.nsui}"

/-- Print rules with confidence intervals -/
def printRulesWithConfidence (pcfg : PCFG) (counts : PCFGCounts) (nt : NonTerminal)
    (confidence : Float := 0.95) : IO Unit := do
  let z := zScoreForConfidence confidence
  let rules := rulesWithConfidence pcfg counts nt z
  let sorted := rules.qsort (fun a b => a.rule.probability > b.rule.probability)

  IO.println s!"\n=== Rules for {nt} (with {confidence * 100}% CI) ==="
  for rwc in sorted do
    let rhsStr := rwc.rule.rule.rhs.toList.map Symbol.toString |> String.intercalate " "
    let probStr := toString (roundTo rwc.rule.probability)
    let ciStr := s!"[{roundTo rwc.confidence.lower}, {roundTo rwc.confidence.upper}]"
    IO.println s!"  → {rhsStr}  (p={probStr}, CI={ciStr}, n={rwc.rule.rule.count})"

end Lean.PCFG
