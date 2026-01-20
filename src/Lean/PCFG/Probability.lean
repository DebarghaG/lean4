/-
Copyright (c) 2024 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DebarghaG
-/
import Lean.PCFG.Basic

namespace Lean.PCFG

/-- Compute log base 2 of a float -/
def log2 (x : Float) : Float :=
  if x <= 0 then 0 else Float.log x / Float.log 2

/-- Compute entropy of a probability distribution: H = -Σ p * log₂(p)
    Handles p=0 correctly (0 * log(0) = 0 by convention) -/
def entropyOfDistribution (probs : Array Float) : Float :=
  probs.foldl (init := 0) fun acc p =>
    if p <= 0 then acc else acc - p * log2 p

/--
Compute probabilities from raw counts using Maximum Likelihood Estimation.
For each non-terminal, P(rule | lhs) = count(rule) / count(lhs)
-/
def computeProbabilities (counts : PCFGCounts) : PCFG := Id.run do
  let mut rules : Std.HashMap NonTerminal (Array WeightedRule) := {}
  let mut nonTerminals : Std.HashSet NonTerminal := {}
  let mut terminals : Std.HashSet Terminal := {}

  for (lhs, rhsMap) in counts.rules do
    nonTerminals := nonTerminals.insert lhs
    let total := counts.lhsCounts.getD lhs 1  -- Avoid division by zero
    let mut weightedRules : Array WeightedRule := #[]

    for (rhs, count) in rhsMap do
      let prob := count.toFloat / total.toFloat
      let rule : ProductionRule := { lhs, rhs, count }
      weightedRules := weightedRules.push { rule, probability := prob }

      -- Collect all symbols appearing in RHS
      for sym in rhs do
        match sym with
        | .terminal t => terminals := terminals.insert t
        | .nonTerminal nt => nonTerminals := nonTerminals.insert nt

    rules := rules.insert lhs weightedRules

  -- Default start symbols for Lean
  let startSymbols := #[
    `Lean.Parser.Module.module,
    `Lean.Parser.Command.declaration,
    `term,
    `tactic
  ]

  { rules, nonTerminals, terminals, startSymbols }

/--
Compute probabilities with Laplace (additive) smoothing.
P(rule | lhs) = (count(rule) + α) / (count(lhs) + α * V)
where V is the number of distinct rules for that LHS.
-/
def computeProbabilitiesSmoothed (counts : PCFGCounts) (alpha : Float := 1.0) : PCFG := Id.run do
  let mut rules : Std.HashMap NonTerminal (Array WeightedRule) := {}
  let mut nonTerminals : Std.HashSet NonTerminal := {}
  let mut terminals : Std.HashSet Terminal := {}

  for (lhs, rhsMap) in counts.rules do
    nonTerminals := nonTerminals.insert lhs
    let total := counts.lhsCounts.getD lhs 1
    let vocabSize := rhsMap.size  -- Number of distinct RHS for this LHS
    let smoothedTotal := total.toFloat + alpha * vocabSize.toFloat
    let mut weightedRules : Array WeightedRule := #[]

    for (rhs, count) in rhsMap do
      let smoothedCount := count.toFloat + alpha
      let prob := smoothedCount / smoothedTotal
      let rule : ProductionRule := { lhs, rhs, count }
      weightedRules := weightedRules.push { rule, probability := prob }

      for sym in rhs do
        match sym with
        | .terminal t => terminals := terminals.insert t
        | .nonTerminal nt => nonTerminals := nonTerminals.insert nt

    rules := rules.insert lhs weightedRules

  let startSymbols := #[
    `Lean.Parser.Module.module,
    `Lean.Parser.Command.declaration,
    `term,
    `tactic
  ]

  { rules, nonTerminals, terminals, startSymbols }

/--
Compute the entropy for a specific non-terminal.
H(NT) = -Σ P(rule | NT) * log₂(P(rule | NT))
Returns 0 if NT not found.
-/
def entropyFor (pcfg : PCFG) (nt : NonTerminal) : Float :=
  match pcfg.rules.get? nt with
  | none => 0
  | some rules =>
    let probs := rules.map (·.probability)
    entropyOfDistribution probs

/--
Compute weighted grammar entropy.
H(G) = Σ weight(NT) * H(NT)
where weight(NT) = totalCount(NT) / Σ totalCount(all NTs)
-/
def grammarEntropy (pcfg : PCFG) (counts : PCFGCounts) : Float := Id.run do
  let mut totalOccurrences : Nat := 0
  for (_, count) in counts.lhsCounts do
    totalOccurrences := totalOccurrences + count

  if totalOccurrences == 0 then return 0

  let mut weightedEntropy : Float := 0
  for (nt, ntCount) in counts.lhsCounts do
    let weight := ntCount.toFloat / totalOccurrences.toFloat
    let h := entropyFor pcfg nt
    weightedEntropy := weightedEntropy + weight * h

  return weightedEntropy

/--
Compute average per-decision entropy (unweighted mean).
-/
def averageEntropy (pcfg : PCFG) : Float := Id.run do
  if pcfg.nonTerminals.isEmpty then return 0
  let mut totalEntropy : Float := 0
  let mut count : Nat := 0
  for nt in pcfg.nonTerminals do
    totalEntropy := totalEntropy + entropyFor pcfg nt
    count := count + 1
  return totalEntropy / count.toFloat

/--
Compute cross-entropy of test data against learned grammar.
CE = -1/N * Σ log₂(P(rule_i))
Returns infinity if any rule has zero probability.
-/
def crossEntropy (pcfg : PCFG) (testCounts : PCFGCounts) : Float := Id.run do
  let mut totalLogProb : Float := 0
  let mut n : Nat := 0

  for (lhs, rhsMap) in testCounts.rules do
    let rules := pcfg.rules.getD lhs #[]
    for (rhs, count) in rhsMap do
      -- Find probability of this rule in the PCFG
      let prob := rules.foldl (init := 0) fun acc wr =>
        if wr.rule.rhs == rhs then wr.probability else acc
      if prob <= 0 then
        return 1.0 / 0.0  -- Positive infinity for unseen rules without smoothing
      totalLogProb := totalLogProb + count.toFloat * log2 prob
      n := n + count

  if n == 0 then return 0
  return -totalLogProb / n.toFloat

/--
Compute perplexity = 2^crossEntropy
-/
def perplexity (pcfg : PCFG) (testCounts : PCFGCounts) : Float :=
  let ce := crossEntropy pcfg testCounts
  Float.pow 2 ce

/--
Print a summary of the PCFG to stdout.
-/
def printSummary (pcfg : PCFG) : IO Unit := do
  IO.println s!"=== PCFG Summary ==="
  IO.println s!"Non-terminals: {pcfg.nonTerminals.size}"
  IO.println s!"Terminals: {pcfg.terminals.size}"
  IO.println s!"Production rules: {pcfg.numRules}"
  IO.println s!"Start symbols: {pcfg.startSymbols.toList}"

/--
Print the top N rules for each non-terminal (by probability).
Useful for inspecting the learned grammar.
-/
def printTopRules (pcfg : PCFG) (topN : Nat := 5) : IO Unit := do
  IO.println s!"\n=== Top {topN} rules per non-terminal ==="
  for (nt, rules) in pcfg.rules do
    let sorted := rules.qsort (fun a b => a.probability > b.probability)
    let top := sorted.extract 0 topN
    IO.println s!"\n{nt}:"
    for wr in top do
      let rhsStr := wr.rule.rhs.toList.map Symbol.toString |> String.intercalate " "
      let probStr := toString (Float.round (wr.probability * 1000) / 1000)
      IO.println s!"  → {rhsStr}  (p={probStr}, n={wr.rule.count})"

/--
Print all rules for a specific non-terminal.
-/
def printRulesFor (pcfg : PCFG) (nt : NonTerminal) : IO Unit := do
  IO.println s!"\n=== Rules for {nt} ==="
  let rules := pcfg.getRulesFor nt
  let sorted := rules.qsort (fun a b => a.probability > b.probability)
  for wr in sorted do
    let rhsStr := wr.rule.rhs.toList.map Symbol.toString |> String.intercalate " "
    let probStr := toString (Float.round (wr.probability * 10000) / 10000)
    IO.println s!"  → {rhsStr}  (p={probStr}, n={wr.rule.count})"

/--
Structure to hold entropy statistics for a non-terminal.
-/
structure NTEntropyStats where
  nt : NonTerminal
  entropy : Float
  numRules : Nat
  totalCount : Nat
  deriving Repr, Inhabited

/--
Compute entropy statistics for all non-terminals.
-/
def computeEntropyStats (pcfg : PCFG) (counts : PCFGCounts) : Array NTEntropyStats := Id.run do
  let mut stats : Array NTEntropyStats := #[]
  for nt in pcfg.nonTerminals do
    let h := entropyFor pcfg nt
    let numRules := (pcfg.rules.getD nt #[]).size
    let totalCount := counts.lhsCounts.getD nt 0
    stats := stats.push { nt, entropy := h, numRules, totalCount }
  return stats

/--
Print entropy statistics to stdout.
Shows overall grammar entropy and lists highest/lowest entropy non-terminals.
-/
def printEntropyStats (pcfg : PCFG) (counts : PCFGCounts) (topN : Nat := 10) : IO Unit := do
  IO.println "\n=== Entropy Statistics ==="

  -- Overall statistics
  let avgH := averageEntropy pcfg
  let weightedH := grammarEntropy pcfg counts
  let avgStr := toString (Float.round (avgH * 1000) / 1000)
  let weightedStr := toString (Float.round (weightedH * 1000) / 1000)

  IO.println s!"Average per-NT entropy:     {avgStr} bits"
  IO.println s!"Weighted grammar entropy:   {weightedStr} bits"

  -- Compute all stats
  let stats := computeEntropyStats pcfg counts

  -- Sort by entropy descending (highest diversity)
  let byEntropyDesc := stats.qsort (fun a b => a.entropy > b.entropy)
  let topHighEntropy := byEntropyDesc.extract 0 topN

  IO.println s!"\n--- Top {topN} highest entropy (most diverse) ---"
  for s in topHighEntropy do
    let hStr := toString (Float.round (s.entropy * 1000) / 1000)
    IO.println s!"  {s.nt}: H={hStr} bits, {s.numRules} rules, {s.totalCount} occurrences"

  -- Sort by entropy ascending (most predictable), but filter out zero-entropy (single rule)
  let nonTrivial := stats.filter (fun s => s.numRules > 1)
  let byEntropyAsc := nonTrivial.qsort (fun a b => a.entropy < b.entropy)
  let topLowEntropy := byEntropyAsc.extract 0 topN

  IO.println s!"\n--- Top {topN} lowest entropy (most predictable, >1 rule) ---"
  for s in topLowEntropy do
    let hStr := toString (Float.round (s.entropy * 1000) / 1000)
    IO.println s!"  {s.nt}: H={hStr} bits, {s.numRules} rules, {s.totalCount} occurrences"

  -- Count single-rule NTs
  let singleRule := stats.filter (fun s => s.numRules == 1)
  IO.println s!"\nDeterministic (single rule): {singleRule.size} non-terminals"

end Lean.PCFG
