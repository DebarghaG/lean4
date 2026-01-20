/-
Tests for PCFG entropy calculations.
-/
import Lean.PCFG

open Lean.PCFG

-- Test log2 function
#guard log2 1.0 == 0.0  -- log2(1) = 0
#guard log2 2.0 == 1.0  -- log2(2) = 1
#guard log2 4.0 == 2.0  -- log2(4) = 2
#guard log2 0.5 == -1.0 -- log2(0.5) = -1

-- Test entropy of uniform distribution
-- H([0.5, 0.5]) = -0.5*log2(0.5) - 0.5*log2(0.5) = 1 bit
def uniformDist2 : Array Float := #[0.5, 0.5]
#guard entropyOfDistribution uniformDist2 == 1.0

-- H([0.25, 0.25, 0.25, 0.25]) = 2 bits
def uniformDist4 : Array Float := #[0.25, 0.25, 0.25, 0.25]
#guard entropyOfDistribution uniformDist4 == 2.0

-- H([1.0]) = 0 bits (deterministic)
def deterministicDist : Array Float := #[1.0]
#guard entropyOfDistribution deterministicDist == 0.0

-- Test entropy bounds: 0 <= H <= log2(n)
def checkEntropyBounds (probs : Array Float) : Bool :=
  let h := entropyOfDistribution probs
  let maxH := log2 probs.size.toFloat
  h >= 0 && h <= maxH + 0.001  -- Small epsilon for float precision

#guard checkEntropyBounds #[0.5, 0.5]
#guard checkEntropyBounds #[0.9, 0.1]
#guard checkEntropyBounds #[0.7, 0.2, 0.1]
#guard checkEntropyBounds #[1.0]

-- Test entropy with zero probability (should be handled correctly)
-- H([1.0, 0.0]) should be 0 (deterministic)
def distWithZero : Array Float := #[1.0, 0.0]
#guard entropyOfDistribution distWithZero == 0.0

-- Test PCFGCounts and entropy computation
def testCountsForEntropy : PCFGCounts :=
  let c := PCFGCounts.empty
  -- Add 10 observations of rule1, 10 of rule2 for `term -> uniform distribution
  let c := c.addRule `term #[Symbol.terminal Terminal.ident]
  let c := c.addRule `term #[Symbol.terminal Terminal.ident]
  let c := c.addRule `term #[Symbol.terminal Terminal.ident]
  let c := c.addRule `term #[Symbol.terminal Terminal.ident]
  let c := c.addRule `term #[Symbol.terminal Terminal.ident]
  let c := c.addRule `term #[Symbol.terminal Terminal.numLit]
  let c := c.addRule `term #[Symbol.terminal Terminal.numLit]
  let c := c.addRule `term #[Symbol.terminal Terminal.numLit]
  let c := c.addRule `term #[Symbol.terminal Terminal.numLit]
  let c := c.addRule `term #[Symbol.terminal Terminal.numLit]
  c

def testPCFGForEntropy : PCFG := computeProbabilities testCountsForEntropy

-- With 5 observations each of 2 rules, we have uniform distribution -> H = 1 bit
#guard entropyFor testPCFGForEntropy `term == 1.0

-- Test average entropy = grammar entropy for single NT
#guard averageEntropy testPCFGForEntropy == 1.0

-- Test deterministic NT (single rule)
def deterministicCounts : PCFGCounts :=
  let c := PCFGCounts.empty
  let c := c.addRule `singleton #[Symbol.terminal Terminal.ident]
  let c := c.addRule `singleton #[Symbol.terminal Terminal.ident]
  c

def deterministicPCFG : PCFG := computeProbabilities deterministicCounts

-- Single rule -> H = 0
#guard entropyFor deterministicPCFG `singleton == 0.0

-- Test smoothed probabilities
def smallCounts : PCFGCounts :=
  let c := PCFGCounts.empty
  let c := c.addRule `small #[Symbol.terminal Terminal.ident]
  c

def smoothedPCFG : PCFG := computeProbabilitiesSmoothed smallCounts 1.0
def unsmoothedPCFG : PCFG := computeProbabilities smallCounts

-- Smoothed probability for single observation with alpha=1: (1+1)/(1+1) = 1.0
-- So entropy should still be 0 for single rule
#guard entropyFor smoothedPCFG `small == 0.0

-- Test cross-entropy with matching grammar (should equal entropy)
-- CE(P, P) = H(P) for the same distribution
def selfCrossEntropy : Float := crossEntropy testPCFGForEntropy testCountsForEntropy

-- Cross-entropy of a distribution with itself equals its entropy
-- Allow small epsilon for floating point
def approxEqual (a b : Float) (eps : Float := 0.001) : Bool :=
  (a - b).abs < eps

#guard approxEqual selfCrossEntropy 1.0

-- Test perplexity = 2^crossEntropy
def testPerplexity : Float := perplexity testPCFGForEntropy testCountsForEntropy
#guard approxEqual testPerplexity 2.0  -- 2^1 = 2

-- Test NTEntropyStats structure
def testStats : Array NTEntropyStats := computeEntropyStats testPCFGForEntropy testCountsForEntropy
#guard testStats.size == 1

-- Check first element using array indexing
def firstStat : NTEntropyStats := testStats[0]!
#guard firstStat.entropy == 1.0
#guard firstStat.numRules == 2
#guard firstStat.totalCount == 10
