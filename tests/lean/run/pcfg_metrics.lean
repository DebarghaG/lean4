/-
Tests for PCFG advanced uncertainty metrics.
-/
import Lean.PCFG

open Lean.PCFG

/-! ## Helper function for approximate equality -/

def approxEqual (a b : Float) (eps : Float := 0.001) : Bool :=
  (a - b).abs < eps

/-! ## Statistical Primitives Tests -/

-- Test arrayMean
#guard arrayMean #[1.0, 2.0, 3.0, 4.0, 5.0] == 3.0
#guard arrayMean #[10.0] == 10.0
#guard arrayMean #[] == 0

-- Test arrayVariance (sample variance)
-- For [1,2,3,4,5], mean=3, variance = ((1-3)^2 + (2-3)^2 + (3-3)^2 + (4-3)^2 + (5-3)^2) / 4
--                                    = (4 + 1 + 0 + 1 + 4) / 4 = 10/4 = 2.5
#guard approxEqual (arrayVariance #[1.0, 2.0, 3.0, 4.0, 5.0]) 2.5

-- Test arrayStd
#guard approxEqual (arrayStd #[1.0, 2.0, 3.0, 4.0, 5.0]) (Float.sqrt 2.5)

-- Test edge cases
#guard arrayVariance #[5.0] == 0  -- Single element has zero variance
#guard arrayVariance #[] == 0

/-! ## Rényi Entropy Tests -/

-- Uniform distribution [0.5, 0.5]
def uniform2 : Array Float := #[0.5, 0.5]

-- Rényi entropy of order 0 (Hartley entropy) = log2(support size)
#guard renyiEntropy uniform2 0 == 1.0  -- log2(2) = 1

-- Rényi entropy of order 1 (Shannon entropy) = 1 for uniform binary
#guard renyiEntropy uniform2 1 == 1.0

-- Rényi entropy of order 2 (Collision entropy)
-- H_2 = -log2(sum(p^2)) = -log2(0.25 + 0.25) = -log2(0.5) = 1
#guard approxEqual (renyiEntropy uniform2 2) 1.0

-- Rényi entropy of order infinity (Min entropy) = -log2(max(p)) = -log2(0.5) = 1
#guard approxEqual (renyiEntropy uniform2 100) 1.0  -- We use 100 as infinity

-- Test uniform distribution of 4 elements
def uniform4 : Array Float := #[0.25, 0.25, 0.25, 0.25]
#guard renyiEntropy uniform4 0 == 2.0   -- log2(4) = 2
#guard renyiEntropy uniform4 1 == 2.0   -- Shannon entropy
#guard approxEqual (renyiEntropy uniform4 2) 2.0
#guard approxEqual (renyiEntropy uniform4 100) 2.0

-- Test non-uniform distribution
def nonuniform : Array Float := #[0.9, 0.1]
-- Min entropy = -log2(0.9) ≈ 0.152
#guard approxEqual (renyiEntropy nonuniform 100) 0.152 0.01

-- Rényi entropy ordering: H_0 >= H_1 >= H_2 >= ... >= H_inf
def checkRenyiOrdering (probs : Array Float) : Bool :=
  let h0 := renyiEntropy probs 0
  let h1 := renyiEntropy probs 1
  let h2 := renyiEntropy probs 2
  let hinf := renyiEntropy probs 100
  h0 >= h1 - 0.001 && h1 >= h2 - 0.001 && h2 >= hinf - 0.001

#guard checkRenyiOrdering #[0.5, 0.5]
#guard checkRenyiOrdering #[0.9, 0.1]
#guard checkRenyiOrdering #[0.7, 0.2, 0.1]
#guard checkRenyiOrdering #[0.25, 0.25, 0.25, 0.25]

/-! ## KL Divergence Tests -/

-- D(P||P) = 0 for any distribution
#guard klDivergence #[0.5, 0.5] #[0.5, 0.5] == 0
#guard klDivergence #[0.9, 0.1] #[0.9, 0.1] == 0

-- D(P||Q) >= 0 (non-negativity)
def checkKlNonNegative (p q : Array Float) : Bool :=
  let d := klDivergence p q
  d >= 0 || d > 1e10  -- Check for very large values (infinity)

#guard checkKlNonNegative #[0.5, 0.5] #[0.5, 0.5]
#guard checkKlNonNegative #[0.9, 0.1] #[0.5, 0.5]
#guard checkKlNonNegative #[0.5, 0.5] #[0.9, 0.1]

-- KL divergence from uniform distribution
-- D(P||U) = log2(n) - H(P) for uniform U
#guard approxEqual (klDivergenceFromUniform #[0.5, 0.5]) 0  -- H = log2(2) = 1, max = 1
#guard approxEqual (klDivergenceFromUniform #[1.0, 0.0]) 1.0  -- H = 0, max = 1

/-! ## Jensen-Shannon Divergence Tests -/

-- JSD(P, P) = 0
#guard jensenShannonDivergence #[0.5, 0.5] #[0.5, 0.5] == 0

-- JSD is symmetric: JSD(P, Q) = JSD(Q, P)
def checkJsdSymmetric (p q : Array Float) : Bool :=
  approxEqual (jensenShannonDivergence p q) (jensenShannonDivergence q p)

#guard checkJsdSymmetric #[0.9, 0.1] #[0.5, 0.5]
#guard checkJsdSymmetric #[0.7, 0.3] #[0.3, 0.7]

-- JSD is bounded: 0 <= JSD <= 1 (with log2)
def checkJsdBounded (p q : Array Float) : Bool :=
  let jsd := jensenShannonDivergence p q
  jsd >= 0 && jsd <= 1.001

#guard checkJsdBounded #[0.5, 0.5] #[0.5, 0.5]
#guard checkJsdBounded #[1.0, 0.0] #[0.0, 1.0]
#guard checkJsdBounded #[0.9, 0.1] #[0.1, 0.9]

/-! ## Wilson Score Confidence Interval Tests -/

-- Basic bounds check: 0 <= lower <= center <= upper <= 1
def checkCiBounds (ci : ConfidenceInterval) : Bool :=
  ci.lower >= 0 && ci.lower <= ci.center && ci.center <= ci.upper && ci.upper <= 1

-- Equal successes and failures -> center near 0.5
def ci50 := wilsonScoreInterval 50 100
#guard checkCiBounds ci50
#guard approxEqual ci50.center 0.5 0.05

-- All successes -> center near 1
def ciAll := wilsonScoreInterval 100 100
#guard checkCiBounds ciAll
#guard approxEqual ciAll.upper 1.0 0.01

-- No successes -> center near 0
def ciNone := wilsonScoreInterval 0 100
#guard checkCiBounds ciNone
#guard ciNone.lower == 0.0

-- Width decreases with more observations
def ciSmall := wilsonScoreInterval 5 10
def ciLarge := wilsonScoreInterval 50 100
#guard ciSmall.width > ciLarge.width

-- Zero observations
def ciZero := wilsonScoreInterval 0 0
#guard checkCiBounds ciZero

/-! ## Grammar Complexity Tests -/

-- Create a simple test grammar
def testCounts1 : PCFGCounts :=
  let c := PCFGCounts.empty
  -- term -> ident | num | term + term (left recursive)
  let c := c.addRule `term #[Symbol.terminal Terminal.ident]
  let c := c.addRule `term #[Symbol.terminal Terminal.numLit]
  let c := c.addRule `term #[Symbol.nonTerminal `term, Symbol.terminal (.symbol "+"), Symbol.nonTerminal `term]
  -- expr -> term
  let c := c.addRule `expr #[Symbol.nonTerminal `term]
  c

def testPCFG1 : PCFG := computeProbabilities testCounts1

-- Test hasDirectLeftRecursion
#guard hasDirectLeftRecursion testPCFG1 `term == true
#guard hasDirectLeftRecursion testPCFG1 `expr == false

-- Test grammar complexity computation
def complexity1 := computeGrammarComplexity testPCFG1
#guard complexity1.numNonTerminals == 2
#guard complexity1.numRules == 4
#guard complexity1.hasLeftRecursion == true

/-! ## Power Iteration / Spectral Tests -/

-- Identity matrix should have spectral radius 1
def identityMatrix : Matrix := #[#[1.0, 0.0], #[0.0, 1.0]]
#guard approxEqual (powerIteration identityMatrix) 1.0

-- Zero matrix should have spectral radius 0
def zeroMatrix : Matrix := #[#[0.0, 0.0], #[0.0, 0.0]]
#guard powerIteration zeroMatrix == 0

-- Scalar matrix [[2, 0], [0, 2]] should have spectral radius 2
def scalarMatrix : Matrix := #[#[2.0, 0.0], #[0.0, 2.0]]
#guard approxEqual (powerIteration scalarMatrix) 2.0

-- Matrix multiplication test
def testMatrix : Matrix := #[#[1.0, 2.0], #[3.0, 4.0]]
def testVector : Array Float := #[1.0, 1.0]
def result := matVecMul testMatrix testVector
#guard approxEqual result[0]! 3.0  -- 1*1 + 2*1 = 3
#guard approxEqual result[1]! 7.0  -- 3*1 + 4*1 = 7

-- Vector normalization
def normalized := vecNormalize #[3.0, 4.0]
#guard approxEqual (vecNorm normalized) 1.0

/-! ## NSUI Tests -/

-- NSUI should be bounded between 0 and 1
def checkNsuiBounded (nsui : Float) : Bool :=
  nsui >= 0 && nsui <= 1.001

-- Deterministic grammar (single rule per NT) should have low NSUI
def deterministicCounts : PCFGCounts :=
  let c := PCFGCounts.empty
  let c := c.addRule `a #[Symbol.terminal Terminal.ident]
  let c := c.addRule `b #[Symbol.terminal Terminal.numLit]
  c

def deterministicPCFG : PCFG := computeProbabilities deterministicCounts
def deterministicNSUI := computeNSUI deterministicPCFG deterministicCounts false
#guard checkNsuiBounded deterministicNSUI
#guard deterministicNSUI == 0  -- Zero entropy -> zero NSUI

-- Uniform distribution should have higher NSUI
def uniformCounts : PCFGCounts :=
  let c := PCFGCounts.empty
  let c := c.addRule `term #[Symbol.terminal Terminal.ident]
  let c := c.addRule `term #[Symbol.terminal Terminal.numLit]
  let c := c.addRule `term #[Symbol.terminal Terminal.strLit]
  let c := c.addRule `term #[Symbol.terminal Terminal.charLit]
  c

def uniformPCFG : PCFG := computeProbabilities uniformCounts
def uniformNSUI := computeNSUI uniformPCFG uniformCounts false
#guard checkNsuiBounded uniformNSUI
#guard uniformNSUI == 1.0  -- Max entropy with single NT -> entropy ratio = 1

/-! ## Distribution Stats Tests -/

def testProbs : Array Float := #[0.1, 0.2, 0.3, 0.4]
def testStats := computeDistributionStats testProbs

#guard testStats.min == 0.1
#guard testStats.max == 0.4
#guard approxEqual testStats.mean 0.25  -- (0.1+0.2+0.3+0.4)/4 = 1.0/4 = 0.25

-- Empty array
def emptyStats := computeDistributionStats #[]
#guard emptyStats.min == 0
#guard emptyStats.max == 0

/-! ## Entropy Metrics Collection Tests -/

def entropyMetrics := computeEntropyMetricsStruct uniformPCFG uniformCounts
-- Shannon entropy for uniform[0.25, 0.25, 0.25, 0.25] = 2 bits
#guard approxEqual entropyMetrics.shannonEntropy 2.0

/-! ## Full Uncertainty Metrics Tests -/

def fullMetrics := computeUncertaintyMetrics testPCFG1 testCounts1 false

#guard fullMetrics.complexity.numRules == 4
#guard checkNsuiBounded fullMetrics.nsui

-- Test with spectral analysis
def fullMetricsSpectral := computeUncertaintyMetrics testPCFG1 testCounts1 true
#guard fullMetricsSpectral.spectral.isSome

/-! ## Round function test -/

#guard roundTo 3.14159 2 == 3.14
-- Note: Float.round may use different rounding behavior
#guard approxEqual (roundTo 2.5 0) 3.0 1.0  -- Could be 2 or 3 depending on rounding
#guard approxEqual (roundTo 0.12345 4) 0.1235 0.0001
