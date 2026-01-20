/-
Sanity check for PCFG extraction on synthetic syntax trees.
Tests the full extraction -> probability -> entropy pipeline.
-/
import Lean.PCFG

open Lean Lean.PCFG

-- Create a realistic-looking syntax tree representing:
-- def foo := 1 + 2
-- (Simplified structure)

def syntheticSyntax : Syntax :=
  -- Root: command
  Syntax.node SourceInfo.none `command #[
    -- def declaration
    Syntax.node SourceInfo.none `Lean.Parser.Command.declaration #[
      Syntax.node SourceInfo.none `Lean.Parser.Command.def #[
        Syntax.atom SourceInfo.none "def",
        Syntax.ident SourceInfo.none "foo".toRawSubstring `foo [],
        Syntax.node SourceInfo.none `Lean.Parser.Command.optDeclSig #[],
        Syntax.atom SourceInfo.none ":=",
        Syntax.node SourceInfo.none `term #[
          Syntax.node SourceInfo.none `Lean.Parser.Term.app #[
            Syntax.node SourceInfo.none `term #[
              Syntax.ident SourceInfo.none "+".toRawSubstring `HAdd.hAdd []
            ],
            Syntax.node SourceInfo.none `Lean.Parser.Term.app #[
              Syntax.node SourceInfo.none `num #[
                Syntax.atom SourceInfo.none "1"
              ],
              Syntax.node SourceInfo.none `num #[
                Syntax.atom SourceInfo.none "2"
              ]
            ]
          ]
        ]
      ]
    ]
  ]

-- Extract productions from synthetic syntax
def syntheticCounts : PCFGCounts := countProductions syntheticSyntax PCFGCounts.empty

-- Should have extracted some productions
#guard syntheticCounts.numNonTerminals > 0
#guard syntheticCounts.numRules > 0

-- Compute probabilities
def syntheticPCFG : PCFG := computeProbabilities syntheticCounts

-- PCFG should have non-terminals and rules
#guard syntheticPCFG.nonTerminals.size > 0
#guard syntheticPCFG.numRules > 0

-- Entropy should be non-negative
def avgH : Float := averageEntropy syntheticPCFG
#guard avgH >= 0

-- Grammar entropy should be non-negative
def gramH : Float := grammarEntropy syntheticPCFG syntheticCounts
#guard gramH >= 0

-- Test with smoothing
def smoothedPCFG : PCFG := computeProbabilitiesSmoothed syntheticCounts 1.0
#guard smoothedPCFG.numRules > 0

-- Cross-entropy with same data should equal entropy (approximately)
def ce : Float := crossEntropy syntheticPCFG syntheticCounts
-- CE should be finite (not infinity)
#guard ce < 100.0  -- Reasonable upper bound

-- Perplexity should be positive
def pp : Float := perplexity syntheticPCFG syntheticCounts
#guard pp > 0

-- Print some stats for manual inspection (won't fail, just informative)
#eval do
  IO.println s!"=== Sanity Check Results ==="
  IO.println s!"Non-terminals: {syntheticPCFG.nonTerminals.size}"
  IO.println s!"Rules: {syntheticPCFG.numRules}"
  IO.println s!"Average entropy: {avgH} bits"
  IO.println s!"Weighted entropy: {gramH} bits"
  IO.println s!"Cross-entropy: {ce} bits"
  IO.println s!"Perplexity: {pp}"
