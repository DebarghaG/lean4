/-
Tests for PCFG extraction from syntax trees.
-/
import Lean.PCFG

open Lean Lean.PCFG

-- Test isLiteralKind
#guard isLiteralKind numLitKind == true
#guard isLiteralKind strLitKind == true
#guard isLiteralKind charLitKind == true
#guard isLiteralKind scientificLitKind == true
#guard isLiteralKind nameLitKind == true
#guard isLiteralKind `someOtherKind == false
#guard isLiteralKind nullKind == false

-- Test syntaxToTerminal with atoms
#guard syntaxToTerminal (Syntax.atom SourceInfo.none "def") == some (Terminal.keyword "def")
#guard syntaxToTerminal (Syntax.atom SourceInfo.none "theorem") == some (Terminal.keyword "theorem")
#guard syntaxToTerminal (Syntax.atom SourceInfo.none "+") == some (Terminal.symbol "+")
#guard syntaxToTerminal (Syntax.atom SourceInfo.none "→") == some (Terminal.symbol "→")
#guard syntaxToTerminal (Syntax.atom SourceInfo.none "(") == some (Terminal.symbol "(")

-- Test syntaxToTerminal with identifiers
#guard syntaxToTerminal (Syntax.ident SourceInfo.none "x".toRawSubstring `x []) == some Terminal.ident

-- Test syntaxToTerminal with missing
#guard syntaxToTerminal Syntax.missing == none

-- Test isTerminalSyntax
#guard isTerminalSyntax (Syntax.atom SourceInfo.none "def") == true
#guard isTerminalSyntax (Syntax.ident SourceInfo.none "x".toRawSubstring `x []) == true
#guard isTerminalSyntax Syntax.missing == true

-- Test with a non-literal node (should not be terminal)
def nonLiteralNode : Syntax := Syntax.node SourceInfo.none `someKind #[]
#guard isTerminalSyntax nonLiteralNode == false

-- Test extractProduction with nullKind (should return none)
def nullNode : Syntax := Syntax.node SourceInfo.none nullKind #[]
#guard extractProduction nullNode == none

-- Test extractProduction with a simple node
def simpleNode : Syntax := Syntax.node SourceInfo.none `myKind #[Syntax.atom SourceInfo.none "hello"]
#guard (extractProduction simpleNode).isSome

-- Test that extractProduction returns the correct LHS
def checkLhs : Bool :=
  match extractProduction simpleNode with
  | some (lhs, _) => lhs == `myKind
  | none => false
#guard checkLhs

-- Test countProductions with a simple tree
def simpleSyntax : Syntax :=
  Syntax.node SourceInfo.none `outer #[
    Syntax.node SourceInfo.none `inner #[Syntax.atom SourceInfo.none "x"],
    Syntax.atom SourceInfo.none "+"
  ]

def countsFromSimple : PCFGCounts :=
  countProductions simpleSyntax PCFGCounts.empty

-- Should have extracted productions for both `outer and `inner
#guard countsFromSimple.numNonTerminals == 2
