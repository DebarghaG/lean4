/-
Tests for PCFG basic data structures.
-/
import Lean.PCFG.Basic

open Lean.PCFG

-- Test Terminal representation
#guard Terminal.ident.toString == "<ident>"
#guard (Terminal.keyword "def").toString == "'def'"
#guard (Terminal.symbol "+").toString == "'+'"
#guard Terminal.numLit.toString == "<num>"
#guard Terminal.strLit.toString == "<str>"

-- Test Symbol representation
#guard (Symbol.terminal Terminal.ident).toString == "<ident>"
#guard (Symbol.nonTerminal `term).toString == "<term>"

-- Test Terminal equality
#guard Terminal.ident == Terminal.ident
#guard Terminal.ident != Terminal.numLit
#guard Terminal.keyword "def" == Terminal.keyword "def"
#guard Terminal.keyword "def" != Terminal.keyword "theorem"

-- Test Symbol equality
#guard Symbol.terminal Terminal.ident == Symbol.terminal Terminal.ident
#guard Symbol.nonTerminal `term == Symbol.nonTerminal `term
#guard Symbol.nonTerminal `term != Symbol.nonTerminal `tactic

-- Test PCFGCounts
def testCounts : PCFGCounts :=
  let c := PCFGCounts.empty
  let c := c.addRule `term #[Symbol.terminal Terminal.ident]
  let c := c.addRule `term #[Symbol.terminal Terminal.ident]  -- Same rule again
  let c := c.addRule `term #[Symbol.nonTerminal `term, Symbol.terminal (Terminal.symbol "+"), Symbol.nonTerminal `term]
  c

#guard testCounts.numNonTerminals == 1
#guard testCounts.numRules == 2  -- Two distinct rules for `term

-- Test PCFG
def emptyPCFG : PCFG := PCFG.empty
#guard emptyPCFG.nonTerminals.isEmpty
#guard emptyPCFG.terminals.isEmpty
#guard emptyPCFG.numRules == 0
