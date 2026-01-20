/-
Copyright (c) 2024 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DebarghaG
-/
import Std.Data.HashMap
import Std.Data.HashSet

namespace Lean.PCFG

/--
Abstract terminal categories for PCFG rules.

Terminals are abstracted to avoid memorizing specific values:
- Keywords are preserved (e.g., "def", "theorem")
- Identifiers, literals are abstracted to categories
-/
inductive Terminal where
  /-- A keyword like "def", "theorem", "where", "let", etc. -/
  | keyword (val : String)
  /-- An operator or punctuation symbol like "+", "→", "(", ")", etc. -/
  | symbol (val : String)
  /-- Any identifier (abstracted) -/
  | ident
  /-- Numeric literals -/
  | numLit
  /-- String literals -/
  | strLit
  /-- Character literals -/
  | charLit
  /-- Scientific notation literals -/
  | scientificLit
  /-- Name literals (backtick names like `foo) -/
  | nameLit
  deriving BEq, Hashable, Repr, Inhabited

namespace Terminal

def toString : Terminal → String
  | keyword k => s!"'{k}'"
  | symbol s => s!"'{s}'"
  | ident => "<ident>"
  | numLit => "<num>"
  | strLit => "<str>"
  | charLit => "<char>"
  | scientificLit => "<scientific>"
  | nameLit => "<name>"

instance : ToString Terminal := ⟨Terminal.toString⟩

end Terminal

/-- NonTerminal is a syntax node kind, which is just a Name -/
abbrev NonTerminal := Name

-- Name already has ToString from Init.Data.ToString.Name

/-- A symbol in the RHS of a production rule -/
inductive Symbol where
  /-- A terminal symbol -/
  | terminal (t : Terminal)
  /-- A non-terminal symbol (reference to another production) -/
  | nonTerminal (nt : NonTerminal)
  deriving BEq, Hashable, Repr, Inhabited

namespace Symbol

def toString : Symbol → String
  | terminal t => t.toString
  | nonTerminal nt => s!"<{nt}>"

instance : ToString Symbol := ⟨Symbol.toString⟩

end Symbol

/-- A production rule with its occurrence count -/
structure ProductionRule where
  /-- The left-hand side non-terminal -/
  lhs : NonTerminal
  /-- The right-hand side sequence of symbols -/
  rhs : Array Symbol
  /-- Number of times this rule was observed -/
  count : Nat := 0
  deriving Repr, Inhabited

namespace ProductionRule

def toString (r : ProductionRule) : String :=
  let rhsStr := r.rhs.toList.map Symbol.toString |> String.intercalate " "
  s!"{r.lhs} → {rhsStr} [{r.count}]"

instance : ToString ProductionRule := ⟨ProductionRule.toString⟩

end ProductionRule

/-- A production rule with its computed probability -/
structure WeightedRule where
  /-- The underlying production rule -/
  rule : ProductionRule
  /-- Probability of this rule given its LHS: P(rule | lhs) -/
  probability : Float
  deriving Repr, Inhabited

namespace WeightedRule

def toString (wr : WeightedRule) : String :=
  let rhsStr := wr.rule.rhs.toList.map Symbol.toString |> String.intercalate " "
  s!"{wr.rule.lhs} → {rhsStr} (p={wr.probability}, n={wr.rule.count})"

instance : ToString WeightedRule := ⟨WeightedRule.toString⟩

end WeightedRule

/-- Accumulated counts during PCFG training -/
structure PCFGCounts where
  /-- Map from LHS to (RHS → count) -/
  rules : Std.HashMap NonTerminal (Std.HashMap (Array Symbol) Nat) := {}
  /-- Total count for each LHS non-terminal -/
  lhsCounts : Std.HashMap NonTerminal Nat := {}
  deriving Inhabited

namespace PCFGCounts

/-- Create an empty PCFGCounts -/
def empty : PCFGCounts := {}

/-- Add an observation of a production rule -/
def addRule (counts : PCFGCounts) (lhs : NonTerminal) (rhs : Array Symbol) : PCFGCounts :=
  let rhsMap := counts.rules.getD lhs {}
  let newCount := rhsMap.getD rhs 0 + 1
  { rules := counts.rules.insert lhs (rhsMap.insert rhs newCount)
    lhsCounts := counts.lhsCounts.insert lhs (counts.lhsCounts.getD lhs 0 + 1) }

/-- Get total number of unique production rules -/
def numRules (counts : PCFGCounts) : Nat :=
  counts.rules.fold (init := 0) fun acc _ rhsMap => acc + rhsMap.size

/-- Get total number of non-terminals -/
def numNonTerminals (counts : PCFGCounts) : Nat :=
  counts.rules.size

end PCFGCounts

/-- The final Probabilistic Context-Free Grammar -/
structure PCFG where
  /-- All production rules grouped by LHS non-terminal -/
  rules : Std.HashMap NonTerminal (Array WeightedRule) := {}
  /-- Set of all non-terminals in the grammar -/
  nonTerminals : Std.HashSet NonTerminal := {}
  /-- Set of all terminals in the grammar -/
  terminals : Std.HashSet Terminal := {}
  /-- Start symbols (typically module, command, term) -/
  startSymbols : Array NonTerminal := #[]
  deriving Inhabited

namespace PCFG

/-- Create an empty PCFG -/
def empty : PCFG := {}

/-- Get total number of production rules -/
def numRules (pcfg : PCFG) : Nat :=
  pcfg.rules.fold (init := 0) fun acc _ rs => acc + rs.size

/-- Get rules for a specific non-terminal -/
def getRulesFor (pcfg : PCFG) (nt : NonTerminal) : Array WeightedRule :=
  pcfg.rules.getD nt #[]

/-- Get all rules sorted by probability (descending) for a non-terminal -/
def getTopRulesFor (pcfg : PCFG) (nt : NonTerminal) (n : Nat := 10) : Array WeightedRule :=
  let rules := pcfg.getRulesFor nt
  let sorted := rules.qsort (fun a b => a.probability > b.probability)
  sorted.extract 0 n

/-- Pretty print the PCFG -/
def toString (pcfg : PCFG) : String :=
  let header := s!"PCFG with {pcfg.nonTerminals.size} non-terminals, {pcfg.terminals.size} terminals, {pcfg.numRules} rules\n"
  let startStr := s!"Start symbols: {pcfg.startSymbols.toList}\n"
  header ++ startStr

instance : ToString PCFG := ⟨PCFG.toString⟩

end PCFG

end Lean.PCFG
