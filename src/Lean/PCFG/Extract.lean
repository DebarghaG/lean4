/-
Copyright (c) 2024 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DebarghaG
-/
import Lean.PCFG.Basic
import Lean.Syntax
import Lean.Parser.Module
import Lean.Environment

namespace Lean.PCFG

/-- Check if a Name represents a known literal kind -/
def isLiteralKind (k : SyntaxNodeKind) : Bool :=
  k == numLitKind || k == strLitKind || k == charLitKind ||
  k == scientificLitKind || k == nameLitKind

/--
Convert a Syntax leaf node to a Terminal.
Returns `none` if the syntax is not a terminal (i.e., it's an internal node).
-/
def syntaxToTerminal (stx : Syntax) : Option Terminal :=
  match stx with
  | .atom _ val =>
    -- Atoms are either keywords (alphabetic) or symbols (operators/punctuation)
    if val.length > 0 && val.all Char.isAlpha then
      some (.keyword val)
    else
      some (.symbol val)
  | .ident .. =>
    -- All identifiers are abstracted to a single terminal
    some .ident
  | .node _ k _ =>
    -- Literal nodes are treated as terminals even though they have structure
    if k == numLitKind then some .numLit
    else if k == strLitKind then some .strLit
    else if k == charLitKind then some .charLit
    else if k == scientificLitKind then some .scientificLit
    else if k == nameLitKind then some .nameLit
    else none  -- Not a terminal - it's an internal node
  | .missing =>
    -- Missing nodes (from parse errors) are ignored
    none

/--
Check if a Syntax node should be treated as a terminal in the PCFG sense.
Terminals are leaf nodes: atoms, identifiers, missing, and literal nodes.
-/
def isTerminalSyntax (stx : Syntax) : Bool :=
  match stx with
  | .atom .. | .ident .. | .missing => true
  | .node _ k args =>
    -- Literal nodes are terminals (they have fixed structure)
    isLiteralKind k && args.size ≤ 1

/--
Convert a child syntax node to a Symbol.
- If it's a terminal, convert it to a Terminal symbol
- If it's an internal node, use its kind as a NonTerminal symbol
- Skip nullKind nodes (they're just grouping)
-/
def syntaxToSymbol (stx : Syntax) : Option Symbol :=
  if isTerminalSyntax stx then
    syntaxToTerminal stx |>.map .terminal
  else
    match stx with
    | .node _ k _ =>
      if k != nullKind then some (.nonTerminal k) else none
    | _ => none

/--
Extract the production rule implied by a syntax node.
Returns `(lhs, rhs)` where `lhs` is the node's kind and `rhs` is the sequence of symbols
derived from its children.

Returns `none` for:
- Non-node syntax (atoms, idents, missing)
- Nodes with nullKind (grouping nodes without semantic meaning)
-/
def extractProduction (stx : Syntax) : Option (NonTerminal × Array Symbol) :=
  match stx with
  | .node _ kind args =>
    -- Skip nullKind nodes - they're just for grouping
    if kind == nullKind then
      none
    else
      -- Convert each child to a symbol, filtering out nullKind children
      let rhs := args.filterMap syntaxToSymbol
      some (kind, rhs)
  | _ => none

/--
Count all production rules in a syntax tree by traversing it top-down.
Uses `firstChoiceOnly := true` to handle ambiguous parses deterministically.
-/
def countProductions (stx : Syntax) (counts : PCFGCounts) : PCFGCounts := Id.run do
  let mut counts := counts
  for node in stx.topDown (firstChoiceOnly := true) do
    if let some (lhs, rhs) := extractProduction node then
      counts := counts.addRule lhs rhs
  return counts

/--
Parse a single Lean file and return its raw syntax tree.
Uses the Lean parser infrastructure.
-/
def parseFile (env : Environment) (path : System.FilePath) : IO Syntax := do
  let stx ← Parser.testParseFile env path
  return stx.raw

/--
Recursively process all .lean files in a directory, accumulating production counts.
Continues processing even if individual files fail to parse.
-/
partial def processDirectory (env : Environment) (dir : System.FilePath)
    (counts : PCFGCounts) (verbose : Bool := false) : IO PCFGCounts := do
  let mut counts := counts
  let entries ← dir.readDir
  for entry in entries do
    let path := entry.path
    if ← path.isDir then
      counts ← processDirectory env path counts verbose
    else if path.extension == some "lean" then
      try
        let stx ← parseFile env path
        counts := countProductions stx counts
        if verbose then
          IO.println s!"Processed: {path}"
      catch e =>
        IO.eprintln s!"Warning: Failed to parse {path}: {e}"
  return counts

/--
Process a single file and return updated counts.
-/
def processFile (env : Environment) (path : System.FilePath)
    (counts : PCFGCounts) (verbose : Bool := false) : IO PCFGCounts := do
  try
    let stx ← parseFile env path
    let counts := countProductions stx counts
    if verbose then
      IO.println s!"Processed: {path}"
    return counts
  catch e =>
    IO.eprintln s!"Warning: Failed to parse {path}: {e}"
    return counts

end Lean.PCFG
