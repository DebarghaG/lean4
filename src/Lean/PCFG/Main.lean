/-
Copyright (c) 2024 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DebarghaG
-/
import Lean.PCFG.Extract
import Lean.PCFG.Probability
import Lean.Util.Path

namespace Lean.PCFG

/-- Command-line options for the PCFG extraction tool -/
structure Options where
  /-- Input directory or file to process -/
  inputPath : System.FilePath
  /-- Whether to print verbose output -/
  verbose : Bool := false
  /-- Number of top rules to print per non-terminal (0 = don't print) -/
  topN : Nat := 0
  /-- Specific non-terminal to inspect -/
  inspectNt : Option Name := none
  /-- Whether to print entropy statistics -/
  showEntropy : Bool := false
  /-- Laplace smoothing parameter (0 = no smoothing) -/
  smoothingAlpha : Float := 0.0
  deriving Repr, Inhabited

/-- Print usage information -/
def printUsage : IO Unit := do
  IO.println "Usage: pcfg-extract <input-path> [options]"
  IO.println ""
  IO.println "Extract a PCFG from Lean source files."
  IO.println ""
  IO.println "Arguments:"
  IO.println "  <input-path>    Directory or .lean file to process"
  IO.println ""
  IO.println "Options:"
  IO.println "  -v, --verbose   Print verbose output"
  IO.println "  --top N         Print top N rules per non-terminal"
  IO.println "  --inspect NAME  Print all rules for a specific non-terminal"
  IO.println "  --entropy       Print entropy statistics"
  IO.println "  --smooth ALPHA  Use Laplace smoothing with given alpha (default: 0)"
  IO.println "  -h, --help      Print this help message"

/-- Exception to signal help was requested -/
inductive ParseResult where
  | options : Options → ParseResult
  | helpRequested : ParseResult
  | error : String → ParseResult

/-- Parse command-line arguments -/
def parseArgs (args : List String) : ParseResult :=
  let rec go (args : List String) (opts : Options) : ParseResult :=
    match args with
    | [] => .options opts
    | "-v" :: rest | "--verbose" :: rest =>
      go rest { opts with verbose := true }
    | "--top" :: n :: rest =>
      match n.toNat? with
      | some n => go rest { opts with topN := n }
      | none => .error s!"Invalid number: {n}"
    | "--inspect" :: name :: rest =>
      go rest { opts with inspectNt := some name.toName }
    | "--entropy" :: rest =>
      go rest { opts with showEntropy := true }
    | "--smooth" :: alpha :: rest =>
      -- Parse float by trying to convert string
      let alphaVal := alpha.toNat?.getD 1 |>.toFloat
      go rest { opts with smoothingAlpha := alphaVal }
    | "-h" :: _ | "--help" :: _ =>
      .helpRequested
    | path :: rest =>
      if opts.inputPath.toString.isEmpty then
        go rest { opts with inputPath := path }
      else
        .error s!"Unexpected argument: {path}"
  if args.isEmpty then
    .helpRequested
  else
    go args { inputPath := "" }

/--
Initialize the Lean environment for parsing.
This loads the basic Lean modules needed for parsing syntax.
-/
def initEnvironment : IO Environment := do
  -- Initialize search path
  initSearchPath (← getBuildDir)
  -- Import Init module for basic parsing support
  let imports := #[{ module := `Init : Import }]
  importModules imports {} 0

/--
Main entry point for the PCFG extraction tool.
-/
def main (args : List String) : IO UInt32 := do
  match parseArgs args with
  | .helpRequested =>
    printUsage
    return 0
  | .error msg =>
    IO.eprintln s!"Error: {msg}"
    printUsage
    return 1
  | .options opts =>
    try
      if opts.verbose then
        IO.println "Initializing Lean environment..."

      let env ← initEnvironment

      if opts.verbose then
        IO.println s!"Processing: {opts.inputPath}"

      -- Process input
      let mut counts := PCFGCounts.empty
      if ← opts.inputPath.isDir then
        counts ← processDirectory env opts.inputPath counts opts.verbose
      else if opts.inputPath.extension == some "lean" then
        counts ← processFile env opts.inputPath counts opts.verbose
      else
        throw (IO.userError s!"Input must be a directory or .lean file: {opts.inputPath}")

      -- Compute probabilities
      if opts.verbose then
        IO.println "Computing probabilities..."

      let pcfg := if opts.smoothingAlpha > 0 then
        computeProbabilitiesSmoothed counts opts.smoothingAlpha
      else
        computeProbabilities counts

      -- Print summary
      printSummary pcfg

      -- Print top rules if requested
      if opts.topN > 0 then
        printTopRules pcfg opts.topN

      -- Print specific non-terminal if requested
      if let some nt := opts.inspectNt then
        printRulesFor pcfg nt

      -- Print entropy statistics if requested
      if opts.showEntropy then
        printEntropyStats pcfg counts

      return 0
    catch e =>
      IO.eprintln s!"Error: {e}"
      return 1

end Lean.PCFG
