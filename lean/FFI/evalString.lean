import Lean

open Lean Parser Elab Tactic Meta

def foo : String := "trivial"

syntax (name := test) "test" : tactic

@[tactic test] def evalTest : Tactic := fun _ =>
  withMainContext do
    match runParserCategory (← getEnv) `tactic foo with
    | .error e => throwError e
    | .ok stx => evalTactic $ ← `(tactic| $(⟨stx⟩))
