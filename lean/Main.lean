import FFI

def main : IO Unit := do
  let tac := mkTac "tac"
  IO.println s!"{tac.stx}"

  let step1 := mkStepTac `nm "type" tac
  match step1 with
  | .tac _ type _ => IO.println s!"{type}"
  | _ => IO.println "missing"

  let step2 := mkStepThm `nm2 "type2" []
  match step2 with
  | .thm nm _ _ => IO.println s!"{nm}"
  | _ => IO.println "missing 2"

  let step3 := mkStepScope `nm3 "type3" []
  match step3 with
  | .scope nm _ _ => IO.println s!"{nm}"
  | _ => IO.println "missing 3"

  let cvc5Proof := mkCvc5Proof [step1, step2, step3]
  match cvc5Proof with
  | [_, _, _] => IO.println "cvc5Proof ok"
  | _ => IO.println s!"missing 4"
