inductive T where
  | A : T
  | B : T
  | C : T

instance : ToString T where
 toString := fun t =>
   match t with
   | T.A => "T.A"
   | T.B => "T.B"
   | T.C => "T.C"

@[extern "my_foo"]
opaque myFoo : T → String

@[extern "my_bar"]
def myBar : String → T := fun _ => T.A


