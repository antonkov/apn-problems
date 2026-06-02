import Lean.Elab.SyntheticMVars
import Batteries.Lean.Expr

/-!
# The `answer( )` elaborator

Indicates where the answer is in a problem statement.
`answer(sorry)` defaults to `True` when the expected type is `Prop`.
-/

/-- Indicates where the answer is in a problem statement. -/
syntax (name := answer) "answer(" term ")" : term

open Lean Elab Meta Term in
/-- Elaborator for `answer()`. In default mode, `answer(sorry)` becomes `True`. -/
@[term_elab answer]
def answerElab : TermElab := fun stx expectedType? => do
  match stx with
  | `(answer($a:term)) =>
    if expectedType? == some (Expr.sort .zero) && a == (← `(term| sorry)) then
      return .const `True []
    else
      elabTerm (← `(by exact $a)) expectedType?
  | _ => Elab.throwUnsupportedSyntax
