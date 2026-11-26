import WeilConjectures.SixFunctors.Etale.Derived.Tensor
open Lean Elab Command Meta CategoryTheory
set_option pp.universes true
set_option pp.all true
run_cmd do
  let env ← getEnv
  for n in [`CategoryTheory.ShrinkHoms.instCategory, `CategoryTheory.ShrinkHoms.instCategory._proof_1,
    `CategoryTheory.DerivedMonoidal, `CategoryTheory.instCategoryDerivedMonoidal,
    `DerivedCategory, `DerivedCategory.Qh, `CategoryTheory.HomologicalComplexUpToQuasiIso.Qh] do
    match env.find? n with
    | some info =>
      logInfo m!"[DECL] {n} type={info.type}"
    | none => logInfo m!"[DECL] {n} missing"
