import WeilConjectures.SixFunctors.Etale.Derived.Tensor

open Lean Elab Command

run_cmd do
  let env ← getEnv
  for n in [
    `CategoryTheory.MonoidalCategory.curriedTensor,
    `CategoryTheory.Functor.uncurry,
    `CategoryTheory.Functor.whiskeringRight,
    `CategoryTheory.DerivedMonoidal,
    `CategoryTheory.toDerivedMonoidal,
    `HomotopyCategory.quasiIso,
    `DerivedCategory.Qh,
    `CategoryTheory.Functor.comp,
    `CategoryTheory.Functor.mk,
    `CategoryTheory.Functor.category,
    `CategoryTheory.Functor.obj,
    `CategoryTheory.Functor.map,
    `CategoryTheory.CategoryStruct.comp,
    `CategoryTheory.NatTrans.app,
    `CategoryTheory.MonoidalCategoryStruct.tensorObj,
    `CategoryTheory.MonoidalCategoryStruct.whiskerLeft,
    `CategoryTheory.MonoidalCategoryStruct.whiskerRight,
    `CategoryTheory.instCategoryDerivedMonoidal,
    `DerivedCategory.instIsLocalizationHomotopyCategoryIntUpQhQuasiIso,
    `CategoryTheory.MorphismProperty.IsMultiplicative.toContainsIdentities,
    `HomotopyCategory.MonoidalCategory.instMonoidalCategory,
    `instMonoidalCategoryHomotopyCategoryIntUp_weilConjectures
  ] do
    match env.find? n with
    | some (.defnInfo v) =>
      let hint := match v.hints with
        | .opaque => "opaque"
        | .abbrev => "abbrev"
        | .regular h => s!"regular({h})"
      logInfo m!"[HINT] {n} kind=def hints={hint}"
    | some (.thmInfo _) => logInfo m!"[HINT] {n} kind=theorem"
    | some (.axiomInfo _) => logInfo m!"[HINT] {n} kind=axiom"
    | some (.opaqueInfo _) => logInfo m!"[HINT] {n} kind=opaque"
    | some (.ctorInfo _) => logInfo m!"[HINT] {n} kind=constructor"
    | some (.recInfo _) => logInfo m!"[HINT] {n} kind=recursor"
    | some (.quotInfo _) => logInfo m!"[HINT] {n} kind=quotient"
    | some (.inductInfo _) => logInfo m!"[HINT] {n} kind=inductive"
    | none => logInfo m!"[HINT] {n} missing"
