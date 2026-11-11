/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.ModuleCohomologyExtResolutionNaturality


public import WeilConjectures.AlgebraicGeometry.ModuleCohomologyExtResolutionNaturalityExtension
meta import Lean

/-! # The Ext-to-abelian-sections part of the comparison

Source: Stacks Project, Tags 015E and 03FD.
(blueprint: new-module-cohomology-ext-sections-factorization)
-/

private meta def ps043ExprDiff (fuel : Nat) (path : String)
    (a b : Lean.Expr) : Lean.MetaM Unit := do
  let a := a.consumeMData
  let b := b.consumeMData
  if a == b then return
  match fuel with
  | 0 => Lean.logInfo m!"PS043 DIFF {path}:\nactual: {a}\nexpected: {b}"
  | n + 1 =>
    if a.isApp && b.isApp &&
        (a.getAppFn == b.getAppFn ||
          (a.getAppFn.isConst && b.getAppFn.isConst &&
            a.getAppFn.constName! == b.getAppFn.constName!)) &&
        a.getAppArgs.size == b.getAppArgs.size then
      for i in [:a.getAppArgs.size] do
        ps043ExprDiff n s!"{path}.{i}" a.getAppArgs[i]! b.getAppArgs[i]!
    else
      Lean.logInfo m!"PS043 DIFF {path}:\nactual: {a}\nexpected: {b}"

@[expose] public section
universe u
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
noncomputable section
namespace AlgebraicGeometry.Scheme.Modules.ExtEdgeResolution

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem sectionsComparisonNatIso_apply
    {A E : Type*} [Category A] [Category E]
    {R : Type u} [Ring R] {K : A ⥤ ModuleCat.{u} R} {T : A ⥤ E}
    {B L Q : E ⥤ AddCommGrpCat.{u}}
    (a : K ⋙ forget₂ _ AddCommGrpCat.{u} ≅ T ⋙ B)
    (b : L ≅ B) (c : L ≅ Q) (F : A) (x : K.obj F) :
    moduleComparisonEquiv (sectionsComparisonNatIso a b c) F x =
      (c.hom.app (T.obj F)) ((b.inv.app (T.obj F)) ((a.hom.app F) x)) := by
  rfl

private theorem moduleComparisonEquiv_siteSections
    {A : Type*} [Category A] {C : Type u} [SmallCategory C]
    (J : GrothendieckTopology C) [HasSheafify J AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf J AddCommGrpCat.{u})]
    {R : Type u} [Ring R] {K : A ⥤ ModuleCat.{u} R}
    {T : A ⥤ Sheaf J AddCommGrpCat.{u}} (U : C) (p : ℕ)
    (e : (presheafToSheaf J AddCommGrpCat.{u}).obj
      (yoneda.obj U ⋙ AddCommGrpCat.free) ≅
        (constantSheaf J AddCommGrpCat.{u}).obj (AddCommGrpCat.of (ULift.{u} ℤ)))
    (a : K ⋙ forget₂ _ AddCommGrpCat.{u} ≅ T ⋙
      (sheafToPresheaf J AddCommGrpCat.{u} ⋙
        (evaluation Cᵒᵖ AddCommGrpCat.{u}).obj (op U)).rightDerived p)
    (η : K ⋙ forget₂ _ AddCommGrpCat.{u} ≅ T ⋙ Sheaf.functorH J p)
    (hη : η = a ≪≫ Functor.isoWhiskerLeft T
      ((siteSectionsNatIso J U p).symm ≪≫ siteExtNatIso J U p ≪≫
        extSourceNatIso e p ≪≫ siteHNatIso J p)) (F : A) (x : K.obj F) :
    moduleComparisonEquiv η F x =
      (Abelian.Ext.precompAddEquiv e (T.obj F) p).symm
        ((siteSectionsObjIso J U (T.obj F) p).inv ((a.app F).hom x)) := by
  run_tac do Lean.logInfo m!"PS043 helper start: {← IO.monoMsNow}"
  subst η
  have h := sectionsComparisonNatIso_apply a (siteSectionsNatIso J U p)
    (siteExtNatIso J U p ≪≫ extSourceNatIso e p ≪≫ siteHNatIso J p) F x
  run_tac Lean.Elab.Tactic.withMainContext do
    let expected ← Lean.Meta.zetaReduce (← Lean.Elab.Tactic.getMainTarget)
    let actual ← Lean.Meta.zetaReduce
      (← Lean.Meta.inferType (.fvar (← Lean.Elab.Tactic.getFVarId (Lean.mkIdent `h))))
    ps043ExprDiff 12 "type" actual expected
  simpa only [sectionsComparisonNatIso, siteExtNatIso, siteHNatIso,
    Iso.refl_trans, Iso.trans_refl, extSourceNatIso, siteSectionsObjIso] using h
  run_tac do Lean.logInfo m!"PS043 helper end: {← IO.monoMsNow}"

set_option maxHeartbeats 800000 in
-- Elaborating the specialized derived-functor types needs additional instance conversions.
/-- The fixed module-to-Ext comparison factors through abelian derived sections.
Source: Stacks Project, Tags 015E and 03FD; the Ext-to-sections half of the defining
composite in ModuleCohomologyExtResolutionNaturality.
(blueprint: new-module-cohomology-ext-sections-factorization)

Proof: Unfold the fixed comparison and its natural isomorphism. Its constructor
composes the common-resolution section comparison, the inverse site-section
comparison, and the terminal Ext-source comparison. First evaluate this three-map
composite for arbitrary functors, before specializing to the scheme. Apply that
component formula and unfold the definition of module cohomology and the Ext-valued
cohomology type. The inverse site component is siteSectionsObjIso.inv, and the
terminal component is precompAddEquiv.symm. Their composite gives the asserted
formula. This never unfolds the acyclic-resolution comparison inside the first
factor, and includes degree zero, zero coefficients and empty schemes. -/
theorem ext_sections_factorization
    (X : Scheme.{u}) (F : SheafOfModules.{u} (moduleRings X.toRingedSpace)) (p : ℕ)
    (x : (RingedSpace.moduleCohomology X.toRingedSpace p).obj F) :
    moduleCohomologyExtResolutionEquiv X F p x = (by
      letI : EnoughInjectives (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
        (RingedSpace.moduleSheaves_abelian_enoughInjectives X.toRingedSpace).2
      let T := SheafOfModules.toSheaf (moduleRings X.toRingedSpace)
      let Γ := sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} ⋙
        (evaluation X.Opensᵒᵖ AddCommGrpCat.{u}).obj (op ⊤)
      let G := RingedSpace.globalSectionsFunctor X.toRingedSpace
      let V := forget₂ (ModuleCat.{u}
        ((moduleRings X.toRingedSpace).obj.obj (op ⊤))) AddCommGrpCat.{u}
      let d := siteSectionsObjIso (Opens.grothendieckTopology X) ⊤ (T.obj F) p
      exact (Abelian.Ext.precompAddEquiv (terminalSourceIso X) (T.obj F) p).symm
        (d.inv (((resolutionSectionsNatIso G V T Γ p (sectionHomologyIso X p)
          (fun M _ ↦ forgottenInjectiveAcyclic X M)).app F).hom x))) := by
  run_tac do Lean.logInfo m!"PS043 main start: {← IO.monoMsNow}"
  let : EnoughInjectives (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
    (RingedSpace.moduleSheaves_abelian_enoughInjectives X.toRingedSpace).2
  let T := SheafOfModules.toSheaf (moduleRings X.toRingedSpace)
  let Γ := sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} ⋙
    (evaluation X.Opensᵒᵖ AddCommGrpCat.{u}).obj (op ⊤)
  let G := RingedSpace.globalSectionsFunctor X.toRingedSpace
  let V := forget₂ (ModuleCat.{u}
    ((moduleRings X.toRingedSpace).obj.obj (op ⊤))) AddCommGrpCat.{u}
  -- Compare natural isomorphisms before evaluating their components.
  unfold moduleCohomologyExtResolutionEquiv
  let a := resolutionSectionsNatIso G V T Γ p (sectionHomologyIso X p)
    (fun M _ ↦ forgottenInjectiveAcyclic X M)
  run_tac do Lean.logInfo m!"PS043 comparison defined: {← IO.monoMsNow}"
  have hη : moduleCohomologyExtResolutionNatIso X p = a ≪≫ Functor.isoWhiskerLeft T
      ((siteSectionsNatIso (Opens.grothendieckTopology X) ⊤ p).symm ≪≫
        siteExtNatIso (Opens.grothendieckTopology X) ⊤ p ≪≫
          extSourceNatIso (terminalSourceIso X) p ≪≫
            siteHNatIso (Opens.grothendieckTopology X) p) := by
    unfold moduleCohomologyExtResolutionNatIso
    rfl
  run_tac do Lean.logInfo m!"PS043 iso equality proved: {← IO.monoMsNow}"
  have h := moduleComparisonEquiv_siteSections (Opens.grothendieckTopology X)
    (K := RingedSpace.moduleCohomology X.toRingedSpace p)
    ⊤ p (terminalSourceIso X) a (moduleCohomologyExtResolutionNatIso X p) hη F x
  run_tac do Lean.logInfo m!"PS043 helper applied: {← IO.monoMsNow}"
  run_tac Lean.Elab.Tactic.withMainContext do
    let expected ← Lean.Meta.zetaReduce (← Lean.Elab.Tactic.getMainTarget)
    let actual ← Lean.Meta.zetaReduce
      (← Lean.Meta.inferType (.fvar (← Lean.Elab.Tactic.getFVarId (Lean.mkIdent `h))))
    ps043ExprDiff 12 "type" actual expected
  dsimp only [id, AlgebraicGeometry.Scheme.Modules.H, Sheaf.functorH] at h ⊢
  exact h
  run_tac do Lean.logInfo m!"PS043 main end: {← IO.monoMsNow}"

end AlgebraicGeometry.Scheme.Modules.ExtEdgeResolution
