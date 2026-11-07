/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.OrdinaryLineScalar.OrdinaryLineScalarData
import all WeilConjectures.Algebra.Homology.ScalarHomOrdinary.ScalarHomOrdinaryTensorComparisonSupplement
import all WeilConjectures.Algebra.Homology.Signed.SignedLineScalarTensorTower
import all WeilConjectures.Algebra.Homology.LineUnbounded.LineUnboundedDerivedTensor

set_option linter.privateModule false

/-! # Ordinary signed-line tensor and derived scalar extension

Source: Stacks Project, Tags 07A4, 0G7E and 0D6D; blueprint main-20261015,
Tate-twist local freeness, proof (3).
(blueprint: lem-pur-ordinary-line-scalar-line-data)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
set_option genInjectivity false
set_option genSizeOf false
set_option genCtorIdx false

set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe t a w u v b r ua va
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite AlgebraicGeometry
-- Prefer the native additive structures over routes through abelian instances.
attribute [local instance 30000] SheafOfModules.instPreadditive
  HomologicalComplex.instPreadditive CategoryTheory.functorCategoryPreadditive
  CategoryTheory.Preadditive.preadditiveHasZeroMorphisms
  CategoryTheory.Functor.preservesZeroMorphisms_of_additive
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology
namespace SheafOfModules.OrdinaryLineScalar

variable (X : Scheme.{t}) [EssentiallySmall.{max a (t + 1)} X.ProEt]

variable {X}
  [∀ R : Sheaf (Scheme.ProEt.topology X) CommRingCat.{max a (t + 1)},
    HasDerivedCategory.{w} (Modules.{t, a} X R)]
local notation "𝒬[" R "]" => (DerivedCategory.Q (C := Modules X R))
attribute [local instance] modulesCategory modulesAbelian monoidalCategory
attribute [local implicit_reducible] monoidalCategory
attribute [local irreducible] LineUnbounded.derived LineUnbounded.normalization
  KFlatFixedTensor.representativeIso compute signedLinePower scalarTensorPower
  LineUnbounded.localizedCancellation LineUnbounded.cancellation
  LineUnbounded.pureTensor ScalarHomOrdinary.pure

set_option backward.isDefEq.respectTransparency.types false

section LineConstruction

set_option backward.isDefEq.respectTransparency.types true

attribute [local irreducible] monoidalCategory
  tensorObjIsoSheafification PresheafOfModules.sheafificationAdjunction

private theorem tensor_kflat_generic
    {A : Type ua} [Category.{va} A] [Abelian A] [MonoidalCategory A] [MonoidalPreadditive A]
    [HasColimitsOfSize.{0, 0} A]
    [∀ M : A, PreservesColimitsOfSize.{0, 0} (tensorLeft M)]
    [∀ M : A, PreservesColimitsOfSize.{0, 0} (tensorRight M)]
    (M : A) [PreservesFiniteLimits (tensorRight M)]
    [PreservesFiniteColimits (tensorRight M)] (P : CochainComplex A ℤ)
    (hP : ∀ F : CochainComplex A ℤ, F.Acyclic →
      (CochainComplex.mapBifunctor F P (curriedTensor A)).Acyclic) :
    ∀ F : CochainComplex A ℤ, F.Acyclic →
      (CochainComplex.mapBifunctor F
        (((tensorRight M).mapHomologicalComplex (.up ℤ)).obj P) (curriedTensor A)).Acyclic := by
  intro F hF i
  have : ∀ (K K' : CochainComplex A ℤ), HomologicalComplex.HasTensor K K' :=
    fun K K' ↦ inferInstance
  have h : (((tensorRight M).mapHomologicalComplex (.up ℤ)).obj
      (CochainComplex.mapBifunctor F P (curriedTensor A))).ExactAt i :=
    (hP F hF i).map (tensorRight M)
  have c := CochainComplex.map₂HomologicalComplexFlipObjSingleIso (curriedTensor A) M
  have e := HomologicalComplex.associator F P ((CochainComplex.singleFunctor A 0).obj M) ≪≫
    (((curriedTensor A).map₂CochainComplex).obj F).mapIso (c.app P)
  exact HomologicalComplex.ExactAt.of_iso h
    ((c.app (CochainComplex.mapBifunctor F P (curriedTensor A))).symm ≪≫ e)

section PureTensorFormula

variable {C : Type u} [Category.{v} C] [EssentiallySmall.{r} C]
  {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{r}] [HasSheafify J AddCommGrpCat.{r}]

private theorem pure_formula (R : Sheaf J CommRingCat.{r})
    (M N : scalarModules J R) (U : Cᵒᵖ)
    (x : M.val.obj U) (y : N.val.obj U) :
    (tensorObjIsoSheafification M N).inv.val.app U
      (((PresheafOfModules.sheafificationAdjunction (𝟙 _)).unit.app
        (M.val ⊗ N.val)).app U (x ⊗ₜ[R.obj.obj U] y)) =
      ScalarHomOrdinary.pure R M N U x y := by
  unfold ScalarHomOrdinary.pure
  rfl

end PureTensorFormula

omit [∀ R : Sheaf (Scheme.ProEt.topology X) CommRingCat.{max a (t + 1)},
  HasDerivedCategory.{w} (Modules.{t, a} X R)] in
private theorem pure_eq_ordinary
    {R : Sheaf (Scheme.ProEt.topology X) CommRingCat.{max a (t + 1)}}
    (M N : Modules.{t, a} X R) (U : X.ProEtᵒᵖ) (x : M.val.obj U) (y : N.val.obj U) :
    LineUnbounded.pureTensor.{t, a} X R M N U x y =
      ScalarHomOrdinary.pure.{t + 1, t, max a (t + 1)} R M N U x y := by
  unfold LineUnbounded.pureTensor
  have hcomputed := pure_formula R M N U x y
  -- Reuse the inferred proof; the kernel checks the displayed target.
  run_tac Lean.Elab.Tactic.withMainContext do
    let some hd := (← Lean.getLCtx).findFromUserName? `hcomputed
      | Lean.throwError "missing comparison proof"
    (← Lean.Elab.Tactic.getMainGoal).assign hd.toExpr
    Lean.Elab.Tactic.replaceMainGoal []

private def tensor_site
    {R : Sheaf (Scheme.ProEt.topology X) CommRingCat.{max a (t + 1)}}
    (M N : Modules.{t, a} X R) :=
  ScalarHomOrdinary.tensorIsoSite.{t + 1, t, max a (t + 1)} R M N

attribute [local irreducible] tensor_site

omit [∀ R : Sheaf (Scheme.ProEt.topology X) CommRingCat.{max a (t + 1)},
  HasDerivedCategory.{w} (Modules.{t, a} X R)] in
private theorem tensor_site_pure
    {R : Sheaf (Scheme.ProEt.topology X) CommRingCat.{max a (t + 1)}}
    (M N : Modules.{t, a} X R) (U : X.ProEtᵒᵖ) (x : M.val.obj U) (y : N.val.obj U) :
    (tensor_site.{t, a} M N).hom.val.app U (LineUnbounded.pureTensor.{t, a} X R M N U x y) =
      siteSheafTensorTmul (J := Scheme.ProEt.topology X) (A := R) M N U x y := by
  unfold tensor_site
  have hcomputed := (congrArg ((ScalarHomOrdinary.tensorIsoSite R M N).hom.val.app U)
    (pure_eq_ordinary M N U x y)).trans
      (ScalarHomOrdinary.tensorIsoSite_pure.{t + 1, t, max a (t + 1)} R M N U x y)
  -- Reuse the inferred proof; the kernel checks the displayed target.
  run_tac Lean.Elab.Tactic.withMainContext do
    let some hd := (← Lean.getLCtx).findFromUserName? `hcomputed
      | Lean.throwError "missing comparison proof"
    (← Lean.Elab.Tactic.getMainGoal).assign hd.toExpr
    Lean.Elab.Tactic.replaceMainGoal []

omit [∀ R : Sheaf (Scheme.ProEt.topology X) CommRingCat.{max a (t + 1)},
  HasDerivedCategory.{w} (Modules.{t, a} X R)] in
private theorem signed_power_rank
    {R : Sheaf (Scheme.ProEt.topology X) CommRingCat.{max a (t + 1)}}
    (L : Modules.{t, a} X R) [L.IsFiniteLocallyFreeOfRank 1] :
    ∀ m : ℤ, (power.{t, a} L m).IsFiniteLocallyFreeOfRank 1 := by
  obtain ⟨I, V, hV, h⟩ :=
    (isFiniteLocallyFreeOfRank_iff_exists_over_iso_free.{max a (t + 1), t, t + 1}
      (M := L) (r := 1)).mp
      inferInstance
  intro m
  apply (isInvertible_iff_isFiniteLocallyFreeOfRank_one.{max a (t + 1), t, t + 1} _).mp
  apply isInvertible_of_forall_over_unit.{max a (t + 1), t, t + 1} V hV
  intro i
  let q := (h i).some ≪≫ freeUniqueIso (ULift (Fin 1))
  obtain ⟨E, hE⟩ := signedBasis_on_chart.{t + 1, t, a} L (V i) q
  exact ⟨(basisChart.{t + 1, t, max a (t + 1)} (power.{t, a} L m)
    (op (V i)) (E m) (hE.1 m)).symm⟩

omit [∀ R : Sheaf (Scheme.ProEt.topology X) CommRingCat.{max a (t + 1)},
  HasDerivedCategory.{w} (Modules.{t, a} X R)] in
private theorem tensor_flat_model
    {R : Sheaf (Scheme.ProEt.topology X) CommRingCat.{max a (t + 1)}}
    (M : Modules.{t, a} X R)
    (hM : PreservesFiniteLimits (LineUnbounded.tensor.{t, a} X R M) ∧
      PreservesFiniteColimits (LineUnbounded.tensor.{t, a} X R M))
    (P : CochainComplex (Modules.{t, a} X R) ℤ) (hP : FlatModel.{t, a} P) :
    FlatModel.{t, a}
      (((LineUnbounded.tensor.{t, a} X R M).mapHomologicalComplex (.up ℤ)).obj P) := by
  change PreservesFiniteLimits (tensorRight M) ∧
    PreservesFiniteColimits (tensorRight M) at hM
  have := hM.1
  have := hM.2
  constructor
  · exact tensor_kflat_generic M P hP.1
  · intro i
    have ht : exactFunctor _ _ (tensorRight (P.X i)) :=
      (exactFunctor _ _).prop_of_iso (siteSheafTensorRightIso R (P.X i)) (hP.2 i)
    have : PreservesFiniteLimits (tensorRight (P.X i)) := ht.1
    have : PreservesFiniteColimits (tensorRight (P.X i)) := ht.2
    have : PreservesFiniteLimits (tensorRight (P.X i) ⋙ tensorRight M) :=
      comp_preservesFiniteLimits _ _
    have : PreservesFiniteColimits (tensorRight (P.X i) ⋙ tensorRight M) :=
      comp_preservesFiniteColimits _ _
    have : PreservesFiniteLimits (tensorRight (P.X i ⊗ M)) :=
      preservesFiniteLimits_of_natIso (tensorRightTensor (P.X i) M).symm
    have : PreservesFiniteColimits (tensorRight (P.X i ⊗ M)) :=
      preservesFiniteColimits_of_natIso (tensorRightTensor (P.X i) M).symm
    change IsFlatOnSite (J := Scheme.ProEt.topology X) (R := R) (P.X i ⊗ M)
    exact ⟨preservesFiniteLimits_of_natIso (siteSheafTensorRightIso R _).symm,
      preservesFiniteColimits_of_natIso (siteSheafTensorRightIso R _).symm⟩

section
attribute [local semireducible] monoidalCategory signedLinePower scalarTensorPower
omit [∀ R : Sheaf (Scheme.ProEt.topology X) CommRingCat.{max a (t + 1)},
  HasDerivedCategory.{w} (Modules.{t, a} X R)] in
private theorem power_zero
    {R : Sheaf (Scheme.ProEt.topology X) CommRingCat.{max a (t + 1)}}
    (L : Modules.{t, a} X R) : power.{t, a} L 0 = 𝟙_ (Modules.{t, a} X R) := rfl
omit [∀ R : Sheaf (Scheme.ProEt.topology X) CommRingCat.{max a (t + 1)},
  HasDerivedCategory.{w} (Modules.{t, a} X R)] in
private theorem power_zero_one
    {R : Sheaf (Scheme.ProEt.topology X) CommRingCat.{max a (t + 1)}}
    (L : Modules.{t, a} X R) (U : X.ProEtᵒᵖ) :
    (eqToHom (power_zero L)).val.app U (1 : R.obj.obj U) = (1 : R.obj.obj U) := rfl
end

attribute [local semireducible] monoidalCategory

end LineConstruction

end SheafOfModules.OrdinaryLineScalar
