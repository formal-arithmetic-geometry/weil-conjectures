/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E7
-/
module

public import Sheaf.Paper.SmoothPurityTowerShriekData
import all Sheaf.Paper.GeometricOrdinaryRealization
import all Sheaf.Paper.GeometricOperationsBaseExistence
import all Sheaf.Paper.SemilinearDerivedSections
import Sheaf.AlgebraicGeometry.ProEtaleToposFunctorialityInverseImage
import Sheaf.Paper.GeometricOperationsTransitionExistence
import Sheaf.Paper.SmoothPurityStrictBaseCoordinates
import Sheaf.Paper.TowerClassFiniteSectionInverseImages

/-! # Geometry with the actual direct-image section coordinates -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite WeilConjectures
attribute [local irreducible] SemilinearSections.systemRing
  SemilinearSections.ringPresheaf SemilinearSections.rings
  AlgebraicGeometry.Scheme.proEtaleRingModulePullback
  AlgebraicGeometry.Scheme.proEtaleRingModuleAdjunction
  AlgebraicGeometry.Scheme.proEtaleRingDirectImageMap
  AlgebraicGeometry.Scheme.proEtaleConstantRingComparison
  CategoryTheory.constantSheaf Padic Padic.coefficientExtensionIntegers

namespace AlgebraicGeometry.ProEtale.SpTowerClasses
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

open SemilinearSections

private theorem whisker_transport
    {A D K : Type*} [Category A] [Category D] [Category K]
    {F : A ⥤ D} {L L' : D ⥤ K} (h : L = L')
    {H : A ⥤ K} (e : H ≅ F ⋙ L) :
    HEq (e ≪≫ Functor.isoWhiskerLeft F (eqToIso h)) e := by
  cases h
  simp


private theorem exact_derived_congr
    {A D : Type*} [Category A] [Category D] [Abelian A] [Abelian D]
    [HasDerivedCategory A] [HasDerivedCategory D]
    {L L' : A ⥤ D} [L.Additive] [L'.Additive]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    [PreservesFiniteLimits L'] [PreservesFiniteColimits L'] (h : L = L') :
    L.mapDerivedCategory = L'.mapDerivedCategory := by
  subst L'
  rfl

private theorem unit_from_transpose
    {A D A' D' : Type*} [Category A] [Category D] [Category A'] [Category D']
    (L : A ⥤ D) (R : D ⥤ A) (a : L ⊣ R) (U : A ⥤ A') (W : D ⥤ D')
    (i : A' ⥤ D') (p : D' ⥤ A') (adj : i ⊣ p)
    (eL : L ⋙ W ≅ U ⋙ i) (eR : R ⋙ U ≅ W ⋙ p)
    (ht : ∀ M N (h : L.obj M ⟶ N),
      U.map (a.homEquiv M N h) ≫ eR.hom.app N =
        adj.homEquiv _ _ (eL.inv.app M ≫ W.map h)) (M : A) :
    U.map (a.unit.app M) ≫ eR.hom.app (L.obj M) ≫ p.map (eL.hom.app M) =
      adj.unit.app (U.obj M) := by
  erw [← a.homEquiv_id M, ← Category.assoc, ht M (L.obj M) (𝟙 _)]
  erw [CategoryTheory.Functor.map_id, Category.comp_id (eL.inv.app M)]
  erw [Adjunction.homEquiv_unit, Category.assoc, ← p.map_comp,
    eL.inv_hom_id_app M, CategoryTheory.Functor.map_id,
    Category.comp_id (adj.unit.app (U.obj M))]

set_option maxHeartbeats 1000000 in
-- The geometry records require many dependent category and instance checks.
/-- Choose geometry before constructing any coefficient-unit comparison.
Source: Stacks 03D2, 03D7; Zheng Construction 4.1 and Lemma 4.10; blueprint
`sk-lem-sp-tower-bound-operations.proof.md`, clause (2).
(blueprint: lem-sfb-tower-class-section-geometry-existence).

Proof: take the ramification and strict sequence-site realization of
strictBaseCoordinates. At each scheme select the semilinear system
calculus. On the actual constant quotient rings transport the canonical algebraic
inverse image through proEtaleConstantRingComparison. Its coefficient squares
commute by naturality of the constant-section maps. Use ordinaryInverseSystem_exists
on these inverse images. For the right adjoints use proEtaleConstantRingPushforward
with proEtaleConstantRingAdjunction, and use the identity on their underlying
section sheaves. The normalized tensor-insertion formula of that adjunction
identifies its underlying transpose with the set adjunction, as required by
ordinaryDirectSystem_exists. Assemble the ordinary system Hom equivalence and
adjunction. Keep its actual level functors, adjunctions and identity underlying
comparisons when constructing GeometryOrdinary. Apply semilinearGeometryEvaluation
and semilinearGeometryTensor to these fixed ordinary data and the two selected
calculi. Derive the ordinary adjunctions canonically; their unit and counit
identities and ordinaryPullTransition give the transition and projection formulas.
Transport the resulting generic Geometry to the constant quotient presentation,
retaining the bundled level adjunctions and all evaluation comparisons. This
produces SpTowerShriek.Geometry with the stated identity on sections. No unit
isomorphism or compatibility of unit maps is asserted. All constructions apply
also to empty schemes and the positive coefficient level indexed by zero. -/
theorem exists_sectionGeometry {X Y : Scheme.{u}} (f : X ⟶ Y) :
    ∃ b : SpTowerShriek.Base l E, ∃ g : SpTowerShriek.Geometry l E b f,
      ∀ (n : ℕ)
        (N : SemilinearSections.Mod.{u + 1, u, u + 1} (Scheme.ProEt.topology X)
          (g.generic.coefficients n)) (U : Y.ProEtᵒᵖ)
        (x : ((SemilinearSections.underlying.{u + 1, u, u + 1}
          (Scheme.ProEt.topology Y) (SpTowerShriek.B l E Y n)).obj
            ((g.generic.levelPush n).obj N)).obj.obj U),
        HEq (((g.generic.levelPushUnderlying n).hom.app N).hom.app U x) x := by
  classical
  obtain ⟨b, _⟩ := SpTowerShriek.strictBaseCoordinates l E
  obtain ⟨I, a, hmodules, hpackage, hI, ha⟩ :=
    finite_sectionInverseImages l E f
  let J := Scheme.ProEt.topology Y
  let J' := Scheme.ProEt.topology X
  let B := SpTowerShriek.B l E Y
  let τ := SpTowerShriek.tau l E Y
  let F := SpTowerShriek.B l E X
  let σ := SpTowerShriek.tau l E X
  let uInv := Scheme.proEtaleSheafInverseImage f (Type (u + 1))
  let uPush := Scheme.proEtaleSheafDirectImage f (Type (u + 1))
  let adjSet := Scheme.proEtaleSheafAdjunction f (Type (u + 1))
  let V := fun n ↦ Scheme.proEtaleConstantRingPushforward (SpTowerShriek.R l E n) f
  let : PreservesFiniteLimits uInv :=
    (AlgebraicGeometry.ProEtale.toposFunctorialityInverseImage f (𝟙 Y)).2.2.2.1
  let eV (n : ℕ) : V n ⋙ underlying.{u + 1, u, u + 1} J (B n) ≅
      underlying.{u + 1, u, u + 1} J' (F n) ⋙ uPush :=
    NatIso.ofComponents (fun _ ↦ Iso.refl _) (by intros; rfl)
  have ha' n (M : SemilinearSections.Mod.{u + 1, u, u + 1} J (B n))
      (N : SemilinearSections.Mod.{u + 1, u, u + 1} J' (F n)) (h : (I n).modules.obj M ⟶ N) :
      (underlying.{u + 1, u, u + 1} J (B n)).map ((a n).homEquiv M N h) ≫
          (eV n).hom.app N =
        adjSet.homEquiv _ _ ((I n).moduleUnderlying.inv.app M ≫
          (underlying.{u + 1, u, u + 1} J' (F n)).map h) := by
    change (underlying.{u + 1, u, u + 1} J (B n)).map ((a n).homEquiv M N h) ≫ 𝟙 _ = _
    exact (Category.comp_id _).trans (ha n M N h)
  let (n : ℕ) : PreservesFiniteLimits (I n).modules :=
    algebraicInverse_limits.{u + 1, u, u + 1} J J' uInv (B n) (F n) (I n)
  let (n : ℕ) : PreservesColimits (I n).modules := (a n).leftAdjoint_preservesColimits
  let (n : ℕ) : (I n).modules.Additive :=
    Functor.additive_of_preserves_binary_products _
  let (n : ℕ) : (V n).Additive := (a n).right_adjoint_additive
  obtain ⟨P⟩ := ordinaryInverseSystem_exists.{u + 1, u, u + 1} J B τ J' uInv F σ I hI
  obtain ⟨D⟩ := ordinaryDirectSystem_exists.{u + 1, u, u + 1} J B τ J' uInv F σ I P V a
    hI uPush adjSet eV ha'
  let core : Adjunction.CoreHomEquiv P.pull D.push :=
    { homEquiv := D.homEquiv
      homEquiv_naturality_left_symm := by
        intro M M' N f g
        apply (D.homEquiv M N).injective
        rw [Equiv.apply_symm_apply,
          system_transpose_natural_left.{u + 1, u, u + 1} J B τ J' uInv P a D,
          Equiv.apply_symm_apply]
      homEquiv_naturality_right :=
        system_transpose_natural_right.{u + 1, u, u + 1} J B τ J' uInv P a D _ }
  let aSys := Adjunction.mkOfHomEquiv core
  let : PreservesColimits P.pull := aSys.leftAdjoint_preservesColimits
  let : P.pull.Additive := Functor.additive_of_preserves_binary_products _
  let : D.push.Additive := aSys.right_adjoint_additive
  have hunit n (M : SemilinearSections.Mod.{u + 1, u, u + 1} J (B n)) :
      (underlying.{u + 1, u, u + 1} J (B n)).map ((a n).unit.app M) ≫
          (eV n).hom.app ((I n).modules.obj M) ≫
          uPush.map ((I n).moduleUnderlying.hom.app M) =
        adjSet.unit.app ((underlying.{u + 1, u, u + 1} J (B n)).obj M) := by
    exact unit_from_transpose (I n).modules (V n) (a n)
      (underlying.{u + 1, u, u + 1} J (B n))
      (underlying.{u + 1, u, u + 1} J' (F n))
      uInv uPush adjSet (I n).moduleUnderlying (eV n) (ha' n) M
  have hsunit n (M : Systems.{u + 1, u, u + 1} J B τ) :
      (evaluation.{u + 1, u, u + 1} J B τ n).map (aSys.unit.app M) ≫
          (D.component n).hom.app (P.pull.obj M) ≫
          (V n).map ((P.component n).hom.app M) =
        (a n).unit.app ((evaluation.{u + 1, u, u + 1} J B τ n).obj M) := by
    rw [← aSys.homEquiv_id M]
    dsimp only [aSys]
    rw [Adjunction.mkOfHomEquiv_homEquiv]
    change (evaluation.{u + 1, u, u + 1} J B τ n).map
      (D.homEquiv M (P.pull.obj M) (𝟙 _)) ≫ _ ≫ _ = _
    rw [← Category.assoc, D.homEquiv_component, ← (a n).homEquiv_naturality_right]
    simpa using (a n).homEquiv_id ((evaluation.{u + 1, u, u + 1} J B τ n).obj M)
  let O : GeometryOrdinary.{u + 1, u, u + 1} J B τ J' uInv uPush adjSet :=
    { coefficients := F
      coefficientTransition := σ
      inverseImage := I
      coefficient_compatibility := hI
      levelPush := V
      levelAdjunction := a
      levelPushUnderlying := eV
      level_unit_underlying := hunit
      pull := P.pull
      ordinaryPullEvaluation := P.component
      push := D.push
      ordinaryAdjunction := aSys
      ordinaryPullEvaluation_sections := P.component_sections
      ordinaryPushEvaluation := D.component
      ordinaryPushEvaluation_sections := D.component_sections
      ordinary_unit_evaluation := hsunit
      restrictionPullback := P.restriction
      restrictionPullback_underlying := P.restriction_underlying
      ordinaryPullTransition := P.transition }
  let systems := b.calculus Y
  let target := b.calculus X
  let : ∀ n, Abelian.HasKInjectiveResolutions
      (SemilinearSections.Mod.{u + 1, u, u + 1} J' (O.coefficients n)) := fun n ↦ inferInstance
  let : Abelian.HasKInjectiveResolutions
      (Systems.{u + 1, u, u + 1} J' O.coefficients O.coefficientTransition) :=
    b.kinjective X
  obtain ⟨evData⟩ := semilinearGeometryEvaluation.{u + 1, u, u + 1}
    J B τ J' uInv uPush adjSet systems O target
  obtain ⟨T⟩ := semilinearGeometryTensor.{u + 1, u, u + 1}
    J B τ J' uInv uPush adjSet systems O target
  let G : SemilinearSections.Geometry.{u + 1, u, u + 1}
      J B τ systems J' uInv uPush adjSet := {
    toGeometryBase := GeometryOrdinary.toBase.{u + 1, u, u + 1} J B τ J' uInv uPush adjSet O target
    derivedLevelAdjunction := fun n ↦
      (O.levelAdjunction n).mapDerivedCategoryRightDerivedAdjunction
    derivedLevelAdjunction_canonical := fun _ ↦ rfl
    derivedAdjunction_canonical := rfl
    pullEvaluation := geometryPullEvaluation.{u + 1, u, u + 1} J B τ J' uInv uPush adjSet O
    pushEvaluation := evData.pushEvaluation
    unit_evaluation := evData.unit_evaluation
    counit_evaluation := evData.counit_evaluation
    coefficientPullback := evData.coefficientPullback
    tensorPullback := T.tensorPullback
    levelTensorPullback := T.levelTensorPullback
    tensorPullback_evaluation := T.tensorPullback_evaluation
    ordinaryPullEvaluation_sections := O.ordinaryPullEvaluation_sections
    ordinaryPushEvaluation := O.ordinaryPushEvaluation
    ordinaryPushEvaluation_sections := O.ordinaryPushEvaluation_sections
    ordinary_unit_evaluation := O.ordinary_unit_evaluation
    derivedLevel_transpose_model := fun n P I _ f ↦
      CategoryTheory.Adjunction.canonical_transpose (O.levelAdjunction n) P I f
    derived_transpose_model := fun P I _ f ↦
      CategoryTheory.Adjunction.canonical_transpose O.ordinaryAdjunction P I f
    pullEvaluation_model := fun _ ↦ rfl
    restrictionPullback := O.restrictionPullback
    restrictionPullback_underlying := O.restrictionPullback_underlying
    ordinaryPullTransition := O.ordinaryPullTransition
    coefficientPullback_transpose := evData.coefficientPullback_transpose
    levelTensorModel := T.levelTensorModel
    levelTensor_pure := T.levelTensor_pure
    tensorModel := T.tensorModel
    tensor_ordinary_evaluation := T.tensor_ordinary_evaluation }
  have hpull : G.PullTransitionFormula J B τ systems J' uInv uPush adjSet :=
    semilinearGeometryTransitionExistence J B τ systems J' uInv uPush adjSet G
  let g : SpTowerShriek.Geometry l E b f := {
    generic := G
    transitionFormula := push_transition_of_pull J B τ systems J' uInv uPush adjSet G hpull
    pullTransitionFormula := hpull
    projectionEvaluation := projection_evaluation J B τ systems J' uInv uPush adjSet G
    coefficients := rfl
    transitions := HEq.rfl
    target := HEq.rfl
    pull := O.pull
    push := O.push
    pull_eq := HEq.rfl
    push_eq := HEq.rfl
    ordinaryAdjunction := O.ordinaryAdjunction
    ordinaryAdjunction_eq := HEq.rfl
    derivedAdjunction_eq := HEq.rfl
    ordinaryPullEvaluation := fun n ↦ O.ordinaryPullEvaluation n ≪≫
      Functor.isoWhiskerLeft _ (eqToIso (hmodules n))
    ordinaryPullEvaluation_eq := fun n ↦
      whisker_transport (hmodules n) (O.ordinaryPullEvaluation n)
    pullEvaluation := fun n ↦ G.pullEvaluation n ≪≫
      Functor.isoWhiskerLeft _ (eqToIso (exact_derived_congr (hmodules n)))
    pullEvaluation_eq := fun n ↦
      whisker_transport (exact_derived_congr (hmodules n))
        (G.pullEvaluation n)
    ordinaryPushEvaluation := O.ordinaryPushEvaluation
    ordinaryPushEvaluation_eq := fun _ ↦ HEq.rfl
    levelAdjunction_eq := fun n ↦ heq_of_eq (hpackage n)
    pushEvaluation := G.pushEvaluation
    pushEvaluation_eq := fun _ ↦ HEq.rfl
    tensorPullback := G.tensorPullback
    tensorPullback_eq := HEq.rfl }
  exact ⟨b, g, fun _ _ _ _ ↦ HEq.rfl⟩


end AlgebraicGeometry.ProEtale.SpTowerClasses
