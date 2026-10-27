/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F2
-/
module

public import Sheaf.Paper.SixFunctorOperationDatum
import Sheaf.Paper.ConstructibleExceptionalCompositorData
import Sheaf.Paper.CompactSupportNormalizedTowerLimit
import all Sheaf.Paper.CompactSupportRepresentativeIndependence

/-! # Normalized strict-tower comparison for the integral support action -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option Elab.async false
attribute [local irreducible] HasDerivedCategory.standard
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

private theorem unitProjection
    {A B : Type*} [Category A] [Category B] [Abelian A] [Abelian B]
    [HasDerivedCategory A] [HasDerivedCategory B] [Abelian.HasKInjectiveResolutions A]
    (F G : A ⥤ B) [F.Additive] [G.Additive]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] (τ : F ⟶ G)
    (π : F.rightDerivedFunctor ⟶ G.mapDerivedCategory)
    (hπ : ∀ (I : CochainComplex A ℤ) [I.IsKInjective],
      π.app (DerivedCategory.Q.obj I) ≫ G.mapDerivedCategoryFactors.hom.app I =
        (F.rightDerivedFunctorObjQIso I).hom ≫
          DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex τ (.up ℤ)).app I))
    (I : CochainComplex A ℤ) :
    (canonicalDerivedUnit F).app I ≫ π.app (DerivedCategory.Q.obj I) ≫
        G.mapDerivedCategoryFactors.hom.app I =
      DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex τ (.up ℤ)).app I) := by
  have := canonicalDerivedUnit_isDerived F
  let β := Functor.whiskerRight (NatTrans.mapHomologicalComplex τ (.up ℤ))
    DerivedCategory.Q ≫ G.mapDerivedCategoryFactors.inv
  let π' := F.rightDerivedFunctor.rightDerivedDesc (canonicalDerivedUnit F)
    (HomologicalComplex.quasiIso _ (.up ℤ)) G.mapDerivedCategory β
  have fac (J : CochainComplex A ℤ) :
      (canonicalDerivedUnit F).app J ≫ π'.app (DerivedCategory.Q.obj J) ≫
        G.mapDerivedCategoryFactors.hom.app J =
      DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex τ (.up ℤ)).app J) := by
    have h := F.rightDerivedFunctor.rightDerived_fac_app (canonicalDerivedUnit F)
      (HomologicalComplex.quasiIso _ (.up ℤ)) G.mapDerivedCategory β J
    change (canonicalDerivedUnit F).app J ≫ π'.app (DerivedCategory.Q.obj J) = _ at h
    rw [← Category.assoc, h]
    simp only [β, NatTrans.comp_app, Functor.whiskerRight_app, Category.assoc,
      Iso.inv_hom_id_app, Category.comp_id]
  have heq : π' = π := by
    apply NatTrans.ext
    funext K
    obtain ⟨J, hJ, ⟨e⟩⟩ := DerivedCategory.exists_iso_Q_obj_of_isKInjective K
    let := hJ
    have hq : π'.app (DerivedCategory.Q.obj J) = π.app (DerivedCategory.Q.obj J) := by
      have : IsIso ((canonicalDerivedUnit F).app J) := by
        dsimp [canonicalDerivedUnit]
        infer_instance
      apply (cancel_epi ((canonicalDerivedUnit F).app J)).1
      apply (cancel_mono (G.mapDerivedCategoryFactors.hom.app J)).1
      rw [Category.assoc, fac J, Category.assoc, hπ J, ← Category.assoc,
        canonicalDerivedUnit_objIso F J, Category.id_comp]
    apply (cancel_mono (G.mapDerivedCategory.map e.hom)).1
    rw [← π'.naturality, hq, π.naturality]
  rw [← heq]
  exact fac I

variable {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
  {E : Type u} [Field E] [Algebra (Padic C.l) E] [FiniteDimensional (Padic C.l) E]
  {n : ℕ} {hn : 1 ≤ n} (S : SixFunctorOperationDatum D C E n hn)

set_option maxHeartbeats 800000 in
-- Elaborating the designated tower's dependent choices requires additional heartbeats.
/-- The actual support action has a projection-normalized comparison with the
specified exact strict tower and its total limit, before applying it to triangles.
Source: current blueprint prop-functor-package.proof.md, clause (3), steps 2--3;
Stacks Tags 0940, 0941 and 08TC.
(blueprint: lem-sf-package-integral-support-tower-normalization).

Proof: take the strict tower designated by
lem-weil-compact-support-reduction-tower-functor and its K-injective total derived
inverse limit. Its evaluation isomorphisms retain every quotient transition.
Apply lem-sf-compact-support-total-limit-realization to this whole tower.
The normalized compact-support construction identifies its total limit with the
recorded integral support functor; use the construction's comparison on whole
strict towers, rather than trying to recover a tower map from its evaluations.
The defining Roos projection normalization makes this isomorphism preserve each
chosen compact-support projection. Naturality on derived morphisms follows from
the functorial K-injective realization. The designated tower is exact, and total
right-derived inverse limit is triangulated, with their normalized shift maps.
The claim concerns all constructible inputs and does not choose new cones. -/
theorem sfPackageIntegralSupportTowerNormalization
    {X Y : SixFunctorSpace D}
    [IsSeparated X.obj.hom] [IsSeparated Y.obj.hom]
    (f : X ⟶ Y)
    [IsSeparated f.hom.left] [LocallyOfFiniteType f.hom.left] [QuasiCompact f.hom.left]
    (hl : IsUnit (C.l : D.k)) (c : Compactification f.hom.left) :
    (fun [_products : HasCountableProducts
        (DerivedCategory (scalarReductionSource C.l E Y.obj.left))] ↦
      ∃ T : CompactSupportReductionTowerConstruction C.l E f.hom.left c,
      T.tower = Classical.choose (Classical.choose_spec (Classical.choose_spec
        (exists_compactSupportReductionTower C.l E D.k X.obj.left Y.obj.left
          f.hom.left hl c))).2.2 ∧
      ∃ (sT : T.tower.CommShift ℤ) (sL : T.limit.CommShift ℤ),
      (fun [_shiftT : T.tower.CommShift ℤ] ↦ T.tower.IsTriangulated) (_shiftT := sT) ∧
      (fun [_shiftL : T.limit.CommShift ℤ] ↦ T.limit.IsTriangulated) (_shiftL := sL) ∧
      ∃ e : S.higher.integral.support f c ⋙
          (sfIntegralConstructible C.l E Y.obj.left).ι ≅
          (sfIntegralConstructible C.l E X.obj.left).ι ⋙ (T.tower ⋙ T.limit),
        ∀ (K : sfIntegralConstructibleCategory C.l E X.obj.left) (m : ℕ),
          HEq (e.hom.app K ≫ (T.projections m).app (T.tower.obj K.obj) ≫
              (T.evaluations m).hom.app K.obj)
            (Classical.choose (Classical.choose_spec (exists_isDerivedLimit_and_iso
              (sfCompactSupportTerm C.l E c K.obj)
              (sfCompactSupportTransition C.l E c K.obj)).1) ≫
                Pi.π (sfCompactSupportTerm C.l E c K.obj) m))
      (_products := integralOperationsDerivedCountableProducts C.l E Y.obj.left) := by
  classical
  let := integralOperationsDerivedCountableProducts C.l E Y.obj.left
  let H := exists_compactSupportReductionTower C.l E D.k X.obj.left Y.obj.left
    f.hom.left hl c
  let sX := H.choose
  let sY := H.choose_spec.choose
  have h := H.choose_spec.choose_spec
  let := sX
  let := sY
  let T := h.2.2.choose
  have hT := h.2.2.choose_spec
  let ev := hT.2.choose_spec.2.choose
  let U := (lim : pbcTowers Y.obj.left
    (completedIntegralCommRingSheafUnrestricted C.l E Y.obj.left) ⥤
      scalarReductionSource C.l E Y.obj.left)
  let η := canonicalDerivedUnit U
  let L := coefficientConstantTowerLimit C.l E Y.obj.left
  have hL : L.IsRightDerivedFunctor η (HomologicalComplex.quasiIso _ (.up ℤ)) :=
    canonicalDerivedUnit_isDerived U
  let datum : CompactSupportReductionTowerConstruction C.l E f.hom.left c := {
    tower := T
    evaluations := ev
    transition_compatibility := hT.2.choose_spec.2.choose_spec
    sourceLinear := sX
    targetLinear := sY
    sourceScalarAction := h.1
    targetScalarAction := h.2.1
    towerLinear := hT.1
    towerShift := ⟨hT.2.choose, hT.2.choose_spec.1⟩
    limit := L
    limitUnit := η
    limit_isRightDerived := hL
    limit_isIso_on_KInjective := by
      intro I hI
      let := hI
      dsimp [η, canonicalDerivedUnit]
      infer_instance
    projections := coefficientConstantTowerProjection C.l E Y.obj.left
    projection_normalization := by
      intro m I
      exact unitProjection U
        ((evaluation ℕᵒᵖ (scalarReductionSource C.l E Y.obj.left)).obj (Opposite.op m))
        (lim.π (Opposite.op m)) (coefficientConstantTowerProjection C.l E Y.obj.left m)
        (coefficientConstantTowerProjection_exists C.l E Y.obj.left m).choose_spec.1 I }
  -- Identify the actual action before using the normalized whole-tower comparison.
  have hsupport : S.higher.integral.support f c =
      sfCompactSupportFiniteIntegralFunctor C.l D.k hl c E :=
    constructibleIntegralSupport_eq D C E ⟨n, lt_of_lt_of_le Nat.zero_lt_one hn⟩ S f c
  obtain ⟨e, he⟩ := compactSupportNormalizedTowerLimit C.l E D.k hl c T ev rfl HEq.rfl
  let sL : L.CommShift ℤ := by
    dsimp only [L, coefficientConstantTowerLimit]
    infer_instance
  have triL : (fun [_shift : L.CommShift ℤ] ↦ L.IsTriangulated) (_shift := sL) := by
    dsimp only [L, coefficientConstantTowerLimit, sL]
    infer_instance
  refine ⟨datum, rfl, hT.2.choose, sL, hT.2.choose_spec.1, triL, ?_⟩
  rw [hsupport]
  exact ⟨e, he⟩

end WeilConjectures
