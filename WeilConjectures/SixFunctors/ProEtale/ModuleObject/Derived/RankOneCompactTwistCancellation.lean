/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.RankOneDivisorClassIntegral
public import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicCoefficientTwistsUnrestricted
import WeilConjectures.AlgebraicGeometry.Integral.IntegralTateBasis
import WeilConjectures.AlgebraicGeometry.Native.NativeSignedLine
import WeilConjectures.SixFunctors.ProEtale.Adic.PadicIntModuleUpperStar
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FinitelyPresentedStalk
import WeilConjectures.CategoryTheory.Adjunction.ProjectionMapDualizable
import WeilConjectures.PoincareDuality.ProjectionFormula

/-! # Untwisting the rank-one compact-support object

Source: latest blueprint, `thm-pur-rank-one-thom`, statement and proof Steps 1--3
(blueprint: thm-pur-rank-one-thom).

The positive divisor class and its proper-section and compact-support comparisons
are the recorded canonical constructions of `RankOneDivisorClassIntegral`.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u

open CategoryTheory.MonoidalCategory
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite
open scoped CategoryTheory.Obj CategoryTheory.MonoidalCategory CategoryTheory.MonObj
open AlgebraicGeometry AlgebraicGeometry.ProEtale
open AlgebraicGeometry.ProEtale.CondensedRing

namespace AlgebraicGeometry.ProEtale.CondensedRing
open Admissible

private theorem pull_basis
    (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj R] [IsCommMonObj R]
    {X Y : Scheme.{u}} (f : Y ⟶ X)
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj R X))
    (e : ((AlgebraicGeometry.ProEtale.upperStar Ab.{u + 1} f).mapMod
      (condensedRingObj R X)).obj M ≅ 𝟙_ _) :
    Nonempty ((CondensedRing.upperStar R f).obj M ≅ 𝟙_ _) :=
  ⟨(Mod.extendScalars (condensedPullbackHom R f)).mapIso e ≪≫
    Mod.extendScalarsObjRegularIso (condensedPullbackHom R f)⟩

set_option maxHeartbeats 1600000 in
-- Module scalar-extension comparisons check several inverse-image tensor instances.
private theorem extend_local_basis
    (R S : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj R] [IsCommMonObj R] [MonObj S] [IsCommMonObj S]
    (φ : R ⟶ S) [IsMonHom φ]
    {X Y : Scheme.{u}} (f : Y ⟶ X)
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj R X))
    (e : (CondensedRing.upperStar R f).obj M ≅ 𝟙_ _) :
    Nonempty (((AlgebraicGeometry.ProEtale.upperStar Ab.{u + 1} f).mapMod
      (condensedRingObj S X)).obj
      ((Mod.extendScalars (coefficientMap φ X)).obj M) ≅ 𝟙_ _) := by
  let ei : (CondensedRing.upperStar S f).obj
      ((Mod.extendScalars (coefficientMap φ X)).obj M) ≅ 𝟙_ _ :=
    (CondensedRing.pullIso φ f).symm.app M ≪≫
      (Mod.extendScalars (coefficientMap φ Y)).mapIso e ≪≫
        Mod.extendScalarsObjRegularIso (coefficientMap φ Y)
  exact ⟨(comapUpperStarObjIso S f _).symm ≪≫
    (Mod.comap (condensedPullbackHom S f)).mapIso ei ≪≫
      (Mod.regularIsoComapRegular (condensedPullbackHom S f)).symm⟩

private theorem extend_cover_basis
    (R S : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj R] [IsCommMonObj R] [MonObj S] [IsCommMonObj S]
    (φ : R ⟶ S) [IsMonHom φ] (X : Scheme.{u})
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj R X))
    (hM : ∃ C : Scheme.Cover.{u} Scheme.proetalePrecoverage X, ∀ i : C.I₀,
      Nonempty (((AlgebraicGeometry.ProEtale.upperStar Ab.{u + 1} (C.f i)).mapMod
        (condensedRingObj R X)).obj M ≅ 𝟙_ _)) :
    ∃ C : Scheme.Cover.{u} Scheme.proetalePrecoverage X, ∀ i : C.I₀,
      Nonempty (((AlgebraicGeometry.ProEtale.upperStar Ab.{u + 1} (C.f i)).mapMod
        (condensedRingObj S X)).obj
        ((Mod.extendScalars (coefficientMap φ X)).obj M) ≅ 𝟙_ _) := by
  obtain ⟨C, hC⟩ := hM
  refine ⟨C, fun i ↦ ?_⟩
  obtain ⟨e⟩ := hC i
  obtain ⟨ei⟩ := pull_basis R (C.f i) M e
  exact extend_local_basis R S φ (C.f i) M ei

private theorem prime_global_isUnit
    (P : WeilConjectures.PurityFiniteSetting.{u})
    (X : Scheme.{u}) (a : X ⟶ Spec (CommRingCat.of P.field.k)) :
    IsUnit (P.coefficients.l : Γ(X, ⊤)) := by
  apply X.toRingedSpace.isUnit_of_isUnit_germ
  intro x hx
  change IsUnit ((X.presheaf.germ ⊤ x hx).hom (P.coefficients.l : Γ(X, ⊤)))
  rw [map_natCast]
  apply (isUnit_map_iff (IsLocalRing.residue (X.presheaf.stalk x)) _).mp
  simpa only [map_natCast] using prime_isUnit P X a x

private theorem line_locally_unit
    (P : WeilConjectures.PurityFiniteSetting.{u})
    (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]
    (hΛ : IsAdmissibleCoefficientFor P.coefficients Λ)
    (X : Scheme.{u}) (a : X ⟶ Spec (CommRingCat.of P.field.k)) :
    ∃ C : Scheme.Cover.{u} Scheme.proetalePrecoverage X, ∀ i : C.I₀,
      Nonempty (((AlgebraicGeometry.ProEtale.upperStar Ab.{u + 1} (C.f i)).mapMod
        (condensedRingObj Λ.X X)).obj
        (line P Λ hΛ X) ≅ 𝟙_ _) := by
  exact extend_cover_basis _ Λ.X (integralMap P Λ hΛ).hom X _
    (tateModule_locally_trivial X P.coefficients.l (prime_global_isUnit P X a))

/-- Projection formula and Tate evaluation cancel the positive shifted line inside Rπ!.

Source: latest blueprint thm-pur-rank-one-thom, final displayed formula and
projection-formula argument (blueprint: lem-pur-rank-one-compact-twist-cancellation).
Proof: the root-normalized Tate line is locally free of rank one; its internal
Hom into the coefficient unit is its negative signed twist. Both lines are flat
and their canonical evaluation is an isomorphism. Pullback commutes with this
line and its dual. The exact degree-zero embedding and the K-flat comparison
identify their derived tensor with their ordinary evaluation. The shift tensor
comparison cancels the shifts 2 and -2. Apply the projection formula separately
to extension by zero along the open part of c and proper direct image along its
proper part, with the perfect negative line as the base tensor factor. Their
composite identifies the displayed left side with Rπ! of the tensor of the
positive line shifted by 2 and the pulled-back negative line shifted by -2.
The evaluation and shift cancellation identify that tensor with the coefficient
unit on E, giving exactly the displayed right side. The construction applies to
every admissible coefficient and any compactification; no isomorphy of τ is used.
The argument also covers the empty base and the zero coefficient ring. -/
theorem rankOne_compact_twist_cancellation
    (P : WeilConjectures.PurityFiniteSetting.{u})
    {B : Scheme.{u}} (b : B ⟶ Spec (CommRingCat.of P.field.k))
    [IsSeparated b] [LocallyOfFiniteType b] [QuasiCompact b]
    (V : PurityVectorBundle P B b 1)
    (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]
    (hΛ : IsAdmissibleCoefficientFor P.coefficients Λ)
    (c : Compactification V.p) :
    let positiveImage := (rightDerivedLowerShriekOfCompactification Λ.X c).obj
      (((DerivedCategory.singleFunctor (Modules Λ V.E) 0).obj
        (line P Λ hΛ V.E)) ⟦(2 : ℤ)⟧)
    let negativeLine := (DerivedCategory.singleFunctor (Modules Λ B) 0).obj
      (coefficientSignedTwist B (condensedRingObj Λ.X B) (line P Λ hΛ B) (-1))
    let unitImage := (rightDerivedLowerShriekOfCompactification Λ.X c).obj
      ((DerivedCategory.singleFunctor (Modules Λ V.E) 0).obj (unit Λ V.E))
    Nonempty (positiveImage ⊗ negativeLine ⟦(-2 : ℤ)⟧ ≅ unitImage) := by
  classical
  let S := DerivedCategory.singleFunctor (Modules Λ B) 0
  let SE := DerivedCategory.singleFunctor (Modules Λ V.E) 0
  let L := line P Λ hΛ B
  let N := coefficientSignedTwist B (condensedRingObj Λ.X B) L (-1)
  let F := (CondensedRing.upperStar Λ.X V.p).leftDerivedFunctor
  let R := rightDerivedLowerShriekOfCompactification Λ.X c
  have hs := nativeSignedLine (condensedRingObj Λ.X B) L (line_locally_unit P Λ hΛ B b)
  have hL : IsLocallyFree (condensedRingObj Λ.X B) L :=
    (hs.2.1 1).of_iso (λ_ L)
  let eLN : L ⊗ N ≅ 𝟙_ (Modules Λ B) :=
    whiskerRightIso (λ_ L).symm N ≪≫ (hs.2.2.2.2 1).some
  let eD : S.obj L ⊗ S.obj N ≅ 𝟙_ (DerivedCategory (Modules Λ B)) :=
    hL.singleFunctorTensorObjIso N 0 ≪≫ S.mapIso eLN ≪≫
      DerivedCategory.singleFunctorObjUnitIso (Modules Λ B)
  let eShift : (S.obj L) ⟦(2 : ℤ)⟧ ⊗ (S.obj N) ⟦(-2 : ℤ)⟧ ≅
      𝟙_ (DerivedCategory (Modules Λ B)) :=
    DerivedCategory.shiftTensorShiftIso _ _ _ 2 (-2) ≪≫
      (shiftFunctorZero _ ℤ).app _ ≪≫ eD
  obtain ⟨_⟩ := DerivedCategory.nonempty_braidedCategory (Modules Λ B)
  have hN : IsDualizable ((S.obj N) ⟦(-2 : ℤ)⟧) :=
    isDualizable_of_tensorIso (β_ _ _ ≪≫ eShift) eShift
  let K := (SE.obj (line P Λ hΛ V.E)) ⟦(2 : ℤ)⟧
  let T := (S.obj N) ⟦(-2 : ℤ)⟧
  let G := (CondensedRing.upperStar Λ.X c.g).leftDerivedFunctor
  let J := (CondensedRing.openImmersionLowerShriek Λ.X c.i).mapDerivedCategory
  have hp : IsIso (properProjectionMorphism Λ.X c.g (J.obj K) T) := by
    have h := Adjunction.isIso_rightAdjointProjectionMap_app_app_of_isDualizable
      (derivedUpperStarLowerStarAdjunction Λ.X c.g)
        (Functor.OplaxMonoidal.δNatTrans G) (fun _ _ ↦ rfl) (J.obj K) hN
    simpa only [Adjunction.rightAdjointProjectionMap_app_app,
      Functor.OplaxMonoidal.δNatTrans_app_app, Adjunction.projectionMorphism,
      properProjectionMorphism, curriedTensor_map_app, curriedTensor_obj_obj,
      Functor.whiskeringLeft₂_obj_obj_obj_obj_obj,
      Functor.postcompose₂_obj_obj_obj_obj, Functor.comp_obj, Functor.id_obj, G, T] using h
  have : IsIso (exceptionalProjectionMorphismOfCompactification Λ.X c K T) := by
    unfold exceptionalProjectionMorphismOfCompactification
    infer_instance
  let eInside : K ⊗ F.obj T ≅ SE.obj (unit Λ V.E) :=
    whiskerRightIso (twistPull P Λ hΛ (V.p ≫ b) b V.p).symm _ ≪≫
      Functor.Monoidal.μIso F _ _ ≪≫ F.mapIso eShift ≪≫
      (Functor.Monoidal.εIso F).symm ≪≫
      (DerivedCategory.singleFunctorObjUnitIso (Modules Λ V.E)).symm
  exact ⟨asIso (exceptionalProjectionMorphismOfCompactification Λ.X c K T) ≪≫
    R.mapIso eInside⟩

end AlgebraicGeometry.ProEtale.CondensedRing
