/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Reduction.ReductionExceptionalObjects
import WeilConjectures.AlgebraicGeometry.SmoothOfRelativeDimension.SmoothAdmissibleCoordinateCover
import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteP1Adjunction
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.OpenCover

/-! # Detecting invertibility from the normalized exceptional chart equation -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace AlgebraicGeometry.ProEtale

/-- The normalized chart equation forces every component of the transpose to be an
isomorphism. Source: blueprint latest, sec-smooth-purity,
sk-lem-sp-reduction-exceptional.proof.md, Steps 12--13
(blueprint: lem-sp-reduction-exceptional-components-isIso).

Proof: the open exceptional-locality comparison identifies each restriction of the
transpose with the canonical chart reassociation. Chart scalar transport makes that
reassociation invertible, and all realization, pullback and site comparisons are
isomorphisms. Derived pullback over the finite admissible open cover is jointly
conservative, so the ambient component is invertible; the full-subcategory inclusion
reflects isomorphisms. -/
theorem reductionExceptional_components_isIso
    (ℓ pchar : ℕ) [Fact ℓ.Prime] (_hp : 0 < pchar) (_hℓ : pchar ≠ ℓ)
    (k : Type u) [Field k] [CharP k pchar]
    {X Z Y : Scheme.{u}}
    [X.Over (Spec (.of k))] [Z.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Z ↘ Spec (.of k))] [QuasiCompact (Z ↘ Spec (.of k))]
    [IsSeparated (Z ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))] (d : ℕ) [SmoothOfRelativeDimension d f]
    (j : X ⟶ Z) [IsOpenImmersion j] [j.IsOver (Spec (.of k))]
    (p : Z ⟶ Y) [IsProper p] [p.IsOver (Spec (.of k))] (hf : j ≫ p = f)
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (hA : ∃ n : ℕ, ∀ x : A, (ℓ ^ n) • x = 0)
    (hB : ∃ n : ℕ, ∀ x : B, (ℓ ^ n) • x = 0) (φ : A →+* B)
    (hFA : ∀ M : spFiniteConstructibleTorCategory X A,
      spFiniteConstructibleTor Y A ((reductionCompactSupport A j p).obj M.obj))
    (hFB : ∀ M : spFiniteConstructibleTorCategory X B,
      spFiniteConstructibleTor Y B ((reductionCompactSupport B j p).obj M.obj))
    (hSX : ∀ M : spFiniteConstructibleTorCategory X A,
      spFiniteConstructibleTor X B ((scalarExtensionFunctor φ X).obj M.obj))
    (hSY : ∀ K : spFiniteConstructibleTorCategory Y A,
      spFiniteConstructibleTor Y B ((scalarExtensionFunctor φ Y).obj K.obj))
    (GA : spFiniteConstructibleTorCategory Y A ⥤ spFiniteConstructibleTorCategory X A)
    (GB : spFiniteConstructibleTorCategory Y B ⥤ spFiniteConstructibleTorCategory X B)
    (adjA : reductionCtfCompactSupport A j p hFA ⊣ GA)
    (adjB : reductionCtfCompactSupport B j p hFB ⊣ GB)
    (RA : ReductionExceptionalRealization A j p hFA GA adjA)
    (RB : ReductionExceptionalRealization B j p hFB GB adjB)
    (c : GA ⋙ reductionCtfScalar φ X hSX ⟶ reductionCtfScalar φ Y hSY ⋙ GB)
    (hchart : ReductionExceptionalChartEquation ℓ φ j p d hFA hFB hSX hSY GA GB adjA adjB RA RB c) :
    ∀ K : spFiniteConstructibleTorCategory Y A, IsIso (c.app K)  := by
  classical
  intro K
  have : IsLocallyNoetherian X :=
    LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of k))
  have : CompactSpace X :=
    QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of k))
  have : IsNoetherian X := ⟨⟩
  have : IsLocallyNoetherian Y :=
    LocallyOfFiniteType.isLocallyNoetherian (Y ↘ Spec (.of k))
  have : CompactSpace Y :=
    QuasiCompact.compactSpace_of_compactSpace (Y ↘ Spec (.of k))
  have : IsNoetherian Y := ⟨⟩
  obtain ⟨r, hr⟩ := hA
  obtain ⟨s, hs⟩ := hB
  let n := r + s
  have hnA : ((ℓ ^ n : ℕ) : ULift.{u + 1, u} A) = 0 := by
    apply ULift.ext
    change ((ℓ ^ (r + s) : ℕ) : A) = 0
    rw [pow_add, Nat.cast_mul]
    have hz : ((ℓ ^ r : ℕ) : A) = 0 := by
      simpa only [nsmul_eq_mul, mul_one] using hr 1
    rw [hz, zero_mul]
  have hnB : ((ℓ ^ n : ℕ) : ULift.{u + 1, u} B) = 0 := by
    apply ULift.ext
    change ((ℓ ^ (r + s) : ℕ) : B) = 0
    rw [pow_add, Nat.cast_mul]
    have hz : ((ℓ ^ s : ℕ) : B) = 0 := by
      simpa only [nsmul_eq_mul, mul_one] using hs 1
    rw [hz, mul_zero]
  obtain ⟨o, ho, hchart⟩ := hchart
  obtain ⟨hY, hchart⟩ := hchart n hnA hnB
  obtain ⟨MA⟩ := Etale.nonempty_etaleCompactSupportNormalization (ULift.{u + 1, u} A)
  obtain ⟨MB⟩ := Etale.nonempty_etaleCompactSupportNormalization (ULift.{u + 1, u} B)
  obtain ⟨tA, DA, _⟩ := Etale.exists_ordinaryFiniteP1Adjunction (ℓ ^ n)
    (pow_pos (Fact.out : ℓ.Prime).pos n) (ULift.{u + 1, u} A) hnA
  obtain ⟨tB, DB, _⟩ := Etale.exists_ordinaryFiniteP1Adjunction (ℓ ^ n)
    (pow_pos (Fact.out : ℓ.Prime).pos n) (ULift.{u + 1, u} B) hnB
  obtain ⟨m, U, V, hUV, e₀, e, hcover, _, _, _, _, he⟩ :=
    SmoothOfRelativeDimension.exists_finite_admissible_coordinate_cover
      (k := k) f d
  have hlocal (a : Fin m) :
      IsIso ((proEtaleConstantRingDerivedPullback B (U a).ι).map (c.app K).hom) := by
    have ha := he a
    have : IsNoetherian (U a).toScheme := ha.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    have : IsSeparated (e a) := ha.2.2.2.2.2.1
    have : AlgebraicGeometry.Etale (e a) := ha.2.2.2.2.2.2.1
    have : LocallyOfFinitePresentation (e a) := ha.2.2.2.2.2.2.2.1
    have : QuasiCompact (e a) := ha.2.2.2.2.2.2.2.2.1
    let v := e a ≫ (affineTraceAffineSpaceIso Y d).inv
    have : IsSeparated v := inferInstance
    have : AlgebraicGeometry.Etale v := inferInstance
    have : LocallyOfFiniteType v := inferInstance
    have : QuasiCompact v := inferInstance
    have hv : (U a).ι ≫ (j ≫ p) = v ≫ affineTraceProjection Y d := by
      rw [hf, ha.2.2.2.2.2.2.2.2.2.2.1]
      dsimp [v]
      have hp : affineTraceToAffineSpace Y d ≫
          (AffineSpace (ULift.{u} (Fin d)) Y ↘ Y) = affineTraceProjection Y d :=
        AffineSpace.homOfVector_over _ _
      rw [← hp]
      simp [Category.assoc, affineTraceAffineSpaceIso]
    have h := hchart MA MB tA DA tB DB inferInstance inferInstance
      (U a).toScheme (U a).ι v hv K
    have : IsIso ((directImageScalarPullbackIso φ (U a).ι).inv.app (GA.obj K).obj ≫
        (proEtaleConstantRingDerivedPullback B (U a).ι).map (c.app K).hom ≫
        (reductionIntrinsicChartIso B j p hFB GB adjB RB MB (U a).ι d v hv
          (ℓ ^ n) hnB tB DB hY ((reductionCtfScalar φ Y hSY).obj K)).hom) := by
      change IsIso ((directImageScalarPullbackIso φ (U a).ι).inv.app
        (GA.obj K).obj ≫ (proEtaleConstantRingDerivedPullback B (U a).ι).map
          (reductionExceptionalComponent φ X Y hSX hSY GA GB c K) ≫ _)
      rw [h]
      infer_instance
    have := IsIso.of_isIso_comp_left
      ((directImageScalarPullbackIso φ (U a).ι).inv.app (GA.obj K).obj)
      ((proEtaleConstantRingDerivedPullback B (U a).ι).map (c.app K).hom ≫
        (reductionIntrinsicChartIso B j p hFB GB adjB RB MB (U a).ι d v hv
          (ℓ ^ n) hnB tB DB hY ((reductionCtfScalar φ Y hSY).obj K)).hom)
    exact IsIso.of_isIso_comp_right _
      (reductionIntrinsicChartIso B j p hFB GB adjB RB MB (U a).ι d v hv
        (ℓ ^ n) hnB tB DB hY ((reductionCtfScalar φ Y hSY).obj K)).hom
  let E := sfIntrinsicDerivedEquivalence X B
  let g := E.inverse.map (c.app K).hom
  have hfixed (a : Fin m) : IsIso ((sfFixedDerivedPullback B (U a).ι).map g) := by
    have hi : IsIso ((proEtaleConstantRingDerivedPullback B (U a).ι).map
        (E.functor.map g)) := by
      have := hlocal a
      exact (NatIso.isIso_map_iff
        (Functor.isoWhiskerRight E.counitIso
          (proEtaleConstantRingDerivedPullback B (U a).ι)) (c.app K).hom).mpr
          (by simpa only [Functor.comp_map, Functor.id_map] using hlocal a)
    have hi' : IsIso ((sfIntrinsicDerivedEquivalence (U a).toScheme B).functor.map
        ((sfFixedDerivedPullback B (U a).ι).map g)) :=
      (NatIso.isIso_map_iff (reductionRealizationPullbackIso B (U a).ι) g).mp hi
    exact isIso_of_reflects_iso _ (sfIntrinsicDerivedEquivalence (U a).toScheme B).functor
  have hg : IsIso g := by
    obtain ⟨C, v, δ, ht⟩ := Pretriangulated.distinguished_cocone_triangle g
    apply (Pretriangulated.Triangle.isZero₃_iff_isIso₁ _ ht).mp
    apply isZero_of_forall_isZero_mapDerivedCategory_upperStar
      (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) U hcover
    intro a
    have := hfixed a
    apply (Pretriangulated.Triangle.isZero₃_iff_isIso₁ _
      ((sfFixedDerivedPullback B (U a).ι).map_distinguished _ ht)).mpr
    exact hfixed a
  have : IsIso (c.app K).hom := isIso_of_reflects_iso _ E.inverse
  exact (ObjectProperty.isIso_hom_iff (c.app K)).mp inferInstance


end AlgebraicGeometry.ProEtale
