/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.DiagonalPasting.PurityDiagonalSectionPastingData
public import WeilConjectures.AlgebraicGeometry.Section.SectionExceptionalFibreCoherence

/-! # The concrete factors of standard section pasting

These are the factors of `DiagonalPasting.nu`, with no orientations inserted.
Source: composition coherence Step 1, affine-space standard pairs.
(blueprint: def-route-standard-section-pasting-factors).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace WeilConjectures.PurityFiniteSetting.StandardPasting
open DiagonalPasting

/-- The block projections commute with affine-space base change, including empty blocks.
Source: composition coherence Step 1 (blueprint: def-route-standard-section-pasting-factors).
Proof: this is naturality of coordinate reindexing. The Cartesian assertion follows by
cancelling the lower affine-space Cartesian square from the outer one. -/
theorem geometry {B B' : Scheme.{u}} (d e : ℕ) (b : B' ⟶ B) :
    AffineSpace.map (ULift.{u} (Fin (d + e))) b ≫ q d e B =
      q d e B' ≫ AffineSpace.map (ULift.{u} (Fin e)) b ∧
    AffineSpace.map (ULift.{u} (Fin (d + e))) b ≫ first d e B =
      first d e B' ≫ AffineSpace.map (ULift.{u} (Fin d)) b ∧
    IsPullback (AffineSpace.map (ULift.{u} (Fin (d + e))) b)
      (q d e B') (q d e B) (AffineSpace.map (ULift.{u} (Fin e)) b) := by
  have hq := AffineSpace.map_reindex
    (fun i : ULift.{u} (Fin e) ↦ ULift.up (Fin.natAdd d i.down)) b
  have ht := AffineSpace.map_reindex
    (fun i : ULift.{u} (Fin d) ↦ ULift.up (Fin.castAdd e i.down)) b
  refine ⟨hq, ht, ?_⟩
  apply IsPullback.of_bot (p := hq)
    (t := AffineSpace.isPullback_map (n := ULift.{u} (Fin e)) b)
  simpa only [q, AffineSpace.reindex_over] using
    (AffineSpace.isPullback_map (n := ULift.{u} (Fin (d + e))) b)

variable (P : PurityFiniteSetting.{u})
  [HasInvertibleExponent P.Coefficient (Spec (.of P.field.k))]

/-- First input C₁: pullback composition followed by the actual smooth base-change mate.
Source: composition coherence Step 1 (blueprint: def-route-standard-section-pasting-factors).
-/
def firstInput (d e : ℕ) (B : Scheme.{u}) [IsNoetherian B]
    (aB : B ⟶ Spec (.of P.field.k)) :=
  letI := (affineGeometry d e B).2.2.2.2.1
  letI := (affineGeometry d e B).2.2.2.2.2.1
  letI := (affineGeometry d e B).2.2.2.2.2.2.1
  letI := (affineGeometry d e B).2.2.2.2.2.2.2.1
  letI := (affineGeometry d e B).2.2.2.2.2.2.2.2
  (Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} P.Coefficient)
    (zero (d + e) B) (first d e B) (zero d B)
    (affineGeometry d e B).2.1.symm).app _ ≪≫
    (Etale.upperStar (ModuleCat.{u + 1} P.Coefficient) (zero (d + e) B)).leftDerivedFunctor.mapIso
      (beta P.Coefficient P d (affineGeometry d e B).1 (pr d B ≫ aB))

/-- Second input C₂ is the compositor for q z = z_e.
Source: composition coherence Step 1 (blueprint: def-route-standard-section-pasting-factors).
-/
def secondInput (d e : ℕ) (B : Scheme.{u}) [IsNoetherian B] :=
  (Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} P.Coefficient)
    (zero (d + e) B) (q d e B) (zero e B)
    (affineGeometry d e B).2.2.1.symm).app (Etale.dualizingComplex P.Coefficient (pr e B))

/-- The sigma tail M is inverse tensor pullback followed by zero pullback of sigma.
Source: composition coherence Step 1 (blueprint: def-route-standard-section-pasting-factors).
-/
def tail (d e : ℕ) (B : Scheme.{u}) [IsNoetherian B]
    (aB : B ⟶ Spec (.of P.field.k)) :=
  letI := (affineGeometry d e B).2.2.2.2.1
  letI := (affineGeometry d e B).2.2.2.2.2.1
  letI := (affineGeometry d e B).2.2.2.2.2.2.1
  letI := (affineGeometry d e B).2.2.2.2.2.2.2.1
  letI := (affineGeometry d e B).2.2.2.2.2.2.2.2
  letI := affineDimension e B
  (Etale.leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} P.Coefficient)
    (zero (d + e) B) _ _).symm ≪≫
    (Etale.upperStar (ModuleCat.{u + 1} P.Coefficient) (zero (d + e) B)).leftDerivedFunctor.mapIso
      (sigma P.Coefficient P d (q d e B) (pr e B) (pr (d + e) B ≫ aB) ≪≫
        dualizingCongr P.Coefficient P (affineGeometry d e B).2.2.2.1)

/-- The specified affine section comparison, written with its structural pullback square.
Source: composition coherence Step 1 (blueprint: def-route-standard-section-pasting-factors).
-/
def baseChange {B B' : Scheme.{u}} [IsNoetherian B] [IsNoetherian B']
    (r : ℕ) (b : B' ⟶ B) (aB : B ⟶ Spec (.of P.field.k)) :=
  letI := affineDimension r B
  Etale.sectionCoherencePullbackIso P.Coefficient b (zero r B) (zero r B')
    (AffineSpace.map (ULift.{u} (Fin r)) b) (AffineSpace.zeroSection_comp_map b).symm _ ≪≫
    (Etale.upperStar (ModuleCat.{u + 1} P.Coefficient) (zero r B')).leftDerivedFunctor.mapIso
      (beta P.Coefficient P r (AffineSpace.isPullback_map b) (pr r B ≫ aB))

/-- k₁ is the zero pullback of the base-change mate for the first block projection.
Source: composition coherence Step 1 (blueprint: def-route-standard-section-pasting-factors).
-/
def firstChange {B B' : Scheme.{u}} [IsNoetherian B] [IsNoetherian B']
    (d e : ℕ) (b : B' ⟶ B) (aB : B ⟶ Spec (.of P.field.k)) :=
  letI := (affineGeometry d e B).2.2.2.2.1
  letI := (affineGeometry d e B).2.2.2.2.2.1
  letI := (affineGeometry d e B).2.2.2.2.2.2.1
  letI := (affineGeometry d e B).2.2.2.2.2.2.2.1
  letI := (affineGeometry d e B').2.2.2.2.2.1
  letI := (affineGeometry d e B').2.2.2.2.2.2.1
  letI := (affineGeometry d e B').2.2.2.2.2.2.2.1
  Etale.sectionCoherencePullbackIso P.Coefficient b (zero (d + e) B) (zero (d + e) B')
    (AffineSpace.map (ULift.{u} (Fin (d + e))) b)
    (AffineSpace.zeroSection_comp_map b).symm _ ≪≫
    (Etale.upperStar (ModuleCat.{u + 1} P.Coefficient) (zero (d + e) B')).leftDerivedFunctor.mapIso
      (beta P.Coefficient P d (geometry d e b).2.2 (pr (d + e) B ≫ aB))

/-- k₂ uses pullback interchange for q and the base-change mate for p_e.
Source: composition coherence Step 1 (blueprint: def-route-standard-section-pasting-factors).
-/
def secondChange {B B' : Scheme.{u}} [IsNoetherian B] [IsNoetherian B']
    (d e : ℕ) (b : B' ⟶ B) (aB : B ⟶ Spec (.of P.field.k)) :=
  letI := affineDimension e B
  Etale.sectionCoherencePullbackIso P.Coefficient b (zero (d + e) B) (zero (d + e) B')
    (AffineSpace.map (ULift.{u} (Fin (d + e))) b)
    (AffineSpace.zeroSection_comp_map b).symm _ ≪≫
    (Etale.upperStar (ModuleCat.{u + 1} P.Coefficient) (zero (d + e) B')).leftDerivedFunctor.mapIso
      (Etale.sectionCoherencePullbackIso P.Coefficient
        (AffineSpace.map (ULift.{u} (Fin (d + e))) b) (q d e B) (q d e B')
        (AffineSpace.map (ULift.{u} (Fin e)) b) (geometry d e b).1 _ ≪≫
      (Etale.upperStar (ModuleCat.{u + 1} P.Coefficient) (q d e B')).leftDerivedFunctor.mapIso
        (beta P.Coefficient P e (AffineSpace.isPullback_map b) (pr e B ≫ aB)))

-- Generate the defining equations in their owner module. Otherwise separate proof
-- modules unfolding these definitions can each export the same equation name.
attribute [local simp] baseChange firstChange secondChange

/-- Unfolding the specified nu gives these three concrete factors.
Source: composition coherence Step 1 (blueprint: def-route-standard-section-pasting-factors).
Proof: expand nu and invert the inverse first-input composite. -/
theorem nu_eq (d e : ℕ) (B : Scheme.{u}) [IsNoetherian B]
    (aB : B ⟶ Spec (.of P.field.k)) :
    nu P.Coefficient P d e B aB =
      tensorComparison P.Coefficient P (firstInput P d e B aB) (secondInput P d e B) ≪≫
        tail P d e B aB := by
  simp only [nu, firstInput, secondInput, tail, Iso.trans_symm,
    Functor.mapIso_symm, Iso.symm_symm_eq, Functor.mapIso_trans]

end WeilConjectures.PurityFiniteSetting.StandardPasting
