/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleCompleteSupplement
public import WeilConjectures.AlgebraicGeometry.ReconstructionUniformTower
public import WeilConjectures.AlgebraicGeometry.ProEtaleConstructibleCoefficientSheaf
import all WeilConjectures.AlgebraicGeometry.CompletedConstructiblePreservation
import all WeilConjectures.AlgebraicGeometry.FiniteCoefficientDerivedOriginPresentation
import all WeilConjectures.AlgebraicGeometry.WeilTensorProduct

/-! # Reconstruction of a uniformly modeled tower in one degree

Source: uniform reconstruction, Stacks Tags 099M and 09AL.
(blueprint: lem-pur-single-degree-uniform-reconstruction)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme

/-- A common model concentrated in one degree reconstructs to a complete constructible
object in that degree. The finite reduction maps are the actual projection counits.

Source: uniform reconstruction, Stacks Tags 099M, 09C7 and 09AL.
(blueprint: lem-pur-single-degree-uniform-reconstruction)

Proof: apply uniform reconstruction with the retained model. Its completeness clause
on a localization representative gives intrinsic completeness in the presentation used
by the constructible complete category. Its invertible counits transport finite-level
constructibility and the common bound to the canonical reductions. Finite constructible
origins and their uniquely lifted normalizations then give the other two clauses of
constructible completeness. The model's equal lower and upper bounds give concentration
of the actual derived limit. All normalizations are those of uniform reconstruction.
-/
theorem singleDegreeUniformReconstruction
    {k : Type u} [Field k] (T : Scheme.{u}) [IsNoetherian T]
    (fT : T ⟶ Spec (.of k)) (hT : LocallyOfFiniteType fT ∧ QuasiCompact fT)
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)
    (M : AdicTower T d) (S : Stratification T) (W : UniformAdicTowerData d M S)
    (q₀ : ℤ) (hlower : W.lower = q₀) (hupper : W.upper = q₀)
    (hc : ∀ (n : ℕ) (q : ℤ),
      @IsConstructibleProEtaleCoefficientModuleSheaf T (A ⧸ d.ideal ^ (n + 1)) _
        (d.quotientFinite n)
        ((pbcRestrict (pbcLevelConstantComparison T d n).hom).obj
          ((DerivedCategory.homologyFunctor _ q).obj (M.level n))))
    (hz : ∀ (n : ℕ) (q : ℤ), q ≠ q₀ →
      IsZero ((DerivedCategory.homologyFunctor _ q).obj (M.level n))) :
    PbcIsBoundedConstructibleComplete T d (uniformReconstructionLimit d M) ∧
    (∀ n : ℕ, IsIso (uniformReconstructionCounit d M n)) ∧
    (∀ (b a : ℕ) (hab : a ≤ b),
      (pbcDerivedExtend (pbcAdicQuotient T d b a hab)).map
          (uniformReconstructionCounit d M b) ≫ (M.normalization b a hab).hom =
        (pbcReductionNormalization (pbcAdicProjection T d b)
          (pbcAdicQuotient T d b a hab) (pbcAdicProjection T d a)
          (pbcAdicProjection_comp T d b a hab)
          (uniformReconstructionLimit d M)).hom ≫ uniformReconstructionCounit d M a) ∧
    ∀ q : ℤ, q ≠ q₀ → IsZero ((DerivedCategory.homologyFunctor _ q).obj
      (uniformReconstructionLimit d M)) := by
  obtain ⟨φ, _, hglobal, _⟩ := reconstructionUniformTower T fT hT d S
  obtain ⟨hcomplete, hunit, hnorm, hbound⟩ := hglobal M W
  have hintrinsic : PbcIsIntrinsicallyComplete T d (uniformReconstructionLimit d M) := by
    obtain ⟨r, a, ha⟩ := Submodule.fg_iff_exists_fin_generating_family.mp d.finitelyGenerated
    exact wfPresentation_of_complete T d r a ha _
      (hcomplete r a ha _ (DerivedCategory.Q.objObjPreimageIso _))
  have hcontrol : PbcConstructibleReductionControl T d
      (uniformReconstructionLimit d M) := by
    refine ⟨q₀, q₀, le_rfl, ?_, ?_⟩
    · intro n q
      have := hunit n
      exact intrinsic_constructible_of_iso T _
        ((pbcRestrict (pbcLevelConstantComparison T d n).hom).mapIso
          ((DerivedCategory.homologyFunctor _ q).mapIso
            (asIso (uniformReconstructionCounit d M n))).symm) (hc n q)
    · intro n q hq
      have := hunit n
      exact (hz n q (by omega)).of_iso
        ((DerivedCategory.homologyFunctor _ q).mapIso
          (asIso (uniformReconstructionCounit d M n)))
  refine ⟨boundedConstructible_of_reductionControl T d _ hintrinsic hcontrol,
    hunit, hnorm, ?_⟩
  intro q hq
  apply hbound q
  rw [hlower, hupper]
  omega

end AlgebraicGeometry.Scheme
