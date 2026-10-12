/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group U3
-/
module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.LinearAlgebra.TensorProduct.RightExactness

/-!
# Residue-field tensor of the section-map cokernel

Source: Stacks Project, Tag 04DG, proof, affine fibre and Nakayama steps.
(blueprint: lem-weil-pbc-finite-fibre-cokernel-tensor).
-/

@[expose] public section

universe u

open CategoryTheory
open scoped TensorProduct

namespace AlgebraicGeometry

/-- The cokernel of the affine section map has zero residue-field tensor when the fibre
is a closed immersion.
Source: Stacks Project, Tag 04DG, proof, affine fibre and Nakayama steps.
(blueprint: lem-weil-pbc-finite-fibre-cokernel-tensor).

Proof: Put A = Γ(S,U) and B = Γ(X,f⁻¹U). Since f is finite, both U and f⁻¹U are affine.
The prime p corresponding to s has residue field canonically isomorphic to κ(s).
The affine pullback formula identifies the fibre with Spec(κ(p) ⊗[A] B), and its map
with the spectrum of the scalar map κ(p) → κ(p) ⊗[A] B. A closed immersion between
these affine schemes gives surjectivity of that scalar map. The image of the map
A → B is its range as an A-linear map. Tensoring its cokernel sequence with κ(p)
is right exact, so its cokernel tensor product is zero. No Nakayama step is needed
here. For an empty fibre the tensor algebra is the zero ring, and the argument
still applies. -/
theorem subsingleton_fibreTensor_sectionCokernel
    {X S : Scheme.{u}} (f : X ⟶ S) [IsFinite f]
    (U : S.Opens) (hU : IsAffineOpen U) (s : U)
    (hf : IsClosedImmersion (f.fiberToSpecResidueField s.1)) :
    letI := (f.app U).hom.toAlgebra
    Subsingleton ((hU.primeIdealOf s).asIdeal.ResidueField ⊗[Γ(S, U)]
      (Γ(X, f ⁻¹ᵁ U) ⧸ (Algebra.linearMap Γ(S, U) Γ(X, f ⁻¹ᵁ U)).range)) := by
  let := (f.app U).hom.toAlgebra
  let A := Γ(S, U)
  let B := Γ(X, f ⁻¹ᵁ U)
  let p := hU.primeIdealOf s
  let K := p.asIdeal.ResidueField
  let φ : A →ₗ[A] B := Algebra.linearMap A B
  let q := φ.range.mkQ
  have hV := hU.preimage f
  have hpb : IsPullback hV.fromSpec (Spec.map (f.app U)) f hU.fromSpec :=
    (IsOpenImmersion.isPullback (Spec.map (f.app U)) hV.fromSpec hU.fromSpec f
      (by simpa only [Scheme.Hom.appLE_eq_app] using
        (IsAffineOpen.SpecMap_appLE_fromSpec f hU hV le_rfl).symm)
      (by rw [hV.opensRange_fromSpec, hU.opensRange_fromSpec])).flip
  have hclosed : IsClosedImmersion
      ((Spec.map (f.app U)).fiberToSpecResidueField p) := by
    apply MorphismProperty.of_isPullback
      (isPullback_fiberToSpecResidueField_of_isPullback hpb p)
    change IsClosedImmersion (f.fiberToSpecResidueField (hU.fromSpec p))
    rw [hU.fromSpec_primeIdealOf]
    exact hf
  have hscalar : IsClosedImmersion
      (Spec.map (CommRingCat.ofHom (algebraMap K (K ⊗[A] B)))) :=
    (MorphismProperty.arrow_mk_iso_iff (P := @IsClosedImmersion)
      (Spec.fiberToSpecResidueFieldIso A B p)).mp hclosed
  have hsurj : Function.Surjective (algebraMap K (K ⊗[A] B)) := by
    have hs := (IsClosedImmersion.isAffine_surjective_of_isAffine
      (Spec.map (CommRingCat.ofHom (algebraMap K (K ⊗[A] B))))).2
    exact (RingHom.surjective_respectsIso.arrow_mk_iso_iff
      (arrowIsoΓSpecOfIsAffine (CommRingCat.ofHom (algebraMap K (K ⊗[A] B))))).mpr hs
  have hqzero : ∀ z : K ⊗[A] B, q.lTensor K z = 0 := by
    intro z
    obtain ⟨k, rfl⟩ := hsurj z
    simp only [Algebra.TensorProduct.algebraMap_apply, LinearMap.lTensor_tmul]
    have hone : q (1 : B) = 0 := by
      exact (Submodule.Quotient.mk_eq_zero φ.range).mpr ⟨1, by simp [φ]⟩
    rw [hone, TensorProduct.tmul_zero]
  have hz : ∀ z : K ⊗[A] (B ⧸ φ.range), z = 0 := by
    intro z
    obtain ⟨y, rfl⟩ := LinearMap.lTensor_surjective K (Submodule.mkQ_surjective φ.range) z
    exact hqzero y
  exact ⟨fun x y ↦ (hz x).trans (hz y).symm⟩

end AlgebraicGeometry
