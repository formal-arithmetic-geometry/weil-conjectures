/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C8
-/
module

public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.RingTheory.TensorProduct.MvPolynomial

/-!
# The affine ambient space of the universal incidence equation

Source: Stacks Project, More on Morphisms, Tag 0G4F, affine incidence charts.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace AlgebraicGeometry

/-- The coefficient-change polynomial square is cartesian on spectra. Thus the pullback
of coefficient affine space to Spec A is Spec of the polynomial ring over A, with its
specified coordinate and projection maps.

Source: Stacks Project, More on Morphisms, Tag 0G4F, the affine incidence chart.
(blueprint: lem-zl-bertini-affine-ambient).

Proof: The tensor product A tensor_k k[x_i] is the pushout of the two k-algebras. Its
canonical polynomial equivalence with A[x_i] identifies the two coprojections with C and
coefficient change. Apply the spectrum functor and reverse the two legs. The argument
works for any commutative base ring and any variable type. -/
theorem isPullback_bertiniAffineAmbient
    (k A : Type u) [CommRing k] [CommRing A] [Algebra k A] (I : Type u) :
    IsPullback
      (Spec.map (CommRingCat.ofHom (MvPolynomial.map
        (σ := I) (algebraMap k A))))
      (Spec.map (CommRingCat.ofHom (MvPolynomial.C : A →+* MvPolynomial I A)))
      (Spec.map (CommRingCat.ofHom (MvPolynomial.C : k →+* MvPolynomial I k)))
      (Spec.map (CommRingCat.ofHom (algebraMap k A))) := by
  let e := (MvPolynomial.algebraTensorAlgEquiv (σ := I) k A).toCommRingCatIso
  have hp : IsPushout
      (CommRingCat.ofHom (algebraMap k A))
      (CommRingCat.ofHom (MvPolynomial.C : k →+* MvPolynomial I k))
      (CommRingCat.ofHom (MvPolynomial.C : A →+* MvPolynomial I A))
      (CommRingCat.ofHom (MvPolynomial.map (algebraMap k A))) :=
    (CommRingCat.isPushout_tensorProduct k A (MvPolynomial I k)).of_iso
    (Iso.refl _) (Iso.refl _) (Iso.refl _) e (by simp) (by simp)
    (by
      apply CommRingCat.hom_ext
      apply RingHom.ext
      intro a
      change (MvPolynomial.algebraTensorAlgEquiv k A)
        (a ⊗ₜ[k] (1 : MvPolynomial I k)) = MvPolynomial.C a
      simp [MvPolynomial.algebraTensorAlgEquiv_tmul, MvPolynomial.smul_eq_C_mul])
    (by
      apply CommRingCat.hom_ext
      apply RingHom.ext
      intro p
      change (MvPolynomial.algebraTensorAlgEquiv k A) (1 ⊗ₜ[k] p) =
        MvPolynomial.map (algebraMap k A) p
      simp [MvPolynomial.algebraTensorAlgEquiv_tmul])
  exact (isPullback_SpecMap_of_isPushout _ _ _ _ hp).flip

end AlgebraicGeometry
