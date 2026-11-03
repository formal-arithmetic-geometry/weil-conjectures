/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteExceptionalTensor.FiniteExceptionalCoefficientTensor

/-! # Ordinary finite-coefficient scalar normalization -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale.FiniteExceptionalTensor
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.FiniteOrAlgebraicallyClosed

/-- The recorded ordinary scalar unit and tensorator have the standard unit and signed
symmetry constraints, for every adjunction presenting extension of coefficients.

Source: latest blueprint, det-sp-reduction-compatibilities, Proof (3), Tensor map;
ordinary K-flat scalar balancing and derived restriction normalization.
(blueprint: lem-sp-ordinary-finite-scalar-unit-symmetry-normalization).

Proof: Start with sheafified ordinary extension of scalars, left adjoint to exact
restriction. On degree-zero free modules, its unit comparison is multiplication
B tensor_A A -> B. The adjunction unit followed by restriction of this map is
precisely the ordinary lax unit of restriction. Resolve by flat-term K-flat complexes.
The derived restriction tensor map is normalized by its total-complex balancing
map. Hence transposition identifies the recorded scalarTensor with the canonical
left-derived comonoidal comparison, and identifies the displayed scalarUnit with
its degree-zero unit comparison, including the single-complex and localization
factors. The comparison on the unit is invertible since that unit is flat.
The ordinary left-unitor equation descends along the K-flat tensor comparisons;
its two sides apply the same scalar multiplication on every homogeneous tensor.
For symmetry, both routes interchange the same homogeneous factors with sign
(-1)^(ij), and keep the B coefficient action. The normalized derived comparisons
therefore satisfy the left-unit and braiding equations on arbitrary derived
objects by naturality and resolution isomorphisms. Finally, use uniqueness of left
adjoints to the fixed restriction functor to replace the derived adjunction by a.
Its unit equation transports both scalarTensor and scalarUnit, so the isomorphism
and both equations hold for the specified a, including zero rings and nonflat maps.
-/
theorem ordinaryFiniteScalar_unit_symmetry
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) (T : Scheme.{u}) (a : scalar φ T ⊣ restrict φ T)
    (U V : D A T) :
    IsIso (scalarUnit φ T a) ∧
      ((scalar φ T).map (λ_ V).hom =
        scalarTensor φ T a (𝟙_ _) V ≫
          (scalarUnit φ T a ⊗ₘ 𝟙 ((scalar φ T).obj V)) ≫
          (λ_ ((scalar φ T).obj V)).hom) ∧
      ((scalar φ T).map (braiding A T U V).hom ≫ scalarTensor φ T a V U =
        scalarTensor φ T a U V ≫
          (braiding B T ((scalar φ T).obj U) ((scalar φ T).obj V)).hom) := by
  sorry

end AlgebraicGeometry.ProEtale.FiniteOrAlgebraicallyClosed
