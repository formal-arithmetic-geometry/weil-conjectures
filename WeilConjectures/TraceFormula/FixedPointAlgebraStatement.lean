/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.FiniteFieldDatum.FiniteFieldRelationsEvaluation
public import WeilConjectures.SmoothPurity.FiniteFieldDatum.RelativeFrobeniusGeometricFiber
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Properties

/-!
# Evaluation and the affine Frobenius fixed scheme

Source: latest blueprint, `sec-trace-formula/sk-lem-tf-fixed-points/`
`det-tf-fixed-point-algebra.md` and its proof
(blueprint: det-tf-fixed-point-algebra).

The two evaluation isomorphisms, their evaluation formulas and their identification of
surviving tuples with model algebra maps are the existing declaration
`FiniteFieldDatum.finite_field_relations_evaluation`; they are not restated here.
This module states the geometric consequence and its affine-open compatibility.
Mathlib's equalizer is the fixed scheme: it represents maps on which Frobenius is the
identity, equivalently the pullback of the graph along the diagonal. No coefficient or
cohomological realization enters this construction.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace WeilConjectures

/-- Algebra maps from the presented model to the prescribed extension field are exactly
its field-valued scheme points over the finite base, with the usual contravariant Spec map.
Together with `finite_field_relations_evaluation`, this indexes the second evaluation
product by the field-valued points appearing in the node.

Source: latest blueprint `sec-trace-formula/sk-lem-tf-fixed-points/`
`det-tf-fixed-point-algebra.proof.md`, surviving rational solutions
(blueprint: det-tf-fixed-point-algebra).

Proof: Spec is fully faithful on commutative rings, so its morphisms between these affine
schemes are exactly the reversed ring homomorphisms. The equation of being over Spec k₀
is equivalent, by faithfulness, to commuting with the two coefficient maps. This is
exactly the algebra-homomorphism condition for the algebra structure induced by the
specified extension embedding. Restricting the Spec bijection to these maps gives the
equivalence and its displayed normalization. The zero ring is allowed: in that case both
sets are empty, since the target extension field is nontrivial. -/
theorem det_tf_fixed_point_algebra_points
    (D : FiniteFieldDatum.{u}) (m : ℕ) (hm : 1 ≤ m) (r : ℕ)
    (a : Ideal (MvPolynomial (Fin r) D.k₀)) :
    letI : Algebra D.k₀ (D.extensionSubfield m hm) :=
      (D.extensionEmbedding m hm).toAlgebra
    ∃ e : D.relationModelPoints m hm r a ≃
        (Over.mk (Spec.map (CommRingCat.ofHom (D.extensionEmbedding m hm))) ⟶
          Over.mk (Spec.map (CommRingCat.ofHom
            (algebraMap D.k₀ (MvPolynomial (Fin r) D.k₀ ⧸ a))))),
      ∀ φ : D.relationModelPoints m hm r a,
        (e φ).left = Spec.map (CommRingCat.ofHom φ.toRingHom) := by
  sorry

end WeilConjectures
