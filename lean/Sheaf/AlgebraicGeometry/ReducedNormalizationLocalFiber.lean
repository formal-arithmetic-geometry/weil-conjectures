/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K7
-/
module

public import Sheaf.AlgebraicGeometry.NodalLocalTangentData
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
# The fibre of reduced normalization from the local integral closure

Source: Stacks Project, Morphisms, Tags 035P and 0CDV; Algebra, Tag 0307.
(blueprint: lem-sfb-reduced-normalization-local-fibre).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.NodalLocal

/-- Localizing componentwise normalization and then taking its closed fibre.

Source: Stacks Project, Morphisms, Tags 035P and 0CDV; Algebra, Tag 0307.
(blueprint: lem-sfb-reduced-normalization-local-fibre).

Proof:
Choose a Noetherian affine neighbourhood Spec S of x, corresponding to p, so the stalk
is S_p. Its reduced ring has finitely many minimal primes p_i, and the components
meeting this neighbourhood are exactly Spec(S/p_i). On each component, the affine
normalization formula identifies the inverse image with Spec B_i, where B_i is the
integral closure in Frac(S/p_i). The finite disjoint union is Spec(product B_i).
Pulling back to Spec(S_p) localizes this product. Integral closure commutes with
localization. Factors with p_i not contained in p become zero; the others give the
integral closures of the minimal-prime quotients of (S_p)_red. The total quotient ring
of this reduced Noetherian ring is the product of their fraction fields. Integrality
is componentwise: projecting a monic equation proves one implication, and multiplying
component monic equations proves the converse. The localized product is therefore the
actual Normalization of the stalk. This gives its canonical map to C's reduced
normalization, over the stalk map. Pulling this cartesian square back to the residue
field gives Spec(B tensor_A kappa) = Spec(B/mB). The quotient and residue structural
maps are the projections, by the affine tensor-product formula. No nodal, purity,
finite-type, or coefficient-field hypothesis is used in this local calculation.
-/
theorem reduced_normalization_local_fibre
    (C : Scheme.{u}) [IsLocallyNoetherian C] (x : C) :
    ∃ l : Spec (.of (Normalization (C.presheaf.stalk x))) ⟶ C.reducedNormalization,
      l ≫ C.fromReducedNormalization =
        Spec.map (CommRingCat.ofHom
          (algebraMap (C.presheaf.stalk x) (Normalization (C.presheaf.stalk x)))) ≫
            C.fromSpecStalk x ∧
      IsPullback
        (Spec.map (CommRingCat.ofHom
          (Ideal.Quotient.mk (normalizationIdeal (C.presheaf.stalk x)))) ≫ l)
        (Spec.map (CommRingCat.ofHom
          (algebraMap (C.residueField x) (ResidueAlgebra (C.presheaf.stalk x)))))
        C.fromReducedNormalization (C.fromSpecResidueField x) := by sorry

end AlgebraicGeometry.NodalLocal
