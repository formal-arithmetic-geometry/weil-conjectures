/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q04
-/
module

public import Sheaf.AlgebraicGeometry.ProEtaleFiniteModules
public import Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations
public import Sheaf.SecSmoothPurity.ScalarExtensionFunctor
public import Sheaf.SecSmoothPurity.ReductionDirectImageComparison

import Sheaf.Paper.ProEtaleBoundedConstructibleTriangulated
import Sheaf.AlgebraicGeometry.ProEtaleInverseImage
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.Algebra.Homology.SuccessiveDerivedQuotientNormalization
import Sheaf.Paper.RingedCoefficientProjectionCocycle
import Mathlib.CategoryTheory.Adjunction.Basic

/-! # Coefficient cocycle for the ambient direct-image mate

Source: blueprint main-20261015, sec-smooth-purity/sk-lem-sp-reduction,
sk-lem-sp-reduction-direct-image.proof.md, Step 4; Stacks Tags 07A7 and 0E47
(blueprint: lem-sp-proetale-direct-image-scalar-cocycle).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.ProEtale

/-- The specified counit mates commute with successive scalar extension, naturally in E.
Source: blueprint direct-image proof Step 4; Stacks Tags 07A7 and 0E47
(blueprint: lem-sp-proetale-direct-image-scalar-cocycle).

Proof:
1. Specialize the small-site geometric operations to q. The canonical constant-ring
inverse-image comparisons preserve constant sections, hence intertwine both coefficient
maps; restriction, gluing and sheafification give the same assertion on all sections
(lem-pur-proetale-constant-coefficient-comparison and def-weil-proetale-inverse-image).
2. Choose flat-term K-flat representatives by lem-pc-kflat-resolution. The associator of
lem-sfb-successive-derived-quotient-normalization sends (x tensor b) tensor c to
x tensor psi(b)c, with inverse inserting 1. This is exactly the specified
scalarExtensionFunctor_composition, including the target-ring action, for arbitrary maps.
3. The balanced tensor/pullback comparison defining directImageScalarComparison is the
inverse-image comparison of lem-pur-ringed-coefficient-projection-cocycle. Its counit
transpose is scalar extension of the source counit after this comparison. Uniqueness of
adjuncts (lem-weil-pbc-adjunct-counit-identity) identifies the three specified mates.
4. Apply lem-pur-ringed-coefficient-projection-cocycle and substitute these identifications
and the normalized associators. Its source is successive scalar extension of Rq_* E;
its target is Rq_* of direct scalar extension of E. This gives the displayed equation.
5. All comparisons are natural transformations, so the equation is natural in every
morphism E to E'. The general cocycle uses ordinary unbounded categories and arbitrary
ring maps and geometric morphisms. No properness, boundedness, flatness or finite
projective dimension enters this specialization. -/
theorem proEtaleDirectImageScalarCocycle
    (ℓ : ℕ) [Fact ℓ.Prime]
    {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    [Finite A] [Finite B] [Finite C]
    (_hA : ∃ n : ℕ, ∀ a : A, (ℓ ^ n) • a = 0)
    (_hB : ∃ n : ℕ, ∀ b : B, (ℓ ^ n) • b = 0)
    (_hC : ∃ n : ℕ, ∀ c : C, (ℓ ^ n) • c = 0)
    (φ : A →+* B) (ψ : B →+* C)
    {Z Y : Scheme.{u}} (q : Z ⟶ Y) (E : Scheme.proEtaleDerivedCategory Z A) :
    (scalarExtensionFunctor_composition φ ψ Y).hom.app
        ((directImageConstantPush A q).obj E) ≫
      (directImageScalarComparison (ψ.comp φ) q).app E =
    (scalarExtensionFunctor ψ Y).map ((directImageScalarComparison φ q).app E) ≫
      (directImageScalarComparison ψ q).app ((scalarExtensionFunctor φ Z).obj E) ≫
      (directImageConstantPush C q).map
        ((scalarExtensionFunctor_composition φ ψ Z).hom.app E) := by
  sorry

end AlgebraicGeometry.ProEtale
