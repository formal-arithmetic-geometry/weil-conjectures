/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q05
-/
module

public import Sheaf.AlgebraicGeometry.ProEtaleFiniteModules
public import Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations
public import Sheaf.SecSmoothPurity.ScalarExtensionFunctor
public import Sheaf.SecSmoothPurity.ReductionDirectImageComparison
public import Sheaf.AlgebraicGeometry.ProEtaleIntrinsicExtensionByZero

import Sheaf.Algebra.Homology.SheafRingDerivedCoefficientAdjunction
import Sheaf.AlgebraicGeometry.ProEtaleRingSheafChangeAdjunction
import Sheaf.Algebra.Homology.SuccessiveDerivedQuotientNormalization
import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.CategoryTheory.Adjunction.Mates
import Mathlib.CategoryTheory.Localization.Predicate
import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings

/-!
# Coefficient cocycle for normalized open scalar comparisons

Source: blueprint main-20261015, sec-smooth-purity/sk-lem-sp-reduction,
sk-lem-sp-reduction-direct-image.proof.md, Steps 1 and 4
(blueprint: lem-sp-proetale-open-scalar-cocycle).

The equation uses the prescribed scalar associator and the prescribed comparison for
sectionwise sheafified extension by zero on the full ordinary unbounded categories.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory
open AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.ProEtale

/-- The normalized open scalar comparison satisfies the coefficient cocycle.
Source: blueprint main-20261015, sk-lem-sp-reduction-direct-image.proof.md, Steps 1 and 4
(blueprint: lem-sp-proetale-open-scalar-cocycle).

Proof:
1. Use the normalized scalar adjunctions of
   lem-pur-sheaf-ring-derived-coefficient-adjunction and the open adjunctions of
   def-sp-reduction-direct-image-comparison, composing them by
   def-weil-pbc-composite-adjunction. The right conjugate of the open comparison beta
   is the restriction/pullback comparison chi of lem-weil-pbc-ring-sheaf-change-adjunction.
2. Restriction along A -> B -> C leaves sections unchanged and gives the action through
   the composite ring map (def-pc-sheaf-restrict-scalars). Both coefficient/pullback
   pastings are the identity on the inverse-image abelian sheaf. Descend this equality
   termwise by lem-weil-pbc-localization-universal-property, including its canonical
   rebracketing comparisons.
3. The unit normalization of lem-sfb-successive-derived-quotient-normalization and
   uniqueness in lem-weil-pbc-conjugate-iso-unit-equation identify the right conjugate
   of the specified scalar associator of det-sp-scalar-extension-functor with the
   restriction-composition comparison rho, at both U and Z.
4. Apply lem-weil-pbc-mate-pasting to both composites with beta. Their right conjugates
   are the two equal pastings of Step 2. Injectivity of def-weil-pbc-adjunction-conjugate
   gives the equality in the normalized left-adjoint coordinates.
5. Expand each prescribed e as S(r_A), then beta, then inverse r_B, using
   def-sp-reduction-direct-image-comparison. The two intermediate r_B factors cancel
   by functoriality. Naturality of r_C moves the scalar associator past its inverse;
   Step 4 replaces the middle three maps. Naturality of the specified scalar associator
   (det-sp-scalar-extension-functor) moves it past r_A, giving the direct e followed
   after alpha, exactly the displayed equation. This works for empty opens, unbounded
   objects and nonflat coefficient maps alike.
-/
theorem proEtaleOpenScalarCocycle
    (ℓ : ℕ) (hℓ : ℓ.Prime)
    {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    [Finite A] [Finite B] [Finite C]
    (hA : ∃ n : ℕ, (ℓ : A) ^ n = 0)
    (hB : ∃ n : ℕ, (ℓ : B) ^ n = 0)
    (hC : ∃ n : ℕ, (ℓ : C) ^ n = 0)
    (φ : A →+* B) (ψ : B →+* C)
    {U Z : Scheme.{u}} (j : U ⟶ Z) [IsOpenImmersion j]
    (M : proEtaleDerivedCategory U A) :
    (scalarExtensionFunctor_composition φ ψ Z).hom.app
        ((sfIntrinsicExtensionByZero j A).mapDerivedCategory.obj M) ≫
      (reductionOpenScalarIso (ψ.comp φ) j).hom.app M =
    (scalarExtensionFunctor ψ Z).map ((reductionOpenScalarIso φ j).hom.app M) ≫
      (reductionOpenScalarIso ψ j).hom.app ((scalarExtensionFunctor φ U).obj M) ≫
      (sfIntrinsicExtensionByZero j C).mapDerivedCategory.map
        ((scalarExtensionFunctor_composition φ ψ U).hom.app M) := by
  sorry

end AlgebraicGeometry.ProEtale
