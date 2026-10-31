/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.EvenLineProductIntegrationMaps

/-! # Coordinate action in the concrete tensor-power coordinates

Source: current blueprint, sec-smooth-purity/sk-prop-sp-composition,
prop-pur-affine-space-composition-law.proof, Steps 3--4.
(blueprint: lem-pur-even-line-coordinate-intertwining).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.EvenLineProduct
open AffineLinePurity AffineSpacePurity

/-- The geometric coordinate action intertwines the specified kappa and signed permutations.
Source: affine-space composition proof Steps 3--4; the adjacent-swap argument in
lem-pur-even-line-product-integration-symmetry, Steps 2--4
(blueprint: lem-pur-even-line-coordinate-intertwining).

Proof: use binaryProductNormalization to change between any binary block product
and the left-associated tensor power. On two adjacent line factors apply the
finite forward-product symmetry theorem. Its signed external interchange agrees
with the coefficient identification coordinateTate: a finite Kummer line is
locally free of rank one, its degree-zero self-interchange is the identity, and
its shifted representative lies in degree -2, so the Koszul coefficient is
(-1)^4=1. Pullback/tensor and shift-additivity comparisons transport this equality
to the displayed Tate coefficients. The actual scheme coordinate interchange
extends to the product of projective lines, and the compactification comparisons
therefore give exactly coordinateAction. Naturality carries an adjacent swap
through unchanged outer factors. Decompose sigma using decomposeOption and
finSuccEquivLast, as in permutation. Induct on the number of factors; each last
factor transposition is the conjugate of lastAdjacent by the preceding lastSwap.
Associativity from binary normalization and the signed braiding hexagon identify
these conjugations with the definitions. Thus the recursive geometric word
intertwines kappa with precisely the stated permutation, including the identity
one-factor case. -/
theorem coordinateIntertwining
    (P : WeilConjectures.PurityFiniteSetting.{u}) (Y : Scheme.{u})
    (aY : Y ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aY] [QuasiCompact aY]
    [IsSeparated aY]
    (hU : Nonempty (integral P Y 0 ≅ 𝟙_ (D P Y)))
    (hV : ∀ r : ℕ, DerivedCategory.constructibleFiniteTor
      (ModuleCat.{u + 1} (Ring P)) Y (integral P Y r))
    (hprod : ∀ r : ℕ, IsIso (forward P Y aY r 0))
    (r : ℕ) (σ : Equiv.Perm (Fin (r + 1))) :
    coordinateAction P Y aY r σ ≫ (kappa P Y aY hprod r).hom =
      (kappa P Y aY hprod r).hom ≫
        (permutation (signedSymmetry P Y) (integral P Y 0) r σ).hom := by sorry

end AlgebraicGeometry.ProEtale.EvenLineProduct
