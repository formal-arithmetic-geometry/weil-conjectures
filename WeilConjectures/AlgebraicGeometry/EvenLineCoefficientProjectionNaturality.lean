/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.EvenLineProductIntegrationMaps

/-! # Coordinate naturality of coefficient-first projection

Source: current blueprint, sec-smooth-purity/sk-prop-sp-composition,
prop-pur-affine-space-composition-law.proof, Steps 3--4.
(blueprint: lem-pur-even-line-coefficient-projection-naturality).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.EvenLineProduct
open AffineLinePurity AffineSpacePurity

/-- The actual forward coefficient-first projection intertwines coordinate actions.
Source: affine-space composition proof Step 4; coefficient extension argument in
lem-pur-even-line-product-integration-symmetry, Step 6
(blueprint: lem-pur-even-line-coefficient-projection-naturality).

Proof: apply compactification_projection_exchange_coherence to the Cartesian
square with upper map coordinate Y r sigma, lower map the identity of Y and
vertical map proj Y r. The coordinate permutation extends to the product of
projective lines compactification. Its comparison with the chosen compactification
intertwines projection by the finite compactification projection comparison on
the bounded Tate coefficient and ctf object K. Use the canonical identity
pullback and pullback compositor to identify the square's coefficient maps with
overPullback and coordinateTate. Insert the two natural signed symmetries that
define VectorIntegrationSite.projection. Naturality carries them past exchange
and compactification comparison, and puts K first on both sides. The resulting
square is exactly the displayed equation. No symmetry crosses K, and neither
invertibility of the coordinate action nor invariance of any trace is used. -/
theorem coefficientProjectionNaturality
    (P : WeilConjectures.PurityFiniteSetting.{u}) (Y : Scheme.{u})
    (aY : Y ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aY] [QuasiCompact aY]
    [IsSeparated aY]
    (r : ℕ) (K : D P Y)
    (hK : DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} (Ring P)) Y K)
    (σ : Equiv.Perm (Fin (r + 1))) :
    VectorIntegrationSite.projection (ModuleCat.{u + 1} (Ring P))
        (compactification Y r) (tate P Y r) K ≫ coefficientAction P Y aY r σ K hK =
      tensorHom (𝟙 K) (coordinateAction P Y aY r σ) ≫
        VectorIntegrationSite.projection (ModuleCat.{u + 1} (Ring P))
          (compactification Y r) (tate P Y r) K := by sorry

end AlgebraicGeometry.ProEtale.EvenLineProduct
