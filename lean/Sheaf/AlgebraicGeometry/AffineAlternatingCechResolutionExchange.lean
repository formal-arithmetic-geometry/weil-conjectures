/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group R3
-/
module
public import Sheaf.AlgebraicGeometry.DerivedBaseChangeUnitCompatibility
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Sheaf.AlgebraicGeometry.AffinePushforwardBaseChange

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u w
open CategoryTheory Limits
namespace AlgebraicGeometry

/-- The ordinary exchange is invertible for the Cech resolution data.
Source: Stacks Project, Tags 02KG and 02KH; the affine intersection exchange
paragraph of `lem-pc-affine-alternating-cech-pinned-mate`.
(blueprint: lem-pc-s3-affine-alternating-cech-resolution-exchange).
Proof: Choose the representative C and its degreewise finite-product
identifications from hterms. For each affine W, separatedness makes W.ι affine,
and W.ι ≫ f is affine because its source and target are affine. The restriction
G|W is quasi-coherent. Apply affinePushforward_baseChange to the cartesian
squares for W.ι and for W.ι ≫ f. The vertical pasting identity for moduleBaseChangeMap,
obtained by transposing under the pullback adjunctions,
with the invertible exchange for W.ι, shows that ordinary exchange for f on
W.ι_*(G|W) is invertible. Both functors in the exchange are additive, so they
preserve finite biproducts, which are the finite products of these module
categories. Naturality transports the factor isomorphisms across each specified
product isomorphism for C.X k. Hence termwise exchange on C is an isomorphism
of complexes; its homotopy image and localization are isomorphisms. Finally
naturality across D ≅ quotient C transports the localized conclusion to D.
The empty finite product is a zero object and gives the same conclusion.
This makes no assertion for arbitrary complexes without hterms. -/
theorem affineAlternatingCech_resolution_exchange
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {A B : CommRingCat.{u}} {X : Scheme.{u}} (f : X ⟶ Spec A)
    [IsSeparated f] (g : Spec B ⟶ Spec A)
    [(Scheme.Modules.tensorPullback g).Additive]
    [(Scheme.Modules.tensorPullback (pullback.fst f g)).Additive]
    (G : X.Modules) [SheafOfModules.IsQuasicoherent.{u} G]
    (D : HomotopyCategory
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) (ComplexShape.up ℤ))
    (hterms : ∃ C : CochainComplex
          (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ,
        Nonempty (D ≅ (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj C) ∧
        ∀ k : ℤ, ∃ (n : ℕ) (W : Fin n → X.Opens),
          (∀ j, IsAffineOpen (W j)) ∧
          Nonempty (C.X k ≅ ∏ᶜ fun j : Fin n ↦
            (Scheme.Modules.pushforward (W j).ι).obj (G.restrict (W j).ι))) :
    IsIso ((DerivedCategory.Qh (C := SheafOfModules.{u}
      (moduleRings (Spec B).toRingedSpace))).map
      ((moduleHomotopyBaseChange f (pullback.snd f g) g (pullback.fst f g)
        pullback.condition).app D)) := by sorry
end AlgebraicGeometry
