/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.Purity.Smooth.Conventions

/-!
# Co-projection for a closed immersion

For a closed immersion `i : Z ⟶ X`, an invertible tensor factor passes through `Ri^!` at the
cost of restricting it: `Ri^! (K ⊗^L L) ≅ Ri^! K ⊗^L Li^* L` (blueprint `sk-lem-coprojection`).
This is the input that moves twists through the exceptional inverse image of a zero section in
the model purity (`WeilConjectures.EtaleCohomology.Purity.Smooth.AffineSpace`) and in purity
for regular closed immersions (`WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersion`).

## Main statements

- `AlgebraicGeometry.Etale.nonempty_iso_rightDerivedUpperShriek_derivedTensor_of_isInvertible`
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] [HasTateTwist Λ] {X Z : Scheme.{u}}

/-- Blueprint `sk-lem-coprojection`: Co-projection for a closed immersion

For a closed immersion `i : Z ⟶ X`, a complex `K ∈ D^b_{ctf}(X, Λ)` and an object `L` of
`D^b_{ctf}(X, Λ)` that is *invertible*, the canonical co-projection

`Ri^! (K ⊗^L L) ≅ Ri^! K ⊗^L Li^* L`

is an isomorphism: an invertible tensor factor passes through `i^!` at the cost of restricting
it. Testing against an arbitrary `A ∈ D^b_{ctf}(Z, Λ)` and using `Ri_! = Ri_*`, the projection
formula for `Ri_*` and invertibility of `L`, the two Hom-functors agree naturally in `A`, so
Yoneda gives the isomorphism.

Taking `L = Λ_X(m)[2m]`, whose restriction is `Λ_Z(m)[2m]`, this reads
`Ri^!(K(m)[2m]) ≅ (Ri^! K)(m)[2m]`; taking `L = Lf^* B` for `B` invertible on `Y` and
`f' = f ∘ i` it reads `Ri^!(K ⊗ Lf^* B) ≅ Ri^! K ⊗ Lf'^* B`. -/
theorem nonempty_iso_rightDerivedUpperShriek_derivedTensor_of_isInvertible
    (i : Z ⟶ X) [IsClosedImmersion i] [HasCompactification i]
    (K L : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hK : DerivedCategory.boundedConstructibleFiniteTor Λ X K)
    (hLctf : DerivedCategory.boundedConstructibleFiniteTor Λ X L)
    (hL : DerivedCategory.isInvertible Λ X L) :
    Nonempty ((rightDerivedUpperShriek (ModuleCat.{u + 1} Λ) i).obj
        (((derivedTensor (ModuleCat.{u + 1} Λ) X).obj K).obj L) ≅
      ((derivedTensor (ModuleCat.{u + 1} Λ) Z).obj
          ((rightDerivedUpperShriek (ModuleCat.{u + 1} Λ) i).obj K)).obj
        ((L((i)^*[ModuleCat.{u + 1} Λ])).obj L)) :=
  sorry

end Etale

end AlgebraicGeometry
