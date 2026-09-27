/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Morphisms.RegularImmersion
public import WeilConjectures.EtaleCohomology.Purity.Smooth.Basic

/-!
# Purity for regular closed immersions

Purity for a regular closed immersion is *not* one of the five moves of the proof of smooth
purity: it is a consequence of smooth purity applied to the two structure morphisms, together
with the co-projection formula for `Ri^!`. The deformation to the normal cone is never applied
to a general regular immersion.

## Main statements

- `AlgebraicGeometry.Etale.nonempty_iso_rightDerivedUpperShriek_derivedTensor_of_isInvertible`
- `AlgebraicGeometry.Etale.nonempty_iso_dualizingComplex_of_isRegularImmersion`
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme Etale

namespace Etale

variable (Λ : Type (u + 1)) [CommRing Λ] {X Z : Scheme.{u}}

/-- Blueprint `sk-lem-coprojection`: Co-projection for a closed immersion

For a closed immersion `i : Z ⟶ X`, a complex `K ∈ D^b_{ctf}(X, Λ)` and an *invertible*
object `L` of `D^b_{ctf}(X, Λ)`, the canonical co-projection

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
    (_hK : DerivedCategory.boundedConstructibleFiniteTor Λ X K)
    (_hL : DerivedCategory.isInvertible Λ X L) :
    Nonempty ((Etale.rightDerivedUpperShriek (ModuleCat.{u + 1} Λ) i).obj
        (((Etale.derivedTensor (ModuleCat.{u + 1} Λ) X).obj K).obj L) ≅
      ((Etale.derivedTensor (ModuleCat.{u + 1} Λ) Z).obj
          ((Etale.rightDerivedUpperShriek (ModuleCat.{u + 1} Λ) i).obj K)).obj
        ((L((i)^*[ModuleCat.{u + 1} Λ])).obj L)) :=
  sorry

/-- Blueprint `sk-thm-regular`: Purity for regular closed immersions

**Purity for a regular closed immersion.** Let `i : Z ⟶ X` be a regular closed immersion of
pure codimension `c`, with `X` smooth over a perfect field `k` and `Z` regular. There is a
canonical isomorphism

`Ri^! Λ_X ≅ Λ_Z(-c)[-2c]`,

carrying `1` to the fundamental class `[Z ⊂ X]`, compatible with étale base change and with
exterior products.

By `sk-lem-regular-smooth` both structure morphisms `a_X` and `a_Z = a_X ∘ i` are smooth, of
relative dimensions `n` and `n - c`; smooth purity computes `ω_{a_X}` and `ω_{a_Z}`, and the
co-projection formula lets one divide the former into the latter. -/
theorem nonempty_iso_dualizingComplex_of_isRegularImmersion {k : Type u} [Field k]
    [PerfectField k] (c n : ℕ) (i : Z ⟶ X) [IsRegularImmersion c i] [HasCompactification i]
    (aX : X ⟶ Spec (.of k)) [IsSeparated aX] [SmoothOfRelativeDimension n aX]
    [HasCompactification aX] [SmoothOfRelativeDimension (n - c) (i ≫ aX)]
    [HasCompactification (i ≫ aX)] :
    Nonempty (dualizingComplex Λ i ≅ (twistShift Λ Z (-c : ℤ)).obj (constantComplex Λ Z)) :=
  sorry

end Etale

end AlgebraicGeometry
