/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.UpperShriek
public import WeilConjectures.SixFunctors.OpenClosed.Exact

/-!
# The supported localization triangle

For complementary immersions `i : Z ⟶ X` and `j : U ⟶ X` the two adjunction maps of the
exceptional formalism assemble into the *supported localization triangle*

`Ri_* Ri^! L ⟶ L ⟶ Rj_* j^* L ⟶ [1]`,

the derived counterpart of the open–closed short exact sequence
`AlgebraicGeometry.Etale.shortExact_openClosedShortComplex`. Its first term is
cohomology-with-supports along `Z`; applied to the closed–open pair `(s, j)` on the affine
line it is what computes the fundamental class of the zero section.

The triangle rests on the *closed-immersion unit*: for a closed immersion `i` the exceptional
adjunction unit `Q ⟶ Ri^! Ri_* Q` is an isomorphism, `Ri_!` being `Ri_*` because `i` is
proper.

## Main statements

- `AlgebraicGeometry.Etale.nonempty_iso_rightDerivedUpperShriek_rightDerivedLowerStar_obj`
- `AlgebraicGeometry.Etale.exists_distTriang_supportedLocalization`
-/

@[expose] public section

universe u' u

open CategoryTheory Limits Pretriangulated

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme Etale

namespace Etale

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [HasSmallSiteSheafify A] {U Z X : Scheme.{u}}

/-- Blueprint `sk-prop-sf-closed-unit`: Closed-immersion unit

For a closed immersion `i : Z ⟶ X` and `Q ∈ D^b_{ctf}(Z, Λ)` the exceptional adjunction unit

`Q ⟶ Ri^! Ri_* Q`

is an isomorphism, `Ri_!` being `Ri_*` because a closed immersion is proper. Equivalently,
`Ri_*` is fully faithful on the exceptional side, which is the derived counterpart of the full
faithfulness of `i_*` recorded in
`AlgebraicGeometry.Etale.fullyFaithfulLowerStar`. -/
theorem nonempty_iso_rightDerivedUpperShriek_rightDerivedLowerStar_obj (i : Z ⟶ X)
    [IsClosedImmersion i] [HasCompactification i]
    (Q : _root_.DerivedCategory (Sheaf Z.smallEtaleTopology A)) :
    Nonempty (Q ≅ (R(i)^![A]).obj ((R((i)_*[A])).obj Q)) :=
  sorry

/-- Blueprint `sk-prop-sf-localization`: Supported localization

**The supported localization triangle.** Let `i : Z ⟶ X` be a closed immersion with
complementary open `j : U ⟶ X`. For `L ∈ D^b_{ctf}(X, Λ)` the adjunction maps form a
distinguished triangle

`Ri_* Ri^! L ⟶ L ⟶ Rj_* j^* L ⟶ [1]`,

natural in `L`. It is the derived form of the open–closed sequence, obtained from the
open–closed triangle by the closed-immersion unit and the determination of a natural
transformation on a generating class. -/
theorem exists_distTriang_supportedLocalization (i : Z ⟶ X) (j : U ⟶ X) [IsClosedImmersion i]
    [HasCompactification i] [IsOpenImmersion j]
    (_hij : Set.range i.base = (Set.range j.base)ᶜ)
    (L : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)) :
    ∃ (u : (R((i)_*[A])).obj ((R(i)^![A]).obj L) ⟶ L)
      (v : L ⟶ (R((j)_*[A])).obj ((D((j)^*[A])).obj L))
      (w : (R((j)_*[A])).obj ((D((j)^*[A])).obj L) ⟶
        ((R((i)_*[A])).obj ((R(i)^![A]).obj L))⟦(1 : ℤ)⟧),
      Triangle.mk u v w ∈ distTriang _ :=
  sorry

end Etale

end AlgebraicGeometry
