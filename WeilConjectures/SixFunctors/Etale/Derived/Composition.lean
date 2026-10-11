/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula
public import WeilConjectures.SixFunctors.Etale.Derived.UpperShriek
public import WeilConjectures.SixFunctors.Etale.LowerShriek.Proper

/-!
# The composition law for `Rf_!` and its mate

Two statements of the six-functor bookkeeping that the purity chapter uses: the
identification `Rf_! ≅ Rf_*` for proper `f`, and the mate of the composition isomorphism,
`R(g ∘ f)^! ≅ Rf^! Rg^!`. The composition isomorphism `R(g ∘ f)_! ≅ Rf_! ⋙ Rg_!` itself is
`AlgebraicGeometry.Etale.nonempty_iso_rightDerivedLowerShriek_comp`, in
`WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula`.

The compactification-independence that makes `Rf_!` well defined is already in the
repository, as
`AlgebraicGeometry.Etale.rightDerivedLowerShriekOfCompactificationPlusComparison`
together with its identity and composition coherences; it is not restated here.

## Implementation notes

Each statement below records only the *existence* of the isomorphism it names. The unit and
associativity coherences of `sk-thm-sf-comp-composition`, and the assertion of `sk-lem-sf-mate`
that `R(gf)^! ≅ Rf^! Rg^!` is the *mate* of the composition isomorphism, cannot be phrased in
that form; they need the isomorphism as a `def`, which in turn needs the comparison maps of
the framework chapter. This is the same gap as the TODO already recorded in
`WeilConjectures.SixFunctors.Etale.Derived.UpperShriek`.

## Main statements

- `AlgebraicGeometry.Etale.nonempty_iso_rightDerivedLowerShriek_rightDerivedLowerStar`
- `AlgebraicGeometry.Etale.nonempty_iso_rightDerivedUpperShriek_comp`
-/

@[expose] public section

universe u' u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [HasSmallSiteSheafify A] {X Y S : Scheme.{u}}

omit [HasSmallSiteSheafify A] in
/-- Blueprint `sk-prop-sf-comp-proper`: Proper coincidence

**Proper coincidence.** For `f : X ⟶ Y` proper the identity is a compactification of `f`, and
the resulting canonical identification

`Rf_! ≅ Rf_*`

is independent of the compactification.

At the level of sheaves this is `AlgebraicGeometry.Etale.isIso_lowerShriekToLowerStar`, which
states that the *canonical comparison* `f_! ⟶ f_*` is an isomorphism; the derived comparison
map has not been constructed, so only the existence of the derived isomorphism is recorded
here. -/
theorem nonempty_iso_rightDerivedLowerShriek_rightDerivedLowerStar (f : X ⟶ Y)
    [HasCompactification f] [IsProper f] :
    Nonempty (R(f)_![A] ≅ R((f)_*[A])) := by
  let c := HasCompactification.compactification f
  -- the open immersion of the compactification is proper, so it has closed range and `j_! ≅ j_*`
  have := Etale.isIso_openImmersionLowerShriekToLowerStar_of_isClosed_range A c.i
    (c.isClopen_range_openImmersion inferInstance).isClosed
  let ι := asIso (Etale.openImmersionLowerShriekToLowerStar A c.i)
  have : PreservesFiniteColimits (c.i)_*[A] := preservesFiniteColimits_of_natIso ι
  have : PreservesFiniteLimits (c.i)_*[A] := preservesFiniteLimits_of_natIso ι
  exact ⟨Functor.isoWhiskerRight (Functor.mapDerivedCategoryNatIso ι) R((c.g)_*[A]) ≪≫
    Functor.isoWhiskerRight ((c.i)_*[A].rightDerivedFunctorIsoMapDerivedCategory).symm
      R((c.g)_*[A]) ≪≫ rightDerivedLowerStarComp A c.i c.g ≪≫
    rightDerivedLowerStarCongr A c.comm.symm⟩

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] in
/-- Blueprint `sk-lem-sf-mate`: Mate calculus for a pasted adjunction

**The mate of the composition isomorphism.** For composable `f : X ⟶ Y` and `g : Y ⟶ S` and
torsion coefficients,

```
  R(f ≫ g)_! ≅ Rf_! ⋙ Rg_!           (left adjoints, sk-thm-sf-comp-composition)
        ⊣              ⊣
  R(f ≫ g)^! ≅ Rg^! ⋙ Rf^!           (right adjoints, the mate)
```

the mate of the composition isomorphism is an isomorphism `R(g ∘ f)^! ≅ Rf^! ∘ Rg^!`: right
adjoints of isomorphic functors are isomorphic, and the right adjoint of a composite is the
composite of the right adjoints. The composition isomorphism of the lower shrieks is
`AlgebraicGeometry.Etale.nonempty_iso_rightDerivedLowerShriek_comp`, which needs torsion
coefficients.

This is clause (b) of `sk-lem-sf-mate` in its étale form, for morphisms admitting a
compactification (`sk-prop-sf-existence`(a)). Clause (a), the pro-étale ambient form, is not
formalised. The hypothesis `HasCompactification (f ≫ g)` is redundant over a quasi-compact
quasi-separated base, by Nagata's theorem; it is kept because no composition instance for
`HasCompactification` is available in general. -/
theorem nonempty_iso_rightDerivedUpperShriek_comp (f : X ⟶ Y) (g : Y ⟶ S)
    [HasCompactification f] [HasCompactification g] [HasCompactification (f ≫ g)] :
    Nonempty (R(f ≫ g)^![ModuleCat.{u + 1} Λ] ≅
      R(g)^![ModuleCat.{u + 1} Λ] ⋙ R(f)^![ModuleCat.{u + 1} Λ]) := by
  obtain ⟨e⟩ := nonempty_iso_rightDerivedLowerShriek_comp Λ f g
  exact ⟨Adjunction.rightAdjointUniq
    ((rightDerivedUpperShriekAdjunction _ (f ≫ g)).ofNatIsoLeft e)
    ((rightDerivedUpperShriekAdjunction _ f).comp (rightDerivedUpperShriekAdjunction _ g))⟩

end Etale

end AlgebraicGeometry
