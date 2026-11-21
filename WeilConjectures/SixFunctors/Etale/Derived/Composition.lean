/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition
public import WeilConjectures.SixFunctors.Etale.Derived.UpperShriek
public import WeilConjectures.SixFunctors.Etale.LowerShriek.Proper

/-!
# The composition law for `Rf_!` and its mate

Two statements of the six-functor bookkeeping that the purity chapter uses: the
identification `Rf_! ≅ Rf_*` for proper `f`, and the mate of the composition isomorphism,
`R(g ∘ f)^! ≅ Rf^! Rg^!`. The composition isomorphism `R(g ∘ f)_! ≅ Rf_! ⋙ Rg_!` itself is
`AlgebraicGeometry.Etale.nonempty_iso_rightDerivedLowerShriek_comp`, in
`WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition`.

The compactification-independence that makes `Rf_!` well defined is
`AlgebraicGeometry.Etale.rightDerivedLowerShriekOfCompactificationPlusComparison`
together with its identity and composition coherences; it is not restated here.

## Implementation details

On the unbounded derived categories the composition isomorphism `R(f ≫ g)_! ≅ Rf_! ⋙ Rg_!` is
only stated to exist, so the mate statement
`AlgebraicGeometry.Etale.exists_rightDerivedUpperShriekAdjunction_comp_eq` is existential in it;
being formal, it holds for every such isomorphism. The canonical composition isomorphism on the
bounded below derived categories, with its unit and associativity laws, is
`AlgebraicGeometry.Etale.rightDerivedLowerShriekPlusCompIso`.

The derived comparison map `Rf_! ⟶ Rf_*` for proper `f` is not constructed, so only the
existence of the derived isomorphism is recorded. The hypothesis `HasCompactification (f ≫ g)`
is redundant over a quasi-compact quasi-separated base, by Nagata's theorem; it is kept because
no composition instance for `HasCompactification` is available in general.

## Main statements

- `AlgebraicGeometry.Etale.nonempty_iso_rightDerivedLowerShriek_rightDerivedLowerStar`
- `AlgebraicGeometry.Etale.exists_rightDerivedUpperShriekAdjunction_comp_eq`
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
/-- **Proper coincidence.** For `f : X ⟶ Y` proper there is an isomorphism `Rf_! ≅ Rf_*`. -/
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
/-- For composable `f : X ⟶ Y` and `g : Y ⟶ S` admitting compactifications and torsion
coefficients, there is a composition isomorphism `e : R(f ≫ g)_! ≅ Rf_! ⋙ Rg_!` whose mate
`Rg^! ⋙ Rf^! ≅ R(f ≫ g)^!` under the adjunctions `Rf_! ⊣ Rf^!` on the unbounded derived
categories of the small étale sites carries the adjunction `R(f ≫ g)_! ⊣ R(f ≫ g)^!` to the
composite adjunction `Rf_! ⋙ Rg_! ⊣ Rg^! ⋙ Rf^!`: the unit and counit of the composite
adjunction are the pasted ones. -/
theorem exists_rightDerivedUpperShriekAdjunction_comp_eq (f : X ⟶ Y) (g : Y ⟶ S)
    [HasCompactification f] [HasCompactification g] [HasCompactification (f ≫ g)]
    [QuasiCompact (f ≫ g)] :
    ∃ e : R(f ≫ g)_![ModuleCat.{u + 1} Λ] ≅
        R(f)_![ModuleCat.{u + 1} Λ] ⋙ R(g)_![ModuleCat.{u + 1} Λ],
      ((rightDerivedUpperShriekAdjunction _ (f ≫ g)).ofNatIsoLeft e).ofNatIsoRight
        (conjugateIsoEquiv
          ((rightDerivedUpperShriekAdjunction _ f).comp (rightDerivedUpperShriekAdjunction _ g))
          (rightDerivedUpperShriekAdjunction _ (f ≫ g)) e).symm =
        (rightDerivedUpperShriekAdjunction _ f).comp (rightDerivedUpperShriekAdjunction _ g) := by
  obtain ⟨e⟩ := nonempty_iso_rightDerivedLowerShriek_comp Λ f g
  exact ⟨e, Adjunction.ofNatIsoLeft_ofNatIsoRight_conjugateIsoEquiv _ _ e⟩

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] in
/-- **The mate of the composition isomorphism.** For composable `f : X ⟶ Y` and `g : Y ⟶ S`
admitting compactifications and torsion coefficients, there is an isomorphism
`R(g ∘ f)^! ≅ Rf^! ∘ Rg^!`. -/
theorem nonempty_iso_rightDerivedUpperShriek_comp (f : X ⟶ Y) (g : Y ⟶ S)
    [HasCompactification f] [HasCompactification g] [HasCompactification (f ≫ g)]
    [QuasiCompact (f ≫ g)] :
    Nonempty (R(f ≫ g)^![Λ] ≅
      R(g)^![Λ] ⋙ R(f)^![Λ]) := by
  obtain ⟨e⟩ := nonempty_iso_rightDerivedLowerShriek_comp Λ f g
  exact ⟨Adjunction.rightAdjointUniq
    ((rightDerivedUpperShriekAdjunction _ (f ≫ g)).ofNatIsoLeft e)
    ((rightDerivedUpperShriekAdjunction _ f).comp (rightDerivedUpperShriekAdjunction _ g))⟩

end Etale

end AlgebraicGeometry
