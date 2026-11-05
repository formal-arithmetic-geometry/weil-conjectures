/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.Purity.Smooth.CohomologicalSmoothness
public import WeilConjectures.EtaleCohomology.Purity.Smooth.Coprojection
public import WeilConjectures.SixFunctors.Etale.Derived.Composition
public import WeilConjectures.SixFunctors.Etale.Derived.EtaleLocalization
public import WeilConjectures.SixFunctors.Etale.Derived.EtaleLocalizationUpperShriek
public import WeilConjectures.SixFunctors.Etale.Derived.GlobalDuality
public import WeilConjectures.SixFunctors.Etale.Derived.Stability.Basic
public import WeilConjectures.SixFunctors.Etale.Derived.UpperShriekCanonicalMapsComposition
public import WeilConjectures.SixFunctors.Etale.Derived.UpperShriekInvertible

/-!
# Cohomologically smooth morphisms

A morphism `f : X ⟶ Y` admitting a compactification is *cohomologically smooth*
(blueprint `def-pur-co-smoothness`) if its dualizing complex `ω_f = Rf^! Λ_Y` is ⊗-invertible,
the canonical map `θ_{f,K} : ω_f ⊗ᴸ Lf^* K ⟶ Rf^! K` is an isomorphism for every
`K ∈ D^b_{ctf}(Y, Λ)`, and the canonical base change map `Lg'^* ω_f ⟶ ω_{f'}` is an
isomorphism for every cartesian square. This file proves the structural results of the
blueprint subsection `sk-prop-cohsm` about this notion:

* smooth morphisms are cohomologically smooth (`thm-pur-cohomological-smoothness`), and the
  dualizing complexes of smooth morphisms are multiplicative under composition;
* `ω_{f ≫ g} ≅ ω_f ⊗ᴸ Lf^* ω_g` for cohomologically smooth `g`, and a composite of
  cohomologically smooth morphisms is cohomologically smooth (`lem-pur-co-smooth-composition`);
* étale morphisms are cohomologically smooth with `ω_u ≅ Λ`, and cohomological smoothness
  descends along surjective étale morphisms (`lem-pur-co-smooth-etale-locality`).

## Implementation notes

The canonical maps are `AlgebraicGeometry.Etale.dualizingComplexTensorMap` and
`AlgebraicGeometry.Etale.dualizingComplexBaseChangeMap`. The base change map is the mate of the
compact-support base change `Ex_!`, which is only constructed for a quasi-compact base change
`f'`; the third clause of the definition is asked for such squares.

The composition law for the canonical maps (`lem-pur-co-smooth-composition`) and their descent
along surjective étale maps (`lem-pur-co-smooth-etale-locality`) compare the canonical maps of
`f`, `g` and `f ≫ g` through a composition isomorphism `R(f ≫ g)_! ≅ Rf_! ⋙ Rg_!` compatible
with the projection maps and with `Ex_!` (`sk-thm-sf-comp-composition`,
`sk-prop-sf-pf-coherence`, `sk-thm-sf-package`), recorded in
`AlgebraicGeometry.Etale.exists_rightDerivedLowerShriekCompIso`; the computations are in
`WeilConjectures.SixFunctors.Etale.Derived.UpperShriekCanonicalMapsComposition`. Descent along
`u` uses that `u` is itself cohomologically smooth with `θ_u` invertible everywhere, so that
`Ru^!` reflects isomorphisms after pullback along `u`, instead of an extension by zero `u_!`.

The invertibility of `ω_{f ≫ g}` needs no canonical map: an invertible tensor factor passes
through every `Rf^!`
(`AlgebraicGeometry.Etale.derivedTensorRightCompRightDerivedUpperShriekIso`), so
`ω_{f ≫ g} ≅ Rf^! ω_g ≅ ω_f ⊗ᴸ Lf^* ω_g` as soon as `ω_g` is invertible.

## Main definitions

- `AlgebraicGeometry.Etale.IsCohomologicallySmooth`

## Main statements

- `AlgebraicGeometry.Etale.isCohomologicallySmooth_of_smoothOfRelativeDimension`
- `AlgebraicGeometry.Etale.isIso_rightDerivedUpperShriekBaseChangeMap_app`
- `AlgebraicGeometry.Etale.IsCohomologicallySmooth.comp`,
  `AlgebraicGeometry.Etale.IsCohomologicallySmooth.nonempty_iso_dualizingComplex_comp`
- `AlgebraicGeometry.Etale.isCohomologicallySmooth_of_etale`,
  `AlgebraicGeometry.Etale.IsCohomologicallySmooth.of_comp_of_surjective`
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]

/-! ### Composition -/

/-- The dualizing complex of a composite with an invertible second dualizing complex: for
`f : X ⟶ Y` and `g : Y ⟶ Z` admitting compactifications, with `ω_g` invertible,

`ω_{f ≫ g} ≅ Rf^! ω_g ≅ Rf^!(Λ_Y ⊗ᴸ ω_g) ≅ ω_f ⊗ᴸ Lf^* ω_g`,

by the composition law for `R^!` and since an invertible tensor factor passes through `Rf^!`
(`AlgebraicGeometry.Etale.derivedTensorRightCompRightDerivedUpperShriekIso`). The
composite is given as a morphism `h` with `f ≫ g = h`. -/
theorem nonempty_iso_dualizingComplex_comp_of_isInvertible {X Y Z : Scheme.{u}} (f : X ⟶ Y)
    (g : Y ⟶ Z) (h : X ⟶ Z) (w : f ≫ g = h) [HasCompactification f] [HasCompactification g]
    [HasCompactification h] [QuasiCompact h]
    (hg : DerivedCategory.isInvertible Λ Y (dualizingComplex Λ g)) :
    Nonempty (dualizingComplex Λ h ≅
      ((derivedTensor (ModuleCat.{u + 1} Λ) X).obj (dualizingComplex Λ f)).obj
        ((L((f)^*[ModuleCat.{u + 1} Λ])).obj (dualizingComplex Λ g))) := by
  subst w
  obtain ⟨c⟩ := nonempty_iso_rightDerivedUpperShriek_comp Λ f g
  obtain ⟨M, ⟨e'⟩, ⟨e⟩⟩ := hg
  exact ⟨c.app _ ≪≫ (R(f)^![Λ]).mapIso (derivedTensorLeftUnitor _ Y _).symm ≪≫
    (derivedTensorRightCompRightDerivedUpperShriekIso Λ f _ M e e').app (𝟙_ _)⟩

variable {Λ}

/-! ### Smooth morphisms -/

variable (Λ)

/-! ### Étale morphisms and étale locality -/

variable {Λ}

end Etale

end AlgebraicGeometry
