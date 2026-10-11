/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.Purity.Smooth.Basic
public import WeilConjectures.SixFunctors.Etale.Derived.Composition
public import WeilConjectures.SixFunctors.Etale.Derived.EtaleLocalization
public import WeilConjectures.SixFunctors.Etale.Derived.Stability.Basic
public import WeilConjectures.SixFunctors.Etale.Derived.UpperShriekCanonicalMaps
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
* `ω_{f ≫ g} ≅ ω_f ⊗ᴸ Lf^* ω_g` for cohomologically smooth `g`, and the dualizing complex of a
  composite of cohomologically smooth morphisms is invertible
  (`lem-pur-co-smooth-composition`);
* étale morphisms are cohomologically smooth with `ω_u ≅ Λ`
  (`lem-pur-co-smooth-etale-locality`).

## Implementation notes

The canonical maps are `AlgebraicGeometry.Etale.dualizingComplexTensorMap` and
`AlgebraicGeometry.Etale.dualizingComplexBaseChangeMap`. The base change map is the mate of the
compact-support base change `Ex_!`, which is only constructed for a quasi-compact base change
`f'`; the third clause of the definition is asked for such squares.

The composition law for the canonical maps (`lem-pur-co-smooth-composition`) and their descent
along surjective étale maps (`lem-pur-co-smooth-etale-locality`) compare the canonical maps of
`f`, `g` and `f ≫ g`. This needs a canonical composition isomorphism
`R(f ≫ g)_! ≅ Rf_! ⋙ Rg_!` compatible with the projection maps and with `Ex_!`
(`sk-thm-sf-comp-composition`, `sk-prop-sf-pf-coherence`), and, for descent, the canonical
étale localization `Lu^* Rf^! ≅ R(u ≫ f)^!` (`lem-amb-etale-adjoint-locality`), the mate of the
composition isomorphism with `Ru_! ⊣ Lu^*`. None of these is available in the library: even
the existence of a composition isomorphism for `R_!`
(`AlgebraicGeometry.Etale.nonempty_iso_rightDerivedLowerShriek_comp`) is not proved there, and
the extension by zero `u_!` along an étale `u` that is not an open immersion is not defined.
These parts are left as `sorry`.

The invertibility of `ω_{f ≫ g}` needs no canonical map: an invertible tensor factor passes
through every `Rf^!`
(`AlgebraicGeometry.Etale.nonempty_iso_rightDerivedUpperShriek_comp_derivedTensorRight`), so
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

/-- Blueprint `def-pur-co-smoothness`: Cohomological smoothness.

A morphism `f : X ⟶ Y` admitting a compactification is *cohomologically smooth* if
1. its dualizing complex `ω_f = Rf^! Λ_Y` is ⊗-invertible;
2. for every `K ∈ D^b_{ctf}(Y, Λ)`, the canonical map `θ_{f,K} : ω_f ⊗ᴸ Lf^* K ⟶ Rf^! K`
   (`AlgebraicGeometry.Etale.dualizingComplexTensorMap`, the mate of the projection formula) is
   an isomorphism;
3. for every cartesian square
   ```
     X' --g'--> X
     |          |
     f'         f
     ↓          ↓
     Y' --g---> Y
   ```
   with `f'` quasi-compact and admitting a compactification, the canonical base change map
   `Lg'^* ω_f ⟶ ω_{f'}` (`AlgebraicGeometry.Etale.dualizingComplexBaseChangeMap`) is an
   isomorphism.

The blueprint asks for clause 3 for every cartesian square; the base change map, the mate of the
compact-support base change `Ex_!`, is only constructed for quasi-compact `f'`. The blueprint
writes the tensor factors of clause 2 in the other order. -/
structure IsCohomologicallySmooth {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f] :
    Prop where
  isInvertible_dualizingComplex :
    DerivedCategory.isInvertible Λ X (dualizingComplex (ModuleCat.{u + 1} Λ) f)
  isIso_dualizingComplexTensorMap
    (K : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hK : DerivedCategory.boundedConstructibleFiniteTor Λ Y K) :
    IsIso (dualizingComplexTensorMap Λ f K)
  isIso_dualizingComplexBaseChangeMap {X' Y' : Scheme.{u}} {g : Y' ⟶ Y} {f' : X' ⟶ Y'}
    {g' : X' ⟶ X} (sq : IsPullback g' f' f g) [HasCompactification f'] [QuasiCompact f'] :
    IsIso (dualizingComplexBaseChangeMap Λ sq)

variable {Λ} in
/-- The tensor formula of a cohomologically smooth morphism: `ω_f ⊗ᴸ Lf^* K ≅ Rf^! K` for
`K ∈ D^b_{ctf}(Y, Λ)`, by the canonical map. -/
theorem IsCohomologicallySmooth.nonempty_iso_rightDerivedUpperShriek_obj {X Y : Scheme.{u}}
    {f : X ⟶ Y} [HasCompactification f] (hf : IsCohomologicallySmooth Λ f)
    (K : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hK : DerivedCategory.boundedConstructibleFiniteTor Λ Y K) :
    Nonempty (((derivedTensor (ModuleCat.{u + 1} Λ) X).obj
        (dualizingComplex (ModuleCat.{u + 1} Λ) f)).obj ((L((f)^*[ModuleCat.{u + 1} Λ])).obj K) ≅
      (R(f)^![ModuleCat.{u + 1} Λ]).obj K) :=
  have := hf.isIso_dualizingComplexTensorMap K hK
  ⟨asIso (dualizingComplexTensorMap Λ f K)⟩

omit [Finite Λ] in
/-- The unit `Λ_X` of `D(X_ét, Λ)` is invertible. -/
lemma DerivedCategory.isInvertible_constantComplex (X : Scheme.{u}) :
    DerivedCategory.isInvertible Λ X (constantComplex Λ X) :=
  ⟨constantComplex Λ X, ⟨derivedTensorLeftUnitor _ X _⟩, ⟨derivedTensorLeftUnitor _ X _⟩⟩

/-! ### Composition -/

/-- The dualizing complex of a composite with an invertible second dualizing complex: for
`f : X ⟶ Y` and `g : Y ⟶ Z` admitting compactifications, with `ω_g` invertible,

`ω_{f ≫ g} ≅ Rf^! ω_g ≅ Rf^!(Λ_Y ⊗ᴸ ω_g) ≅ ω_f ⊗ᴸ Lf^* ω_g`,

by the composition law for `R^!` and since an invertible tensor factor passes through `Rf^!`
(`AlgebraicGeometry.Etale.nonempty_iso_rightDerivedUpperShriek_comp_derivedTensorRight`). The
composite is given as a morphism `h` with `f ≫ g = h`. -/
theorem nonempty_iso_dualizingComplex_comp_of_isInvertible {X Y Z : Scheme.{u}} (f : X ⟶ Y)
    (g : Y ⟶ Z) (h : X ⟶ Z) (w : f ≫ g = h) [HasCompactification f] [HasCompactification g]
    [HasCompactification h]
    (hg : DerivedCategory.isInvertible Λ Y (dualizingComplex (ModuleCat.{u + 1} Λ) g)) :
    Nonempty (dualizingComplex (ModuleCat.{u + 1} Λ) h ≅
      ((derivedTensor (ModuleCat.{u + 1} Λ) X).obj (dualizingComplex (ModuleCat.{u + 1} Λ) f)).obj
        ((L((f)^*[ModuleCat.{u + 1} Λ])).obj (dualizingComplex (ModuleCat.{u + 1} Λ) g))) := by
  subst w
  obtain ⟨c⟩ := nonempty_iso_rightDerivedUpperShriek_comp Λ f g
  obtain ⟨t⟩ := nonempty_iso_rightDerivedUpperShriek_comp_derivedTensorRight Λ f hg
  exact ⟨c.app _ ≪≫ (R(f)^![ModuleCat.{u + 1} Λ]).mapIso (derivedTensorLeftUnitor _ Y _).symm ≪≫
    t.app (𝟙_ _)⟩

variable {Λ}

/-- Blueprint `lem-pur-co-smooth-composition`: Composition.

For cohomologically smooth `g : Y ⟶ Z` and any `f : X ⟶ Y` admitting a compactification,
`ω_{f ≫ g} ≅ ω_f ⊗ᴸ Lf^* ω_g`. -/
theorem IsCohomologicallySmooth.nonempty_iso_dualizingComplex_comp {X Y Z : Scheme.{u}}
    {f : X ⟶ Y} {g : Y ⟶ Z} [HasCompactification f] [HasCompactification g]
    [HasCompactification (f ≫ g)] (hg : IsCohomologicallySmooth Λ g) :
    Nonempty (dualizingComplex (ModuleCat.{u + 1} Λ) (f ≫ g) ≅
      ((derivedTensor (ModuleCat.{u + 1} Λ) X).obj (dualizingComplex (ModuleCat.{u + 1} Λ) f)).obj
        ((L((f)^*[ModuleCat.{u + 1} Λ])).obj (dualizingComplex (ModuleCat.{u + 1} Λ) g))) :=
  nonempty_iso_dualizingComplex_comp_of_isInvertible Λ f g _ rfl hg.isInvertible_dualizingComplex

/-- Blueprint `lem-pur-co-smooth-composition`: Composition.

If `f : X ⟶ Y` and `g : Y ⟶ Z` are cohomologically smooth, the dualizing complex
`ω_{f ≫ g} ≅ ω_f ⊗ᴸ Lf^* ω_g` of `f ≫ g` is invertible, as a tensor product of invertible
objects. -/
theorem IsCohomologicallySmooth.isInvertible_dualizingComplex_comp {X Y Z : Scheme.{u}}
    {f : X ⟶ Y} {g : Y ⟶ Z} [HasCompactification f] [HasCompactification g]
    [HasCompactification (f ≫ g)] (hf : IsCohomologicallySmooth Λ f)
    (hg : IsCohomologicallySmooth Λ g) :
    DerivedCategory.isInvertible Λ X (dualizingComplex (ModuleCat.{u + 1} Λ) (f ≫ g)) := by
  obtain ⟨e⟩ := hg.nonempty_iso_dualizingComplex_comp (f := f)
  exact .of_iso e.symm (hf.isInvertible_dualizingComplex.derivedTensor
    (hg.isInvertible_dualizingComplex.leftDerivedUpperStar f))

/-- Blueprint `lem-pur-co-smooth-composition`: Composition.

If `f : X ⟶ Y` and `g : Y ⟶ Z` are cohomologically smooth, then so is `f ≫ g`:
* `ω_{f ≫ g} ≅ ω_f ⊗ᴸ Lf^* ω_g` is invertible
  (`AlgebraicGeometry.Etale.IsCohomologicallySmooth.isInvertible_dualizingComplex_comp`);
* the blueprint factors `θ_{f ≫ g, K}` through `θ_{f, Lg^* K}` and `Rf^! θ_{g, K}`, and the base
  change map of `f ≫ g` through those of `f` and `g`. Both factorizations are identities between
  canonical maps built from a canonical composition isomorphism `R(f ≫ g)_! ≅ Rf_! ⋙ Rg_!`
  compatible with the projection maps and with `Ex_!` (`sk-thm-sf-comp-composition`,
  `sk-prop-sf-pf-coherence`), which is not available in the library (see the module
  docstring); these two clauses are left as `sorry`. -/
theorem IsCohomologicallySmooth.comp {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    [HasCompactification f] [HasCompactification g] [HasCompactification (f ≫ g)]
    (hf : IsCohomologicallySmooth Λ f) (hg : IsCohomologicallySmooth Λ g) :
    IsCohomologicallySmooth Λ (f ≫ g) where
  isInvertible_dualizingComplex := hf.isInvertible_dualizingComplex_comp hg
  isIso_dualizingComplexTensorMap K hK := sorry
  isIso_dualizingComplexBaseChangeMap sq _ _ := sorry

/-! ### Smooth morphisms -/

variable (Λ)

/-- Blueprint `lem-pur-smb-extraordinary`: Smooth base change for the exceptional inverse image.

For a cartesian square

```
  X' --u--> X
  |          |
  f'         f
  ↓          ↓
  Y' --v--> Y
```

in which `f` is smooth of pure relative dimension `d`, `v` is arbitrary and `f'` is quasi-compact
and admits a compactification, and every `K ∈ D^b_{ctf}(Y, Λ)`, the canonical comparison
`Lu^* Rf^! K ⟶ Rf'^! Lv^* K` (`AlgebraicGeometry.Etale.rightDerivedUpperShriekBaseChangeMap`)
is an isomorphism. This is the component at `K` of smooth base change for `R^!`
(`AlgebraicGeometry.Etale.isIso_rightDerivedUpperShriekBaseChangeMap_of_smoothOfRelativeDimension`),
which holds for every `K`. -/
theorem isIso_rightDerivedUpperShriekBaseChangeMap_app
    {X Y X' Y' : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f] (d : ℕ)
    [SmoothOfRelativeDimension d f] [HasInvertibleExponent Λ X] {v : Y' ⟶ Y} {f' : X' ⟶ Y'}
    {u : X' ⟶ X} (sq : IsPullback u f' f v) [HasCompactification f'] [QuasiCompact f']
    (K : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (_hK : DerivedCategory.boundedConstructibleFiniteTor Λ Y K) :
    IsIso ((rightDerivedUpperShriekBaseChangeMap Λ sq).app K) :=
  have := isIso_rightDerivedUpperShriekBaseChangeMap_of_smoothOfRelativeDimension Λ f d sq
  inferInstance

/-- Blueprint `lem-pur-smb-extraordinary`: Smooth base change for the exceptional inverse image.

The form of `AlgebraicGeometry.Etale.isIso_rightDerivedUpperShriekBaseChangeMap_app`
for a base change `f'` that need not be quasi-compact, for which the canonical comparison is not
constructed: `Lu^* Rf^! K ≅ Rf'^! Lv^* K`. This is the component at `K` of
`AlgebraicGeometry.Etale.nonempty_iso_leftDerivedUpperStar_comp_rightDerivedUpperShriek`. -/
theorem nonempty_iso_leftDerivedUpperStar_obj_rightDerivedUpperShriek_obj {X Y X' Y' : Scheme.{u}}
    (f : X ⟶ Y) [HasCompactification f] (d : ℕ) [SmoothOfRelativeDimension d f]
    [HasInvertibleExponent Λ X] {v : Y' ⟶ Y} {f' : X' ⟶ Y'} {u : X' ⟶ X}
    (sq : IsPullback u f' f v) [HasCompactification f']
    (K : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (_hK : DerivedCategory.boundedConstructibleFiniteTor Λ Y K) :
    Nonempty ((L((u)^*[ModuleCat.{u + 1} Λ])).obj ((R(f)^![ModuleCat.{u + 1} Λ]).obj K) ≅
      (R(f')^![ModuleCat.{u + 1} Λ]).obj ((L((v)^*[ModuleCat.{u + 1} Λ])).obj K)) := by
  obtain ⟨e⟩ := nonempty_iso_leftDerivedUpperStar_comp_rightDerivedUpperShriek Λ (d := d) f sq
  exact ⟨e.app K⟩

/-- Blueprint `thm-pur-cohomological-smoothness`: Cohomological smoothness of smooth morphisms.

A smooth morphism `f : X ⟶ Y` of pure relative dimension `d` admitting a compactification, with
the exponent of `Λ` invertible on `X`, is cohomologically smooth: `ω_f` is invertible
(`AlgebraicGeometry.Etale.isInvertible_dualizingComplex`), the canonical tensor map is an
isomorphism
(`AlgebraicGeometry.Etale.isIso_dualizingComplexTensorMap_of_smoothOfRelativeDimension`) and the
canonical base change map is an isomorphism, by smooth base change for `R^!`
(`AlgebraicGeometry.Etale.isIso_rightDerivedUpperShriekBaseChangeMap_of_smoothOfRelativeDimension`).
The compatibility with composition is
`AlgebraicGeometry.Etale.nonempty_iso_dualizingComplex_comp_of_smoothOfRelativeDimension`. -/
theorem isCohomologicallySmooth_of_smoothOfRelativeDimension {X Y : Scheme.{u}} (f : X ⟶ Y)
    [HasCompactification f] (d : ℕ) [SmoothOfRelativeDimension d f]
    [HasInvertibleExponent Λ X] : IsCohomologicallySmooth Λ f where
  isInvertible_dualizingComplex := isInvertible_dualizingComplex Λ (d := d) f
  isIso_dualizingComplexTensorMap K _ :=
    isIso_dualizingComplexTensorMap_of_smoothOfRelativeDimension Λ (d := d) f K
  isIso_dualizingComplexBaseChangeMap sq _ _ := by
    have := isIso_rightDerivedUpperShriekBaseChangeMap_of_smoothOfRelativeDimension Λ f d sq
    rw [isIso_dualizingComplexBaseChangeMap_iff]
    infer_instance

/-- Blueprint `thm-pur-cohomological-smoothness`: Cohomological smoothness of smooth morphisms.

*Composition.* For smooth `f : X ⟶ Y` and `g : Y ⟶ Z`, `ω_{f ≫ g} ≅ ω_f ⊗ᴸ Lf^* ω_g`. Only the
invertibility of `ω_g` is used. -/
theorem nonempty_iso_dualizingComplex_comp_of_smoothOfRelativeDimension {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) [HasCompactification f] [HasCompactification g]
    [HasCompactification (f ≫ g)] (e : ℕ) [SmoothOfRelativeDimension e g]
    [HasInvertibleExponent Λ Y] :
    Nonempty (dualizingComplex (ModuleCat.{u + 1} Λ) (f ≫ g) ≅
      ((derivedTensor (ModuleCat.{u + 1} Λ) X).obj (dualizingComplex (ModuleCat.{u + 1} Λ) f)).obj
        ((L((f)^*[ModuleCat.{u + 1} Λ])).obj (dualizingComplex (ModuleCat.{u + 1} Λ) g))) :=
  nonempty_iso_dualizingComplex_comp_of_isInvertible Λ f g _ rfl
    (isInvertible_dualizingComplex Λ (d := e) g)

/-! ### Étale morphisms and étale locality -/

/-- For a separated quasi-compact étale `u : U ⟶ X` admitting a compactification, the
exceptional inverse image is the pullback, `Ru^! ≅ Lu^*`: this is the étale localization
`Lu^* R(𝟙 X)^! ≅ Ru^!` of `lem-amb-etale-adjoint-locality`, with `R(𝟙 X)^! ≅ 𝟭`. -/
theorem nonempty_iso_rightDerivedUpperShriek_of_etale {U X : Scheme.{u}} (u : U ⟶ X) [Etale u]
    [IsSeparated u] [QuasiCompact u] [HasCompactification u] :
    Nonempty (R(u)^![ModuleCat.{u + 1} Λ] ≅ L((u)^*[ModuleCat.{u + 1} Λ])) := by
  obtain ⟨ι⟩ := nonempty_iso_rightDerivedUpperShriek_comp_leftDerivedUpperStar_of_etale Λ u
    (𝟙 X) u (Category.comp_id u)
  exact ⟨ι.symm ≪≫ Functor.isoWhiskerRight (rightDerivedUpperShriekIdIso Λ X) _ ≪≫
    Functor.leftUnitor _⟩

/-- For a separated quasi-compact étale `u : U ⟶ X` admitting a compactification, `ω_u ≅ Λ_U`. -/
theorem nonempty_iso_dualizingComplex_of_etale {U X : Scheme.{u}} (u : U ⟶ X) [Etale u]
    [IsSeparated u] [QuasiCompact u] [HasCompactification u] :
    Nonempty (dualizingComplex (ModuleCat.{u + 1} Λ) u ≅ constantComplex Λ U) := by
  obtain ⟨ι⟩ := nonempty_iso_rightDerivedUpperShriek_of_etale Λ u
  exact ⟨ι.app _ ≪≫ leftDerivedUpperStarUnitIso _ u⟩

/-- Blueprint `lem-pur-co-smooth-etale-locality`: Source-étale locality.

Every étale morphism `u` admitting a compactification, with the exponent of `Λ` invertible on
`U`, is cohomologically smooth: it is smooth of relative dimension `0`
(`AlgebraicGeometry.Etale.isCohomologicallySmooth_of_smoothOfRelativeDimension`). For separated
quasi-compact `u`, moreover `ω_u ≅ Λ`
(`AlgebraicGeometry.Etale.nonempty_iso_dualizingComplex_of_etale`). -/
theorem isCohomologicallySmooth_of_etale {U X : Scheme.{u}} (u : U ⟶ X) [Etale u]
    [HasCompactification u] [HasInvertibleExponent Λ U] :
    IsCohomologicallySmooth Λ u :=
  isCohomologicallySmooth_of_smoothOfRelativeDimension Λ u 0

variable {Λ}

/-- Blueprint `lem-pur-co-smooth-etale-locality`: Source-étale locality.

Let `u : U ⟶ X` be a surjective étale morphism of separated schemes of finite type and
`f : X ⟶ Y`. If `u ≫ f` is cohomologically smooth, then so is `f`.

The blueprint pulls the canonical maps of `f` back along `u`, identifies them with those of
`u ≫ f` and concludes by
`AlgebraicGeometry.Etale.isIso_of_isIso_leftDerivedUpperStar_map_of_surjective`. The
identification needs the canonical étale localization `Lu^* Rf^! ≅ R(u ≫ f)^!`
(`lem-amb-etale-adjoint-locality`), the mate of a canonical composition isomorphism
`R(u ≫ f)_! ≅ Ru_! ⋙ Rf_!` under `Ru_! ⊣ Lu^*`, and its compatibility with the projection maps
and with `Ex_!`. None of these is available in the library (see the module docstring), and
the hypothesis on `u ≫ f` says nothing about `f` without such a comparison of `R(u ≫ f)^!` with
`Rf^!`. Clause 1 alone could be descended through the evaluation `ω_f ⊗ᴸ RHom(ω_f, Λ) ⟶ Λ`, but
this needs the *derived* internal hom to commute with `Lu^*`; only its sheaf-level form
`AlgebraicGeometry.Etale.isIso_ihomComparison_upperStar` is available. -/
theorem IsCohomologicallySmooth.of_comp_of_surjective {U X Y : Scheme.{u}} (u : U ⟶ X)
    [Etale u] [Surjective u] [IsSeparated u] [QuasiCompact u] (f : X ⟶ Y)
    [HasCompactification f] [HasCompactification (u ≫ f)]
    (h : IsCohomologicallySmooth Λ (u ≫ f)) : IsCohomologicallySmooth Λ f :=
  sorry

end Etale

end AlgebraicGeometry
