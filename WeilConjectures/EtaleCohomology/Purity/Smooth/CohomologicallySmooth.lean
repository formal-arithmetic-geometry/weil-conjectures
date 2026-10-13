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
(`AlgebraicGeometry.Etale.derivedTensorRightCompRightDerivedUpperShriekIso`). The
composite is given as a morphism `h` with `f ≫ g = h`. -/
theorem nonempty_iso_dualizingComplex_comp_of_isInvertible {X Y Z : Scheme.{u}} (f : X ⟶ Y)
    (g : Y ⟶ Z) (h : X ⟶ Z) (w : f ≫ g = h) [HasCompactification f] [HasCompactification g]
    [HasCompactification h] [QuasiCompact h]
    (hg : DerivedCategory.isInvertible Λ Y (dualizingComplex (ModuleCat.{u + 1} Λ) g)) :
    Nonempty (dualizingComplex (ModuleCat.{u + 1} Λ) h ≅
      ((derivedTensor (ModuleCat.{u + 1} Λ) X).obj (dualizingComplex (ModuleCat.{u + 1} Λ) f)).obj
        ((L((f)^*[ModuleCat.{u + 1} Λ])).obj (dualizingComplex (ModuleCat.{u + 1} Λ) g))) := by
  subst w
  obtain ⟨c⟩ := nonempty_iso_rightDerivedUpperShriek_comp Λ f g
  obtain ⟨M, ⟨e'⟩, ⟨e⟩⟩ := hg
  exact ⟨c.app _ ≪≫ (R(f)^![ModuleCat.{u + 1} Λ]).mapIso (derivedTensorLeftUnitor _ Y _).symm ≪≫
    (derivedTensorRightCompRightDerivedUpperShriekIso Λ f _ M e e').app (𝟙_ _)⟩

variable {Λ}

/-- Blueprint `lem-pur-co-smooth-composition`: Composition.

For cohomologically smooth `g : Y ⟶ Z` and any `f : X ⟶ Y` admitting a compactification,
`ω_{f ≫ g} ≅ ω_f ⊗ᴸ Lf^* ω_g`. -/
theorem IsCohomologicallySmooth.nonempty_iso_dualizingComplex_comp {X Y Z : Scheme.{u}}
    {f : X ⟶ Y} {g : Y ⟶ Z} [HasCompactification f] [HasCompactification g]
    [HasCompactification (f ≫ g)] [QuasiCompact (f ≫ g)] (hg : IsCohomologicallySmooth Λ g) :
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
    [HasCompactification (f ≫ g)] [QuasiCompact (f ≫ g)] (hf : IsCohomologicallySmooth Λ f)
    (hg : IsCohomologicallySmooth Λ g) :
    DerivedCategory.isInvertible Λ X (dualizingComplex (ModuleCat.{u + 1} Λ) (f ≫ g)) := by
  obtain ⟨e⟩ := hg.nonempty_iso_dualizingComplex_comp (f := f)
  exact .of_iso e.symm (hf.isInvertible_dualizingComplex.derivedTensor
    (hg.isInvertible_dualizingComplex.leftDerivedUpperStar f))

/-- Blueprint `lem-pur-co-smooth-composition`: Composition.

If `f : X ⟶ Y` and `g : Y ⟶ Z` are cohomologically smooth, then so is `f ≫ g`:
* `ω_{f ≫ g} ≅ ω_f ⊗ᴸ Lf^* ω_g` is invertible
  (`AlgebraicGeometry.Etale.IsCohomologicallySmooth.isInvertible_dualizingComplex_comp`);
* `θ_{f ≫ g, K}` factors through `τ_f(ω_g, Lg^* K)` and `Rf^! θ_{g, K}`, by the composition law
  for `R_!` compatible with the projection maps
  (`AlgebraicGeometry.Etale.isIso_dualizingComplexTensorMap_comp`);
* for a cartesian square over `Z`, built from cartesian squares over `Y` and over `Z`, the base
  change map of `f ≫ g` is that of `f` at `ω_g` followed by `Rf'^!` of that of `g`
  (`AlgebraicGeometry.Etale.isIso_rightDerivedUpperShriekBaseChangeMap_comp_iff`); the base
  change map of `f` is an isomorphism at the invertible `ω_g` as soon as it is one at `Λ_Y`
  (`AlgebraicGeometry.Etale.isIso_rightDerivedUpperShriekBaseChangeMap_app_of_isInvertible`).

The intermediate base change of `g` is quasi-compact when `g` is, which is assumed; this holds
under the conventions of the blueprint (morphisms of finite type). -/
theorem IsCohomologicallySmooth.comp {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    [HasCompactification f] [HasCompactification g] [HasCompactification (f ≫ g)]
    [QuasiCompact g] [QuasiCompact (f ≫ g)]
    (hf : IsCohomologicallySmooth Λ f) (hg : IsCohomologicallySmooth Λ g) :
    IsCohomologicallySmooth Λ (f ≫ g) where
  isInvertible_dualizingComplex := hf.isInvertible_dualizingComplex_comp hg
  isIso_dualizingComplexTensorMap K hK :=
    isIso_dualizingComplexTensorMap_comp f g hf.isIso_dualizingComplexTensorMap
      hg.isInvertible_dualizingComplex K hK (hg.isIso_dualizingComplexTensorMap K hK)
  isIso_dualizingComplexBaseChangeMap {X' Z'} {c} {h'} {a} sq _ _ := by
    rw [isIso_dualizingComplexBaseChangeMap_iff]
    have sqg : IsPullback (pullback.fst g c) (pullback.snd g c) g c := .of_hasPullback g c
    obtain ⟨f', hf', w'⟩ : ∃ f' : X' ⟶ pullback g c,
        f' ≫ pullback.fst g c = a ≫ f ∧ f' ≫ pullback.snd g c = h' :=
      ⟨pullback.lift (a ≫ f) h' (by simpa using sq.w), by simp, by simp⟩
    have sqf : IsPullback a f' f (pullback.fst g c) :=
      IsPullback.of_bot (by rw [w']; exact sq) hf'.symm sqg
    have : HasCompactification f' := .of_isPullback sqf
    have : QuasiCompact (f' ≫ pullback.snd g c) := by
      rw [w']
      infer_instance
    have := QuasiCompact.of_comp f' (pullback.snd g c)
    have h₁ := (isIso_dualizingComplexBaseChangeMap_iff Λ sqf).1
      (hf.isIso_dualizingComplexBaseChangeMap sqf)
    have hf₁ := isIso_rightDerivedUpperShriekBaseChangeMap_app_of_isInvertible sqf h₁
      hg.isInvertible_dualizingComplex
    have hg₁ := (isIso_dualizingComplexBaseChangeMap_iff Λ sqg).1
      (hg.isIso_dualizingComplexBaseChangeMap sqg)
    exact (isIso_rightDerivedUpperShriekBaseChangeMap_comp_iff sqf sqg sq rfl w' (𝟙_ _) hf₁).2
      inferInstance

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
    [HasCompactification (f ≫ g)] [QuasiCompact (f ≫ g)] (e : ℕ) [SmoothOfRelativeDimension e g]
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
  exact ⟨ι.symm ≪≫
    Functor.isoWhiskerRight (rightDerivedUpperShriekIdIso (ModuleCat.{u + 1} Λ) X) _ ≪≫
    Functor.leftUnitor _⟩

/-- Blueprint `lem-pur-co-smooth-etale-locality`: Source-étale locality.

Every étale morphism `u` admitting a compactification, with the exponent of `Λ` invertible on
`U`, is cohomologically smooth: it is smooth of relative dimension `0`
(`AlgebraicGeometry.Etale.isCohomologicallySmooth_of_smoothOfRelativeDimension`). Moreover
`ω_u ≅ Λ` (`AlgebraicGeometry.Etale.nonempty_dualizingComplex_iso_constantComplex_of_etale`). -/
theorem isCohomologicallySmooth_of_etale {U X : Scheme.{u}} (u : U ⟶ X) [Etale u]
    [HasCompactification u] [HasInvertibleExponent Λ U] :
    IsCohomologicallySmooth Λ u :=
  isCohomologicallySmooth_of_smoothOfRelativeDimension Λ u 0

variable {Λ}

/-- Blueprint `lem-pur-co-smooth-etale-locality`: Source-étale locality.

Let `u : U ⟶ X` be a surjective étale morphism and `f : X ⟶ Y`. If `u ≫ f` is cohomologically
smooth, then so is `f`. The étale `u` is cohomologically smooth with `θ_u` an isomorphism at every
object (`AlgebraicGeometry.Etale.isCohomologicallySmooth_of_etale`), so `Ru^!` reflects
isomorphisms after pullback along `u`, and isomorphisms descend along `u`
(`AlgebraicGeometry.Etale.isIso_of_isIso_leftDerivedUpperStar_map_of_surjective`):
1. `ω_{u ≫ f} ≅ ω_u ⊗ᴸ Lu^* ω_f`, so `Lu^* ω_f` is invertible, and invertibility descends along
   `u` (`AlgebraicGeometry.Etale.isInvertible_dualizingComplex_of_comp`);
2. `θ_{u ≫ f, K}` factors through `Ru^! θ_{f, K}`
   (`AlgebraicGeometry.Etale.isIso_dualizingComplexTensorMap_of_comp`);
3. for a cartesian square of `f`, the base change map of `u ≫ f` along the pulled back square is
   that of `u` followed by `Ru'^!` of that of `f`
   (`AlgebraicGeometry.Etale.isIso_rightDerivedUpperShriekBaseChangeMap_comp_iff`), and the base
   change map of `u` is an isomorphism (`prop-asd-smooth-base-change`).

The blueprint takes `u` separated of finite type between schemes over a field on which the
exponent of `Λ` is invertible; here `u` is assumed quasi-compact and to admit a
compactification, and the exponent of `Λ` invertible on `U`. -/
theorem IsCohomologicallySmooth.of_comp_of_surjective {U X Y : Scheme.{u}} (u : U ⟶ X)
    [Etale u] [Surjective u] [QuasiCompact u] [HasCompactification u]
    [HasInvertibleExponent Λ U] (f : X ⟶ Y) [HasCompactification f]
    [HasCompactification (u ≫ f)] [QuasiCompact (u ≫ f)] (h : IsCohomologicallySmooth Λ (u ≫ f)) :
    IsCohomologicallySmooth Λ f where
  isInvertible_dualizingComplex :=
    isInvertible_dualizingComplex_of_comp u f
      (isIso_dualizingComplexTensorMap_of_smoothOfRelativeDimension Λ (d := 0) u)
      (_root_.AlgebraicGeometry.Etale.isInvertible_dualizingComplex Λ (d := 0) u)
      h.isInvertible_dualizingComplex
  isIso_dualizingComplexTensorMap K hK :=
    isIso_dualizingComplexTensorMap_of_comp u f
      (isIso_dualizingComplexTensorMap_of_smoothOfRelativeDimension Λ (d := 0) u)
      (_root_.AlgebraicGeometry.Etale.isInvertible_dualizingComplex Λ (d := 0) u) K
      (h.isIso_dualizingComplexTensorMap K hK)
  isIso_dualizingComplexBaseChangeMap {X' Y'} {g} {f'} {g'} sq _ _ := by
    rw [isIso_dualizingComplexBaseChangeMap_iff]
    have squ : IsPullback (pullback.fst u g') (pullback.snd u g') u g' := .of_hasPullback u g'
    have sqh := squ.paste_vert sq
    have : HasCompactification (pullback.snd u g' ≫ f') := .of_isPullback sqh
    have : HasInvertibleExponent Λ (pullback u g') := .of_hom (pullback.fst u g')
    have := isIso_rightDerivedUpperShriekBaseChangeMap_of_smoothOfRelativeDimension Λ u 0 squ
    have hh := (isIso_dualizingComplexBaseChangeMap_iff Λ sqh).1
      (h.isIso_dualizingComplexBaseChangeMap sqh)
    exact isIso_of_isIso_rightDerivedUpperShriek_map (pullback.snd u g')
      (isIso_dualizingComplexTensorMap_of_smoothOfRelativeDimension Λ (d := 0) _)
      (_root_.AlgebraicGeometry.Etale.isInvertible_dualizingComplex Λ (d := 0) _) _
      ((isIso_rightDerivedUpperShriekBaseChangeMap_comp_iff squ sq sqh rfl rfl (𝟙_ _)
        inferInstance).1 hh)

end Etale

end AlgebraicGeometry
