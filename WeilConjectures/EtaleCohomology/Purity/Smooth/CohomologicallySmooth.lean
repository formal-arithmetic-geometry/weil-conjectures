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

A morphism `f : X ⟶ Y` admitting a compactification is *cohomologically smooth* if its
dualizing complex
`ω_f = Rf^! Λ_Y` is ⊗-invertible, the canonical map `θ_{f,K} : ω_f ⊗ᴸ Lf^* K ⟶ Rf^! K` is an
isomorphism for every `K ∈ D^b_{ctf}(Y, Λ)`, and the canonical base change map `Lg'^* ω_f ⟶ ω_{f'}`
is an isomorphism for every cartesian square. This file proves the structural results about
this notion:

* smooth morphisms are cohomologically smooth, and the dualizing complexes of smooth morphisms
  are multiplicative under composition;
* `ω_{f ≫ g} ≅ ω_f ⊗ᴸ Lf^* ω_g` for cohomologically smooth `g`, and a composite of
  cohomologically smooth morphisms is cohomologically smooth;
* étale morphisms are cohomologically smooth with `ω_u ≅ Λ`, and cohomological smoothness
  descends along surjective étale morphisms.

## Implementation notes

The canonical maps are `AlgebraicGeometry.Etale.dualizingComplexTensorMap` and
`AlgebraicGeometry.Etale.dualizingComplexBaseChangeMap`. The base change map is the mate of the
compact-support base change `Ex_!`, which is only constructed for a quasi-compact base change
`f'`; the third clause of the definition is asked for such squares. For `f` of finite type,
every base change `f'` of it is quasi-compact, so this is no restriction there. The tensor
factors of the second clause are written `ω_f ⊗ᴸ Lf^* K`. As for all purity conventions
(`AlgebraicGeometry.Etale.tateTwist`), the categories are those of the small étale site,
identified with the pro-étale ones by the pro-étale comparison.

In the composition law, the intermediate base change of `g` is asked to be quasi-compact, which
holds for morphisms of finite type. Source-étale descent takes `u` quasi-compact and admitting a
compactification, with the exponent of `Λ` invertible on `U`.

The composition law for the canonical maps and their descent
along surjective étale maps compare the canonical maps of
`f`, `g` and `f ≫ g` through a composition isomorphism `R(f ≫ g)_! ≅ Rf_! ⋙ Rg_!` compatible
with the projection maps and with `Ex_!`, recorded in
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

/-- Cohomological smoothness.

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
   isomorphism. -/
structure IsCohomologicallySmooth {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f] :
    Prop where
  isInvertible_dualizingComplex :
    DerivedCategory.isInvertible Λ X (dualizingComplex Λ f)
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
        (dualizingComplex Λ f)).obj ((L((f)^*[ModuleCat.{u + 1} Λ])).obj K) ≅
      (R(f)^![Λ]).obj K) :=
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

`ω_{f ≫ g} ≅ Rf^! ω_g ≅ Rf^!(Λ_Y ⊗ᴸ ω_g) ≅ ω_f ⊗ᴸ Lf^* ω_g`.

The composite is given as a morphism `h` with `f ≫ g = h`. -/
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

/-- Composition.

For cohomologically smooth `g : Y ⟶ Z` and any `f : X ⟶ Y` admitting a compactification,
`ω_{f ≫ g} ≅ ω_f ⊗ᴸ Lf^* ω_g`. -/
theorem IsCohomologicallySmooth.nonempty_iso_dualizingComplex_comp {X Y Z : Scheme.{u}}
    {f : X ⟶ Y} {g : Y ⟶ Z} [HasCompactification f] [HasCompactification g]
    [HasCompactification (f ≫ g)] [QuasiCompact (f ≫ g)] (hg : IsCohomologicallySmooth Λ g) :
    Nonempty (dualizingComplex Λ (f ≫ g) ≅
      ((derivedTensor (ModuleCat.{u + 1} Λ) X).obj (dualizingComplex Λ f)).obj
        ((L((f)^*[ModuleCat.{u + 1} Λ])).obj (dualizingComplex Λ g))) :=
  nonempty_iso_dualizingComplex_comp_of_isInvertible Λ f g _ rfl hg.isInvertible_dualizingComplex

/-- Composition.

If `f : X ⟶ Y` and `g : Y ⟶ Z` are cohomologically smooth, the dualizing complex
`ω_{f ≫ g} ≅ ω_f ⊗ᴸ Lf^* ω_g` of `f ≫ g` is invertible, as a tensor product of invertible
objects. -/
theorem IsCohomologicallySmooth.isInvertible_dualizingComplex_comp {X Y Z : Scheme.{u}}
    {f : X ⟶ Y} {g : Y ⟶ Z} [HasCompactification f] [HasCompactification g]
    [HasCompactification (f ≫ g)] [QuasiCompact (f ≫ g)] (hf : IsCohomologicallySmooth Λ f)
    (hg : IsCohomologicallySmooth Λ g) :
    DerivedCategory.isInvertible Λ X (dualizingComplex Λ (f ≫ g)) := by
  obtain ⟨e⟩ := hg.nonempty_iso_dualizingComplex_comp (f := f)
  exact .of_iso e.symm (hf.isInvertible_dualizingComplex.derivedTensor
    (hg.isInvertible_dualizingComplex.leftDerivedUpperStar f))

/-- Composition.

If `f : X ⟶ Y` and `g : Y ⟶ Z` are cohomologically smooth, with `g` quasi-compact, then so is
`f ≫ g`. -/
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

/-- Smooth base change for the exceptional inverse image.

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
is an isomorphism, for `Y` quasi-separated. -/
theorem isIso_rightDerivedUpperShriekBaseChangeMap_app
    {X Y X' Y' : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f] (d : ℕ)
    [SmoothOfRelativeDimension d f] [HasInvertibleExponent Λ X] [QuasiSeparatedSpace Y]
    {v : Y' ⟶ Y} {f' : X' ⟶ Y'} {u : X' ⟶ X} (sq : IsPullback u f' f v)
    [HasCompactification f'] [QuasiCompact f']
    (K : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (_hK : DerivedCategory.boundedConstructibleFiniteTor Λ Y K) :
    IsIso ((rightDerivedUpperShriekBaseChangeMap Λ sq).app K) :=
  have := isIso_rightDerivedUpperShriekBaseChangeMap_of_smoothOfRelativeDimension Λ f d sq
  inferInstance

/-- Smooth base change for the exceptional inverse image.

The form of `AlgebraicGeometry.Etale.isIso_rightDerivedUpperShriekBaseChangeMap_app`
as an abstract isomorphism `Lu^* Rf^! K ≅ Rf'^! Lv^* K`, under the same hypotheses (`Y`
quasi-separated, `f'` quasi-compact). -/
theorem nonempty_iso_leftDerivedUpperStar_obj_rightDerivedUpperShriek_obj {X Y X' Y' : Scheme.{u}}
    (f : X ⟶ Y) [HasCompactification f] (d : ℕ) [SmoothOfRelativeDimension d f]
    [HasInvertibleExponent Λ X] [QuasiSeparatedSpace Y] {v : Y' ⟶ Y} {f' : X' ⟶ Y'}
    {u : X' ⟶ X} (sq : IsPullback u f' f v) [HasCompactification f'] [QuasiCompact f']
    (K : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (_hK : DerivedCategory.boundedConstructibleFiniteTor Λ Y K) :
    Nonempty ((L((u)^*[ModuleCat.{u + 1} Λ])).obj ((R(f)^![Λ]).obj K) ≅
      (R(f')^![Λ]).obj ((L((v)^*[ModuleCat.{u + 1} Λ])).obj K)) := by
  obtain ⟨e⟩ := nonempty_iso_leftDerivedUpperStar_comp_rightDerivedUpperShriek Λ (d := d) f sq
  exact ⟨e.app K⟩

/-- Cohomological smoothness of smooth morphisms.

A smooth morphism `f : X ⟶ Y` of pure relative dimension `d` admitting a compactification, with
the exponent of `Λ` invertible on `X` and `Y` quasi-separated, is cohomologically smooth. -/
theorem isCohomologicallySmooth_of_smoothOfRelativeDimension {X Y : Scheme.{u}} (f : X ⟶ Y)
    [HasCompactification f] (d : ℕ) [SmoothOfRelativeDimension d f]
    [HasInvertibleExponent Λ X] [QuasiSeparatedSpace Y] : IsCohomologicallySmooth Λ f where
  isInvertible_dualizingComplex := isInvertible_dualizingComplex Λ (d := d) f
  isIso_dualizingComplexTensorMap K _ :=
    isIso_dualizingComplexTensorMap_of_smoothOfRelativeDimension Λ (d := d) f K
  isIso_dualizingComplexBaseChangeMap sq _ _ := by
    have := isIso_rightDerivedUpperShriekBaseChangeMap_of_smoothOfRelativeDimension Λ f d sq
    rw [isIso_dualizingComplexBaseChangeMap_iff]
    infer_instance

/-- Cohomological smoothness of smooth morphisms.

*Composition.* For smooth `f : X ⟶ Y` and `g : Y ⟶ Z`, `ω_{f ≫ g} ≅ ω_f ⊗ᴸ Lf^* ω_g`. -/
theorem nonempty_iso_dualizingComplex_comp_of_smoothOfRelativeDimension {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) [HasCompactification f] [HasCompactification g]
    [HasCompactification (f ≫ g)] [QuasiCompact (f ≫ g)] (e : ℕ) [SmoothOfRelativeDimension e g]
    [HasInvertibleExponent Λ Y] :
    Nonempty (dualizingComplex Λ (f ≫ g) ≅
      ((derivedTensor (ModuleCat.{u + 1} Λ) X).obj (dualizingComplex Λ f)).obj
        ((L((f)^*[ModuleCat.{u + 1} Λ])).obj (dualizingComplex Λ g))) :=
  nonempty_iso_dualizingComplex_comp_of_isInvertible Λ f g _ rfl
    (isInvertible_dualizingComplex Λ (d := e) g)

/-! ### Étale morphisms and étale locality -/

/-- For a separated quasi-compact étale `u : U ⟶ X` admitting a compactification, the
exceptional inverse image is the pullback, `Ru^! ≅ Lu^*`. -/
theorem nonempty_iso_rightDerivedUpperShriek_of_etale {U X : Scheme.{u}} (u : U ⟶ X) [Etale u]
    [IsSeparated u] [QuasiCompact u] [HasCompactification u] :
    Nonempty (R(u)^![Λ] ≅ L((u)^*[ModuleCat.{u + 1} Λ])) := by
  obtain ⟨ι⟩ := nonempty_iso_rightDerivedUpperShriek_comp_leftDerivedUpperStar_of_etale Λ u
    (𝟙 X) u (Category.comp_id u)
  exact ⟨ι.symm ≪≫
    Functor.isoWhiskerRight (rightDerivedUpperShriekIdIso Λ X) _ ≪≫
    Functor.leftUnitor _⟩

/-- Source-étale locality.

Every étale morphism `u` admitting a compactification, with the exponent of `Λ` invertible on
`U` and `X` quasi-separated, is cohomologically smooth. -/
theorem isCohomologicallySmooth_of_etale {U X : Scheme.{u}} (u : U ⟶ X) [Etale u]
    [HasCompactification u] [HasInvertibleExponent Λ U] [QuasiSeparatedSpace X] :
    IsCohomologicallySmooth Λ u :=
  isCohomologicallySmooth_of_smoothOfRelativeDimension Λ u 0

variable {Λ}

/-- Source-étale locality.

Let `u : U ⟶ X` be a surjective étale morphism and `f : X ⟶ Y`. If `u ≫ f` is cohomologically
smooth, then so is `f`. -/
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
    have := etaleBaseChange Λ u squ
    have hh := (isIso_dualizingComplexBaseChangeMap_iff Λ sqh).1
      (h.isIso_dualizingComplexBaseChangeMap sqh)
    exact isIso_of_isIso_rightDerivedUpperShriek_map (pullback.snd u g')
      (isIso_dualizingComplexTensorMap_of_smoothOfRelativeDimension Λ (d := 0) _)
      (_root_.AlgebraicGeometry.Etale.isInvertible_dualizingComplex Λ (d := 0) _) _
      ((isIso_rightDerivedUpperShriekBaseChangeMap_comp_iff squ sq sqh rfl rfl (𝟙_ _)
        inferInstance).1 hh)

end Etale

end AlgebraicGeometry
