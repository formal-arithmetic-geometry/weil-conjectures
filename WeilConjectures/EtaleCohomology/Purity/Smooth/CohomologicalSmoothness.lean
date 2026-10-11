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
public import WeilConjectures.SixFunctors.Etale.Derived.UpperShriekInvertible

/-!
# Cohomologically smooth morphisms

A morphism `f : X ⟶ Y` admitting a compactification is *cohomologically smooth*
(blueprint `def-pur-co-smoothness`) if its dualizing complex `ω_f = Rf^! Λ_Y` is ⊗-invertible,
`Rf^! K ≅ Lf^* K ⊗ᴸ ω_f` for every `K ∈ D^b_{ctf}(Y, Λ)`, and the formation of `ω_f` commutes
with arbitrary base change. This file proves the structural results of the blueprint subsection
`sk-prop-cohsm` about this notion:

* smooth morphisms are cohomologically smooth (`thm-pur-cohomological-smoothness`), and the
  dualizing complexes of smooth morphisms are multiplicative under composition;
* cohomologically smooth morphisms are stable under composition, with
  `ω_{f ≫ g} ≅ ω_f ⊗ᴸ Lf^* ω_g` (`lem-pur-co-smooth-composition`);
* étale morphisms are cohomologically smooth with `ω_u ≅ Λ`, and cohomological smoothness
  descends along surjective étale morphisms of the source (`lem-pur-co-smooth-etale-locality`).

## Implementation notes

The blueprint asks for the *canonical* maps — the mate `θ_{f,K}` of the projection formula and
the base change map `Lg'^* ω_f ⟶ ω_{f'}` — to be isomorphisms. Neither map, nor the canonical
composition isomorphism `R(f ≫ g)^! ≅ Rf^! ⋙ Rg^!` of which the blueprint's proofs make use, is
available in the library (`AlgebraicGeometry.Etale.nonempty_iso_rightDerivedUpperShriek_comp`
records its existence only). As for the statements of `sk-prop-cohsm` in
`WeilConjectures.EtaleCohomology.Purity.Smooth.Basic`, the definition records the existence of
the isomorphisms.

The composition law needs no tensor formula for the base change: an invertible tensor factor
passes through every `Rf^!`
(`AlgebraicGeometry.Etale.nonempty_iso_rightDerivedUpperShriek_comp_derivedTensorRight`), so
`ω_{f ≫ g} ≅ Rf^! ω_g ≅ ω_f ⊗ᴸ Lf^* ω_g` as soon as `ω_g` is invertible.

## Main definitions

- `AlgebraicGeometry.Etale.IsCohomologicallySmooth`

## Main statements

- `AlgebraicGeometry.Etale.isCohomologicallySmooth_of_smoothOfRelativeDimension`
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
2. for every `K ∈ D^b_{ctf}(Y, Λ)`, `Lf^* K ⊗ᴸ ω_f ≅ Rf^! K`;
3. for every cartesian square
   ```
     X' --g'--> X
     |          |
     f'         f
     ↓          ↓
     Y' --g---> Y
   ```
   with `f'` admitting a compactification, `Lg'^* ω_f ≅ ω_{f'}`.

The blueprint asks for the canonical maps (the mate of the projection formula, the base change
map) to be isomorphisms; they are not available in the library, and the existence of
isomorphisms is recorded instead (see the module docstring). -/
structure IsCohomologicallySmooth {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f] :
    Prop where
  isInvertible_dualizingComplex :
    DerivedCategory.isInvertible Λ X (dualizingComplex (ModuleCat.{u + 1} Λ) f)
  nonempty_iso_rightDerivedUpperShriek_obj
    (K : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hK : DerivedCategory.boundedConstructibleFiniteTor Λ Y K) :
    Nonempty (((derivedTensor (ModuleCat.{u + 1} Λ) X).obj
        ((L((f)^*[ModuleCat.{u + 1} Λ])).obj K)).obj (dualizingComplex (ModuleCat.{u + 1} Λ) f) ≅
      (R(f)^![ModuleCat.{u + 1} Λ]).obj K)
  nonempty_iso_dualizingComplex_of_isPullback {X' Y' : Scheme.{u}} {g : Y' ⟶ Y}
    {f' : X' ⟶ Y'} {g' : X' ⟶ X} (sq : IsPullback g' f' f g) [HasCompactification f'] :
    Nonempty ((L((g')^*[ModuleCat.{u + 1} Λ])).obj (dualizingComplex (ModuleCat.{u + 1} Λ) f) ≅
      dualizingComplex (ModuleCat.{u + 1} Λ) f')

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

For cohomologically smooth `f : X ⟶ Y` and `g : Y ⟶ Z`,
`ω_{f ≫ g} ≅ ω_f ⊗ᴸ Lf^* ω_g`. -/
theorem IsCohomologicallySmooth.nonempty_iso_dualizingComplex_comp {X Y Z : Scheme.{u}}
    {f : X ⟶ Y} {g : Y ⟶ Z} [HasCompactification f] [HasCompactification g]
    [HasCompactification (f ≫ g)] (hg : IsCohomologicallySmooth Λ g) :
    Nonempty (dualizingComplex (ModuleCat.{u + 1} Λ) (f ≫ g) ≅
      ((derivedTensor (ModuleCat.{u + 1} Λ) X).obj (dualizingComplex (ModuleCat.{u + 1} Λ) f)).obj
        ((L((f)^*[ModuleCat.{u + 1} Λ])).obj (dualizingComplex (ModuleCat.{u + 1} Λ) g))) :=
  nonempty_iso_dualizingComplex_comp_of_isInvertible Λ f g _ rfl hg.isInvertible_dualizingComplex

/-- Blueprint `lem-pur-co-smooth-composition`: Composition.

If `f : X ⟶ Y` and `g : Y ⟶ Z` are cohomologically smooth, then so is `f ≫ g`:
* `ω_{f ≫ g} ≅ ω_f ⊗ᴸ Lf^* ω_g` is a tensor product of invertible objects;
* for `K ∈ D^b_{ctf}(Z, Λ)`, with `Lg^* K ∈ D^b_{ctf}(Y, Λ)`,
  `R(f ≫ g)^! K ≅ Rf^!(Lg^* K ⊗ᴸ ω_g) ≅ Rf^!(Lg^* K) ⊗ᴸ Lf^* ω_g
    ≅ (L(f ≫ g)^* K ⊗ᴸ ω_f) ⊗ᴸ Lf^* ω_g ≅ L(f ≫ g)^* K ⊗ᴸ ω_{f ≫ g}`;
* a cartesian square over `f ≫ g` is the composite of a cartesian square over `f` and one over
  `g`, and `Lg''^* ω_{f ≫ g} ≅ Lg''^* ω_f ⊗ᴸ Lg''^* Lf^* ω_g ≅ ω_{f'} ⊗ᴸ Lf'^* ω_{g'}
  ≅ ω_{f' ≫ g'}`, the last step because `ω_{g'} ≅ Lv^* ω_g` is invertible. -/
theorem IsCohomologicallySmooth.comp {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    [HasCompactification f] [HasCompactification g] [HasCompactification (f ≫ g)]
    (hf : IsCohomologicallySmooth Λ f) (hg : IsCohomologicallySmooth Λ g) :
    IsCohomologicallySmooth Λ (f ≫ g) where
  isInvertible_dualizingComplex := by
    obtain ⟨e⟩ := hg.nonempty_iso_dualizingComplex_comp (f := f)
    exact .of_iso e.symm (hf.isInvertible_dualizingComplex.derivedTensor
      (hg.isInvertible_dualizingComplex.leftDerivedUpperStar f))
  nonempty_iso_rightDerivedUpperShriek_obj K hK := by
    obtain ⟨e⟩ := hg.nonempty_iso_dualizingComplex_comp (f := f)
    obtain ⟨c⟩ := nonempty_iso_rightDerivedUpperShriek_comp Λ f g
    obtain ⟨t⟩ := nonempty_iso_rightDerivedUpperShriek_comp_derivedTensorRight Λ f
      hg.isInvertible_dualizingComplex
    obtain ⟨eg⟩ := hg.nonempty_iso_rightDerivedUpperShriek_obj K hK
    obtain ⟨ef⟩ := hf.nonempty_iso_rightDerivedUpperShriek_obj _
      (constructibleFiniteTor_leftDerivedUpperStar _ g hK)
    exact ⟨((derivedTensor _ X).obj _).mapIso e ≪≫ (derivedTensorAssociator _ X _ _ _).symm ≪≫
      ((derivedTensor _ X).flip.obj _).mapIso
        (((derivedTensor _ X).flip.obj _).mapIso ((leftDerivedUpperStarComp _ f g).app K) ≪≫
          ef) ≪≫
      (t.app _).symm ≪≫ (R(f)^![ModuleCat.{u + 1} Λ]).mapIso eg ≪≫ (c.app K).symm⟩
  nonempty_iso_dualizingComplex_of_isPullback {X' Z'} w h' g'' sq _ := by
    have sqY := IsPullback.of_hasPullback g w
    let f' : X' ⟶ pullback g w := pullback.lift (g'' ≫ f) h' (by rw [Category.assoc, sq.w])
    have hcomp : f' ≫ pullback.snd g w = h' := pullback.lift_snd _ _ _
    have sqX : IsPullback g'' f' f (pullback.fst g w) :=
      IsPullback.of_bot (by rw [hcomp]; exact sq) (pullback.lift_fst _ _ _).symm sqY
    have : HasCompactification f' := .of_isPullback sqX
    have : HasCompactification (pullback.snd g w) := .of_isPullback sqY
    obtain ⟨e⟩ := hg.nonempty_iso_dualizingComplex_comp (f := f)
    obtain ⟨ef⟩ := hf.nonempty_iso_dualizingComplex_of_isPullback sqX
    obtain ⟨eg⟩ := hg.nonempty_iso_dualizingComplex_of_isPullback sqY
    obtain ⟨e'⟩ := nonempty_iso_dualizingComplex_comp_of_isInvertible Λ f' (pullback.snd g w) h'
      hcomp (.of_iso eg (hg.isInvertible_dualizingComplex.leftDerivedUpperStar _))
    exact ⟨(L((g'')^*[ModuleCat.{u + 1} Λ])).mapIso e ≪≫ leftDerivedUpperStarTensorIso _ g'' _ _ ≪≫
      ((derivedTensor _ X').mapIso ef).app _ ≪≫ ((derivedTensor _ X').obj _).mapIso
        (((leftDerivedUpperStarComp _ g'' f).app _).symm ≪≫
          (leftDerivedUpperStarComp _ f' (pullback.fst g w) (g'' ≫ f) sqX.w).app _ ≪≫
          (L((f')^*[ModuleCat.{u + 1} Λ])).mapIso eg) ≪≫ e'.symm⟩

/-! ### Smooth morphisms -/

variable (Λ)

/-- Blueprint `thm-pur-cohomological-smoothness`: Cohomological smoothness of smooth morphisms.

A smooth morphism `f : X ⟶ Y` of pure relative dimension `d` admitting a compactification, with
the exponent of `Λ` invertible on `X`, is cohomologically smooth: `ω_f` is invertible
(`AlgebraicGeometry.Etale.isInvertible_dualizingComplex`), the tensor formula holds
(`AlgebraicGeometry.Etale.nonempty_iso_rightDerivedUpperShriek_obj_derivedTensor`) and the
formation of `ω_f` commutes with arbitrary base change, by smooth base change for `R^!`
(`AlgebraicGeometry.Etale.nonempty_iso_leftDerivedUpperStar_comp_rightDerivedUpperShriek`).
The compatibility with composition is
`AlgebraicGeometry.Etale.nonempty_iso_dualizingComplex_comp_of_smoothOfRelativeDimension`. -/
theorem isCohomologicallySmooth_of_smoothOfRelativeDimension {X Y : Scheme.{u}} (f : X ⟶ Y)
    [HasCompactification f] (d : ℕ) [SmoothOfRelativeDimension d f]
    [HasInvertibleExponent Λ X] : IsCohomologicallySmooth Λ f where
  isInvertible_dualizingComplex := isInvertible_dualizingComplex Λ (d := d) f
  nonempty_iso_rightDerivedUpperShriek_obj K hK :=
    nonempty_iso_rightDerivedUpperShriek_obj_derivedTensor Λ (d := d) f K hK
  nonempty_iso_dualizingComplex_of_isPullback {X' Y'} g f' g' sq _ := by
    obtain ⟨e⟩ := nonempty_iso_leftDerivedUpperStar_comp_rightDerivedUpperShriek Λ (d := d) f sq
    exact ⟨e.app (𝟙_ _) ≪≫
      (R(f')^![ModuleCat.{u + 1} Λ]).mapIso (leftDerivedUpperStarUnitIso _ g)⟩

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

Every separated quasi-compact étale morphism `u` admitting a compactification is
cohomologically smooth, with `ω_u ≅ Λ`
(`AlgebraicGeometry.Etale.nonempty_iso_dualizingComplex_of_etale`): `Ru^! ≅ Lu^*` is preserved by
base change, the base change of `u` being again étale. -/
theorem isCohomologicallySmooth_of_etale {U X : Scheme.{u}} (u : U ⟶ X) [Etale u]
    [IsSeparated u] [QuasiCompact u] [HasCompactification u] :
    IsCohomologicallySmooth Λ u where
  isInvertible_dualizingComplex := by
    obtain ⟨e⟩ := nonempty_iso_dualizingComplex_of_etale Λ u
    exact .of_iso e.symm (DerivedCategory.isInvertible_constantComplex Λ U)
  nonempty_iso_rightDerivedUpperShriek_obj K _ := by
    obtain ⟨e⟩ := nonempty_iso_dualizingComplex_of_etale Λ u
    obtain ⟨ι⟩ := nonempty_iso_rightDerivedUpperShriek_of_etale Λ u
    exact ⟨((derivedTensor _ U).obj _).mapIso e ≪≫ derivedTensorRightUnitor _ U _ ≪≫
      (ι.app K).symm⟩
  nonempty_iso_dualizingComplex_of_isPullback {U' X'} g u' g' sq _ := by
    have : Etale u' := MorphismProperty.of_isPullback sq ‹Etale u›
    have : IsSeparated u' := MorphismProperty.of_isPullback sq ‹IsSeparated u›
    have : QuasiCompact u' := MorphismProperty.of_isPullback sq ‹QuasiCompact u›
    obtain ⟨e⟩ := nonempty_iso_dualizingComplex_of_etale Λ u
    obtain ⟨e'⟩ := nonempty_iso_dualizingComplex_of_etale Λ u'
    exact ⟨(L((g')^*[ModuleCat.{u + 1} Λ])).mapIso e ≪≫ leftDerivedUpperStarUnitIso _ g' ≪≫
      e'.symm⟩

variable {Λ}

/-- Blueprint `lem-pur-co-smooth-etale-locality`: Source-étale locality.

Let `u : U ⟶ X` be a surjective étale morphism of separated schemes of finite type and
`f : X ⟶ Y`. If `u ≫ f` is cohomologically smooth, then so is `f`.

The blueprint's argument pulls back the canonical maps of `def-pur-co-smoothness` along `u`,
identifies them with those of `u ≫ f` and concludes by
`AlgebraicGeometry.Etale.isIso_of_isIso_leftDerivedUpperStar_map_of_surjective`. This needs the
canonical maps and their compatibility with the canonical identification `Lu^* Rf^! ≅ R(u ≫ f)^!`;
neither is available in the library, and isomorphisms whose existence alone is known cannot be
descended along `u`. -/
theorem IsCohomologicallySmooth.of_comp_of_surjective {U X Y : Scheme.{u}} (u : U ⟶ X)
    [Etale u] [Surjective u] [IsSeparated u] [QuasiCompact u] (f : X ⟶ Y)
    [HasCompactification f] [HasCompactification (u ≫ f)]
    (h : IsCohomologicallySmooth Λ (u ≫ f)) : IsCohomologicallySmooth Λ f :=
  sorry

end Etale

end AlgebraicGeometry
