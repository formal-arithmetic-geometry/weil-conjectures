/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Triangulated.LocalizingClosureRepresentable
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.AmbientAdjointClass
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperShriekLocalizing

/-!
# The exceptional adjunction on `Dctf` is the restriction of the one on `Loc(Dctf)`

Let `Λ` be a finite commutative ring and `k` a field of finite cohomological dimension for
`Λ`-modules, `X`, `Y` separated finite-type `k`-schemes on which the exponent of `Λ` is
invertible, and `c` a compactification of `f : X ⟶ Y`. The adjunction
`Rf_! ⊣ f^!` on the localizing closures `Loc(Dctf(-, Λ))`
(`AlgebraicGeometry.ProEtale.rightDerivedUpperShriekLocalizingAdjunction`, obtained by Brown
representability) restricts to `Dctf`:

* for `L` in `Loc(Dctf(Y, Λ))` whose underlying object lies in `Dctf(Y, Λ)`, the value `f^! L`
  is the constructible exceptional inverse image `Rf^! L`
  (`AlgebraicGeometry.ProEtale.rightDerivedUpperShriekLocalizingObjIso`), hence lies in
  `Dctf(X, Λ)`
  (`AlgebraicGeometry.ProEtale.constructibleFiniteTor_rightDerivedUpperShriekLocalizing_obj`).
  Indeed `Rf^! L` represents `A ↦ Hom(Rf_!(c) A, L)` on the objects `A` of `Dctf(X, Λ)`
  (`bijective_rightDerivedLowerShriekOfCompactification_map_comp_counit`), and these objects
  detect isomorphisms of `Loc(Dctf(X, Λ))`
  (`CategoryTheory.ObjectProperty.isIso_homEquiv_of_bijective_localizingClosure`).
* Since `Dctf` is a full subcategory of `Loc(Dctf)` and both functors preserve it, the ambient
  adjunction restricts to an adjunction on `Dctf` with the same units and counits
  (`DerivedCategoryFiniteTor.rightDerivedLowerShriekLocalizingAdjunction`),
  whose right adjoint is the constructible exceptional inverse image `Rf^!`
  (`AlgebraicGeometry.ProEtale.DerivedCategoryFiniteTor.rightDerivedUpperShriekLocalizingIso`).

This is blueprint `proposition-six-operations-dctf--17` for finite coefficient rings.
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

open Scheme

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] {k : Type u} [Field k]
  (hk : Etale.HasFiniteCohomologicalDimension Λ (Spec (.of k))) {X Y : Scheme.{u}}
  (aX : X ⟶ Spec (.of k)) [LocallyOfFiniteType aX] [QuasiCompact aX]
  [IsSeparated aX] [HasInvertibleExponent Λ X]
  (aY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType aY] [QuasiCompact aY]
  [IsSeparated aY] [HasInvertibleExponent Λ Y] {f : X ⟶ Y} (c : Compactification f)
  [HasCompactification f] [QuasiCompact f]

/-- Blueprint `proposition-six-operations-dctf--17`: the exceptional inverse image
`f^! : Loc(Dctf(Y, Λ)) ⥤ Loc(Dctf(X, Λ))` (right adjoint of `Rf_!(c)`, obtained by Brown
representability) agrees on objects of `Dctf(Y, Λ)` with the constructible exceptional inverse
image `Rf^!`. The inverse of this isomorphism is the adjunct of the counit
`Rf_!(c) Rf^! L ⟶ L` of the class adjunction. -/
noncomputable def rightDerivedUpperShriekLocalizingObjIso
    (L : DerivedCategoryLocalizingFiniteTor Λ Y)
    (hL : DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) Y L.obj) :
    ((rightDerivedUpperShriekLocalizing Λ hk aX aY c).obj L).obj ≅
      (rightDerivedUpperShriek Λ f).obj L.obj := by
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace aY
  let adjE := Etale.rightDerivedUpperShriekAdjunctionOfCompactification Λ c
  have hG := Etale.plus_rightDerivedUpperShriek_obj Λ f
  have hLp := DerivedCategory.constructibleFiniteTor.plus hL
  let adj := rightDerivedUpperShriekLocalizingAdjunction Λ hk aX aY c
  let F := rightDerivedLowerShriekLocalizing Λ aY c
  let T : DerivedCategoryLocalizingFiniteTor Λ X :=
    ⟨(rightDerivedUpperShriekOfAdjunction _ adjE).obj L.obj,
      ObjectProperty.le_localizingClosure _ _
        (constructibleFiniteTor_rightDerivedUpperShriek Λ aY f hL)⟩
  let ε : F.obj T ⟶ L :=
    ObjectProperty.homMk (rightDerivedUpperShriekOfAdjunctionCounit adjE hG L.obj hLp)
  have hε : ∀ A : DerivedCategoryLocalizingFiniteTor Λ X,
      DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) X A.obj →
        Function.Bijective (fun g : A ⟶ T ↦ F.map g ≫ ε) := by
    intro A hA
    have hb := bijective_rightDerivedLowerShriekOfCompactification_map_comp_counit adjE hG
      (DerivedCategory.constructibleFiniteTor.plusEtaleOrigin hA) hLp
    have he : (fun g : A ⟶ T ↦ F.map g ≫ ε) =
        (fun g ↦ (ObjectProperty.homMk g : F.obj A ⟶ L)) ∘
          (fun g : A.obj ⟶ T.obj ↦
            (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} Λ) c).map g ≫
              rightDerivedUpperShriekOfAdjunctionCounit adjE hG L.obj hLp) ∘
          (fun g : A ⟶ T ↦ g.hom) := by
      ext g
      simp [F, ε, rightDerivedLowerShriekLocalizing, ObjectProperty.localizingClosureLift]
    rw [he]
    refine Function.Bijective.comp ?_ (hb.comp ?_)
    · exact ⟨fun g g' h ↦ by simpa using congrArg (fun x ↦ x.hom) h,
        fun g ↦ ⟨g.hom, rfl⟩⟩
    · exact ⟨fun g g' h ↦ by ext; exact h, fun g ↦ ⟨ObjectProperty.homMk g, rfl⟩⟩
  have : (DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) X).IsStableUnderShift ℤ :=
    ⟨fun n ↦ ⟨fun K hK ↦ hK.shift n⟩⟩
  have := ObjectProperty.isIso_homEquiv_of_bijective_localizingClosure adj ε hε
  exact ((ObjectProperty.ι _).mapIso (asIso (adj.homEquiv T L ε))).symm

/-- Blueprint `proposition-six-operations-dctf--17`: the exceptional inverse image
`f^! : Loc(Dctf(Y, Λ)) ⥤ Loc(Dctf(X, Λ))` carries objects of `Dctf(Y, Λ)` to objects of
`Dctf(X, Λ)`. -/
theorem constructibleFiniteTor_rightDerivedUpperShriekLocalizing_obj
    (L : DerivedCategoryLocalizingFiniteTor Λ Y)
    (hL : DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) Y L.obj) :
    DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) X
      ((rightDerivedUpperShriekLocalizing Λ hk aX aY c).obj L).obj :=
  (DerivedCategory.constructibleFiniteTor _ X).prop_of_iso
    (rightDerivedUpperShriekLocalizingObjIso Λ hk aX aY c L hL).symm
    (constructibleFiniteTor_rightDerivedUpperShriek Λ aY f hL)

namespace DerivedCategoryFiniteTor

variable (X) in
/-- The inclusion of `Dctf(X, Λ)` into its localizing closure `Loc(Dctf(X, Λ))`, a fully
faithful functor. -/
noncomputable abbrev toLocalizing :
    (DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) X).FullSubcategory ⥤
      DerivedCategoryLocalizingFiniteTor Λ X :=
  ObjectProperty.ιOfLE (ObjectProperty.le_localizingClosure _)

/-- The compact-support direct image `Rf_!(c) : Dctf(X, Λ) ⥤ Dctf(Y, Λ)` along a
compactification `c` of `f`, the restriction of
`AlgebraicGeometry.ProEtale.rightDerivedLowerShriekLocalizing`. -/
noncomputable abbrev rightDerivedLowerShriekLocalizingRestrict :
    (DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) X).FullSubcategory ⥤
      (DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) Y).FullSubcategory :=
  (DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) Y).lift
    ((DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) X).ι ⋙
      rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} Λ) c)
    (fun K ↦ (DerivedCategory.localizingConstructibleFiniteTor_lowerShriek_of_finiteType
      Λ aY c).2.1 _ K.property)

/-- The exceptional inverse image `f^! : Dctf(Y, Λ) ⥤ Dctf(X, Λ)`, the restriction of the
exceptional inverse image `AlgebraicGeometry.ProEtale.rightDerivedUpperShriekLocalizing` on the
localizing closures, which preserves `Dctf`
(`AlgebraicGeometry.ProEtale.constructibleFiniteTor_rightDerivedUpperShriekLocalizing_obj`). -/
noncomputable abbrev rightDerivedUpperShriekLocalizingRestrict :
    (DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) Y).FullSubcategory ⥤
      (DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) X).FullSubcategory :=
  (DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) X).lift
    (toLocalizing Λ Y ⋙ rightDerivedUpperShriekLocalizing Λ hk aX aY c ⋙
      (DerivedCategory.localizingConstructibleFiniteTor Λ X).ι)
    (fun L ↦ constructibleFiniteTor_rightDerivedUpperShriekLocalizing_obj Λ hk aX aY c
      ((toLocalizing Λ Y).obj L) L.property)

/-- Blueprint `proposition-six-operations-dctf--17`: the adjunction `Rf_! ⊣ f^!` on `Dctf`, the
restriction of the ambient adjunction `Rf_! ⊣ f^!` on the localizing closures `Loc(Dctf)`
(`AlgebraicGeometry.ProEtale.rightDerivedUpperShriekLocalizingAdjunction`) to the full
subcategories `Dctf`, which both functors preserve. Its units and counits are the ambient ones
(`map_rightDerivedLowerShriekLocalizingAdjunction_unit_app`,
`map_rightDerivedLowerShriekLocalizingAdjunction_counit_app`), and its right adjoint is the
constructible exceptional inverse image `Rf^!`
(`AlgebraicGeometry.ProEtale.DerivedCategoryFiniteTor.rightDerivedUpperShriekLocalizingIso`). -/
noncomputable def rightDerivedLowerShriekLocalizingAdjunction :
    rightDerivedLowerShriekLocalizingRestrict Λ aY c ⊣
      rightDerivedUpperShriekLocalizingRestrict Λ hk aX aY c :=
  (rightDerivedUpperShriekLocalizingAdjunction Λ hk aX aY c).restrictFullyFaithful
    (iC := toLocalizing Λ X) (iD := toLocalizing Λ Y)
    (ObjectProperty.fullyFaithfulιOfLE _) (ObjectProperty.fullyFaithfulιOfLE _)
    (Iso.refl _) (Iso.refl _)

/-- The unit of the adjunction on `Dctf` is the unit of the ambient adjunction on `Loc(Dctf)`. -/
theorem map_rightDerivedLowerShriekLocalizingAdjunction_unit_app
    (K : (DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) X).FullSubcategory) :
    (toLocalizing Λ X).map
        ((rightDerivedLowerShriekLocalizingAdjunction Λ hk aX aY c).unit.app K) =
      (rightDerivedUpperShriekLocalizingAdjunction Λ hk aX aY c).unit.app
        ((toLocalizing Λ X).obj K) := by
  rw [rightDerivedLowerShriekLocalizingAdjunction, Adjunction.map_restrictFullyFaithful_unit_app]
  simp

/-- The counit of the adjunction on `Dctf` is the counit of the ambient adjunction on
`Loc(Dctf)`. -/
theorem map_rightDerivedLowerShriekLocalizingAdjunction_counit_app
    (L : (DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) Y).FullSubcategory) :
    (toLocalizing Λ Y).map
        ((rightDerivedLowerShriekLocalizingAdjunction Λ hk aX aY c).counit.app L) =
      (rightDerivedUpperShriekLocalizingAdjunction Λ hk aX aY c).counit.app
        ((toLocalizing Λ Y).obj L) := by
  rw [rightDerivedLowerShriekLocalizingAdjunction,
    Adjunction.map_restrictFullyFaithful_counit_app]
  dsimp only [Iso.refl_inv, NatTrans.id_app]
  erw [Category.id_comp, CategoryTheory.Functor.map_id, Category.id_comp]

/-- The class adjunction `Rf_!(c) ⊣ Rf^!` between bounded below objects of étale origin and
bounded below objects (`AlgebraicGeometry.ProEtale.classUpperShriekAdjunction`), restricted to
`Dctf`. -/
noncomputable def rightDerivedLowerShriekClassAdjunction :
    rightDerivedLowerShriekLocalizingRestrict Λ aY c ⊣
      (DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) X).lift
        ((DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) Y).ι ⋙
          rightDerivedUpperShriek Λ f)
        (fun L ↦ constructibleFiniteTor_rightDerivedUpperShriek Λ aY f L.property) :=
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace aY
  (classUpperShriekAdjunction Λ c).restrictFullyFaithful
    (iC := ObjectProperty.ιOfLE
      (fun _ hK ↦ DerivedCategory.constructibleFiniteTor.plusEtaleOrigin hK))
    (iD := ObjectProperty.ιOfLE (fun _ hL ↦ DerivedCategory.constructibleFiniteTor.plus hL))
    (ObjectProperty.fullyFaithfulιOfLE
      (fun _ hK ↦ DerivedCategory.constructibleFiniteTor.plusEtaleOrigin hK))
    (ObjectProperty.fullyFaithfulιOfLE (fun _ hL ↦ DerivedCategory.constructibleFiniteTor.plus hL))
    (Iso.refl _) (Iso.refl _)

/-- Blueprint `proposition-six-operations-dctf--17`: the right adjoint of the adjunction on
`Dctf` restricted from `Loc(Dctf)` is the constructible exceptional inverse image `Rf^!`
restricted to `Dctf`, compatibly with the counits
(`rightDerivedUpperShriekLocalizingIso_hom_app_counit`). -/
noncomputable def rightDerivedUpperShriekLocalizingIso :
    rightDerivedUpperShriekLocalizingRestrict Λ hk aX aY c ≅
      (DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) X).lift
        ((DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) Y).ι ⋙
          rightDerivedUpperShriek Λ f)
        (fun L ↦ constructibleFiniteTor_rightDerivedUpperShriek Λ aY f L.property) :=
  (rightDerivedLowerShriekLocalizingAdjunction Λ hk aX aY c).rightAdjointUniq
    (rightDerivedLowerShriekClassAdjunction Λ aY c)

/-- The isomorphism `f^! ≅ Rf^!` on `Dctf` is compatible with the counits of the adjunction
restricted from `Loc(Dctf)` and of the class adjunction. -/
theorem rightDerivedUpperShriekLocalizingIso_hom_app_counit
    (L : (DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) Y).FullSubcategory) :
    (rightDerivedLowerShriekLocalizingRestrict Λ aY c).map
        ((rightDerivedUpperShriekLocalizingIso Λ hk aX aY c).hom.app L) ≫
        (rightDerivedLowerShriekClassAdjunction Λ aY c).counit.app L =
      (rightDerivedLowerShriekLocalizingAdjunction Λ hk aX aY c).counit.app L :=
  Adjunction.rightAdjointUniq_hom_app_counit _ _ L

end DerivedCategoryFiniteTor

end AlgebraicGeometry.ProEtale
