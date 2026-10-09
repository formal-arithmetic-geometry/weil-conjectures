/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan, Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.UpperShriek
public import WeilConjectures.SixFunctors.ProEtale.Derived.LowerShriekComparison

/-!

# Derived Upper Shriek

This is the pro-étale counterpart of
`WeilConjectures.SixFunctors.Etale.Derived.UpperShriek`.

The pro-étale derived lower shriek `Rf_!` is in general *not* a left adjoint, not even on `D⁺`:
for the structure morphism of an elliptic curve over `𝔽̄_p` and `𝔽_r`-module coefficients with
`r ≠ p`, `Rf_! = Rf_*` does not preserve coproducts (blueprint `sk-rem-sf-fullcd-scope`; see
`WeilConjectures.SixFunctors.ProEtale.ExceptionalAdjoint`). So the exceptional inverse image is
not defined as a right adjoint. Following blueprint `sk-def-sf-operations` (vi), it is the
*constructible* exceptional inverse image, the étale right adjoint transported along the
comparison:

`Rf^! := ν_X^* ∘ f^× ∘ Rν_{Y,*} : D(Y_proét) ⥤ D(X_proét)`,

where `f^× = AlgebraicGeometry.Etale.rightDerivedUpperShriek` is the right adjoint of the étale
`Rf_!`. Its defining property is a theorem, not a hypothesis (blueprint `sk-prop-sf-existence`
(c)): for `K` bounded below of étale origin and `L` bounded below,
`Hom(Rf_! K, L) ≃ Hom(K, Rf^! L)`, naturally in both
(`AlgebraicGeometry.ProEtale.rightDerivedUpperShriekHomEquiv`). Every bounded constructible
object is bounded below of étale origin, so the adjunction holds on the constructible
categories.

# Main Results

- `AlgebraicGeometry.ProEtale.rightDerivedUpperShriek` : `Rf^! : D(Y_proét) ⥤ D(X_proét)`,
  with scoped notation `R(f)^![A]`.
- `AlgebraicGeometry.ProEtale.plus_rightDerivedUpperShriek_obj`,
  `AlgebraicGeometry.ProEtale.plusEtaleOrigin_rightDerivedUpperShriek_obj` : `Rf^!` sends a
  bounded below object to an object bounded below of étale origin.
- `AlgebraicGeometry.ProEtale.rightDerivedUpperShriekCounit` : the counit
  `Rf_! Rf^! L ⟶ L` at a bounded below `L`, natural in `L`
  (`AlgebraicGeometry.ProEtale.rightDerivedUpperShriekCounit_naturality`).
- `AlgebraicGeometry.ProEtale.rightDerivedUpperShriekHomEquiv` : the adjunction
  `Hom(Rf_! K, L) ≃ Hom(K, Rf^! L)` for `K` bounded below of étale origin and `L` bounded below,
  whose inverse is `g ↦ Rf_! g ≫ ε_L`.
- `AlgebraicGeometry.ProEtale.rightDerivedUpperShriekPlus` : `Rf^! : D⁺(Y_proét) ⥤ D⁺(X_proét)`,
  the restriction of `R(f)^![A]`, with scoped notation `R(f)^![A]+`.

## Implementation notes

* `Rf^!` is defined by the same formula on the whole unbounded derived category, but it is only
  meaningful on `D⁺(Y_proét)`, where the blueprint defines it: the adjunction is only asserted for
  bounded below objects.
* The bijectivity in `rightDerivedUpperShriekHomEquiv` is the chain of bijections of the proof of
  blueprint `sk-prop-sf-existence` (c): the compact-support comparison
  `AlgebraicGeometry.ProEtale.rightDerivedLowerShriekComparisonIso`, the adjunction
  `ν^* ⊣ Rν_*`, the étale adjunction `Rf_! ⊣ f^×` and the full faithfulness of `ν^*` on `D⁺`
  (`AlgebraicGeometry.ProEtale.bijective_comparisonUpperStar_mapDerivedCategory_map`).
* The ambient right adjoint of `Rf_!` of blueprint `sk-prop-sf-existence` (b) is not defined
  here: it does not exist for proper curves, and nothing needs it.
* Everything here takes `[AlgebraicGeometry.Etale.HasBoundedBelowUpperShriek A f]`: that the
  étale `Rf_!` is a left adjoint, so that `f^×` exists, and that `f^×` preserves bounded below
  objects. Both rest on the finite cohomological amplitude of proper direct images, so they are
  not available for an arbitrary coefficient category; for torsion coefficients `ModuleCat Λ`,
  `Λ` finite, they are the instance
  `AlgebraicGeometry.Etale.hasBoundedBelowUpperShriek`.

-/

@[expose] public section

universe u' u

open CategoryTheory Abelian Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]

namespace ProEtale

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f]
  [Etale.HasBoundedBelowUpperShriek A f]

/-- Blueprint `sk-def-sf-operations` (vi): the exceptional inverse image
`Rf^! := ν_X^* ∘ f^× ∘ Rν_{Y,*} : D(Y_proét) ⥤ D(X_proét)` along a morphism `f : X ⟶ Y`
admitting a compactification, where `f^×` is the étale exceptional inverse image
`AlgebraicGeometry.Etale.rightDerivedUpperShriek`, the right adjoint of the étale `Rf_!`. It is
the constructible exceptional inverse image of the blueprint, meaningful on bounded below
complexes, where it is right adjoint to `Rf_!` on objects of étale origin
(`AlgebraicGeometry.ProEtale.rightDerivedUpperShriekHomEquiv`). -/
noncomputable def rightDerivedUpperShriek :
    DerivedCategory (Sheaf (Scheme.ProEt.topology Y) A) ⥤
      DerivedCategory (Sheaf (Scheme.ProEt.topology X) A) :=
  R(ν_*(Y)[A]) ⋙ Etale.rightDerivedUpperShriek A f ⋙ D(ν^*(X)[A])

@[inherit_doc rightDerivedUpperShriek]
scoped notation "R(" f ")^![" A "]" =>
  rightDerivedUpperShriek A f

lemma rightDerivedUpperShriek_obj (L : DerivedCategory (Sheaf (Scheme.ProEt.topology Y) A)) :
    (R(f)^![A]).obj L =
      D(ν^*(X)[A]).obj ((Etale.rightDerivedUpperShriek A f).obj (R(ν_*(Y)[A]).obj L)) :=
  rfl

/-- Transport of the exceptional inverse image along an equality of morphisms:
`Rf^! ≅ Rg^!` for `f = g`. -/
noncomputable def rightDerivedUpperShriekCongr {f g : X ⟶ Y} (h : f = g)
    [HasCompactification f] [HasCompactification g] [Etale.HasBoundedBelowUpperShriek A f]
    [Etale.HasBoundedBelowUpperShriek A g] : R(f)^![A] ≅ R(g)^![A] :=
  eqToIso <| by
    subst h
    rfl

@[simp]
lemma rightDerivedUpperShriekCongr_rfl :
    rightDerivedUpperShriekCongr A (rfl : f = f) = Iso.refl _ :=
  rfl

section BoundedBelow

variable {A}

/-- The right derived comparison restriction `Rν_*` sends bounded below objects to bounded
below objects. -/
lemma plus_rightDerivedFunctor_comparisonLowerStar_obj
    {L : DerivedCategory (Sheaf (Scheme.ProEt.topology Y) A)}
    (hL : DerivedCategory.TStructure.t.plus L) :
    DerivedCategory.TStructure.t.plus (R(ν_*(Y)[A]).obj L) :=
  DerivedCategory.TStructure.t.plus.prop_of_iso
    ((ν_*(Y)[A]).rightDerivedFunctorPlusCompatibility.app ⟨L, hL⟩)
    (R+(ν_*(Y)[A]).obj ⟨L, hL⟩).property

/-- The étale object `f^× Rν_* L` of which `Rf^! L` is the comparison pullback is bounded
below when `L` is. -/
lemma plus_etaleRightDerivedUpperShriek_obj
    {L : DerivedCategory (Sheaf (Scheme.ProEt.topology Y) A)}
    (hL : DerivedCategory.TStructure.t.plus L) :
    DerivedCategory.TStructure.t.plus
      ((Etale.rightDerivedUpperShriek A f).obj (R(ν_*(Y)[A]).obj L)) :=
  Etale.plus_rightDerivedUpperShriek_obj A f _ (plus_rightDerivedFunctor_comparisonLowerStar_obj hL)

/-- `Rf^!` sends a bounded below object to an object bounded below of étale origin. -/
lemma plusEtaleOrigin_rightDerivedUpperShriek_obj
    {L : DerivedCategory (Sheaf (Scheme.ProEt.topology Y) A)}
    (hL : DerivedCategory.TStructure.t.plus L) :
    DerivedCategory.plusEtaleOrigin A X ((R(f)^![A]).obj L) :=
  DerivedCategory.plusEtaleOrigin_mapDerivedCategory_obj
    (plus_etaleRightDerivedUpperShriek_obj f hL)

/-- The exceptional inverse image `Rf^!` preserves bounded below objects. -/
lemma plus_rightDerivedUpperShriek_obj
    {L : DerivedCategory (Sheaf (Scheme.ProEt.topology Y) A)}
    (hL : DerivedCategory.TStructure.t.plus L) :
    DerivedCategory.TStructure.t.plus ((R(f)^![A]).obj L) :=
  (plusEtaleOrigin_rightDerivedUpperShriek_obj f hL).plus

variable (A)

/-- The exceptional inverse image `Rf^! : D⁺(Y_proét) ⥤ D⁺(X_proét)` on the *bounded below*
derived categories of pro-étale sheaves: the restriction of `R(f)^![A]`, which is well defined
by `plus_rightDerivedUpperShriek_obj`. -/
noncomputable def rightDerivedUpperShriekPlus :
    DerivedCategory.Plus (Sheaf (Scheme.ProEt.topology Y) A) ⥤
      DerivedCategory.Plus (Sheaf (Scheme.ProEt.topology X) A) :=
  DerivedCategory.TStructure.t.plus.lift (DerivedCategory.Plus.ι ⋙ R(f)^![A])
    (fun K ↦ plus_rightDerivedUpperShriek_obj f K.property)

@[inherit_doc rightDerivedUpperShriekPlus]
scoped notation "R(" f ")^![" A "]+" =>
  rightDerivedUpperShriekPlus A f

/-- The bounded below `R(f)^![A]+` is compatible with the inclusions of the bounded below
derived categories, by construction. -/
noncomputable def rightDerivedUpperShriekPlusCompatibility :
    R(f)^![A]+ ⋙ DerivedCategory.Plus.ι ≅ DerivedCategory.Plus.ι ⋙ R(f)^![A] :=
  ObjectProperty.liftCompιIso _ _ _

end BoundedBelow

section Adjunction

/- The adjunction `ν^* ⊣ Rν_*` on the unbounded derived categories is obtained by deriving the
pullback via K-flat resolutions, hence the closed symmetric monoidal structure on `A`. -/
variable [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]

variable {A}

/-- Blueprint `sk-prop-sf-existence` (c): the counit `ε_L : Rf_! Rf^! L ⟶ L` of the
exceptional adjunction at a bounded below `L`: the composite

```
  Rf_! ν_X^* f^× Rν_* L ≅ ν_Y^* Rf^{ét}_! f^× Rν_* L ──ν^* ε^{ét}──▶ ν_Y^* Rν_* L ──ε^ν──▶ L
```

of the compact-support comparison `AlgebraicGeometry.ProEtale.rightDerivedLowerShriekComparisonIso`
(at the bounded below `f^× Rν_* L`), the counit of the étale adjunction `Rf_! ⊣ f^×` and the
counit of `ν^* ⊣ Rν_*`. -/
noncomputable def rightDerivedUpperShriekCounit
    (L : DerivedCategory (Sheaf (Scheme.ProEt.topology Y) A))
    (hL : DerivedCategory.TStructure.t.plus L) :
    (ProEtale.rightDerivedLowerShriek A f).obj ((R(f)^![A]).obj L) ⟶ L :=
  ((rightDerivedLowerShriekComparisonIso A f).app
      ⟨_, plus_etaleRightDerivedUpperShriek_obj f hL⟩).hom ≫
    D(ν^*(Y)[A]).map ((Etale.rightDerivedUpperShriekAdjunction A f).counit.app _) ≫
    (derivedComparisonAdjunction A Y).counit.app L

/-- The counit of the exceptional adjunction is natural in the bounded below `L`. -/
@[reassoc]
lemma rightDerivedUpperShriekCounit_naturality
    {L L' : DerivedCategory (Sheaf (Scheme.ProEt.topology Y) A)}
    (hL : DerivedCategory.TStructure.t.plus L) (hL' : DerivedCategory.TStructure.t.plus L')
    (φ : L ⟶ L') :
    (ProEtale.rightDerivedLowerShriek A f).map ((R(f)^![A]).map φ) ≫
        rightDerivedUpperShriekCounit f L' hL' =
      rightDerivedUpperShriekCounit f L hL ≫ φ := by
  have h := (rightDerivedLowerShriekComparisonIso A f).hom.naturality
    (X := ⟨_, plus_etaleRightDerivedUpperShriek_obj f hL⟩)
    (Y := ⟨_, plus_etaleRightDerivedUpperShriek_obj f hL'⟩)
    (ObjectProperty.homMk ((Etale.rightDerivedUpperShriek A f).map (R(ν_*(Y)[A]).map φ)))
  dsimp at h
  simp only [rightDerivedUpperShriekCounit, rightDerivedUpperShriek, Functor.comp_map,
    Iso.app_hom]
  have h2 := (Etale.rightDerivedUpperShriekAdjunction A f).counit_naturality
    (R(ν_*(Y)[A]).map φ)
  have h3 := (derivedComparisonAdjunction A Y).counit_naturality φ
  rw [reassoc_of% h, ← Functor.map_comp_assoc]
  erw [h2]
  rw [Functor.map_comp_assoc]
  erw [h3]
  simp

/-- The key computation behind `rightDerivedUpperShriekHomEquiv`: for `K'` bounded below,
`g ↦ Rf_! g ≫ ε_L` sends `ν^* h`, for `h : K' ⟶ f^× Rν_* L`, to the image of `h` under the chain
of adjunction bijections, read through the compact-support comparison at `K'`. -/
lemma rightDerivedLowerShriek_map_mapDerivedCategory_map_comp_counit
    {K' : DerivedCategory (Sheaf X.smallEtaleTopology A)}
    (hK' : DerivedCategory.TStructure.t.plus K')
    {L : DerivedCategory (Sheaf (Scheme.ProEt.topology Y) A)}
    (hL : DerivedCategory.TStructure.t.plus L)
    (h : K' ⟶ (Etale.rightDerivedUpperShriek A f).obj (R(ν_*(Y)[A]).obj L)) :
    (ProEtale.rightDerivedLowerShriek A f).map (D(ν^*(X)[A]).map h) ≫
        rightDerivedUpperShriekCounit f L hL =
      ((rightDerivedLowerShriekComparisonIso A f).app ⟨K', hK'⟩).hom ≫
        ((derivedComparisonAdjunction A Y).homEquiv _ _).symm
          (((Etale.rightDerivedUpperShriekAdjunction A f).homEquiv _ _).symm h) := by
  have hn := (rightDerivedLowerShriekComparisonIso A f).hom.naturality
    (X := ⟨K', hK'⟩) (Y := ⟨_, plus_etaleRightDerivedUpperShriek_obj f hL⟩)
    (ObjectProperty.homMk h)
  dsimp at hn
  simp only [rightDerivedUpperShriekCounit, Adjunction.homEquiv_counit, Functor.map_comp,
    Category.assoc, Iso.app_hom]
  rw [reassoc_of% hn]

/-- For `K'` bounded below and `L` bounded below, `g ↦ Rf_! g ≫ ε_L` is a bijection
`Hom(ν^* K', Rf^! L) ≃ Hom(Rf_! ν^* K', L)`. -/
lemma bijective_rightDerivedLowerShriek_map_comp_counit_of_plus
    {K' : DerivedCategory (Sheaf X.smallEtaleTopology A)}
    (hK' : DerivedCategory.TStructure.t.plus K')
    {L : DerivedCategory (Sheaf (Scheme.ProEt.topology Y) A)}
    (hL : DerivedCategory.TStructure.t.plus L) :
    Function.Bijective (fun g : D(ν^*(X)[A]).obj K' ⟶ (R(f)^![A]).obj L ↦
      (ProEtale.rightDerivedLowerShriek A f).map g ≫ rightDerivedUpperShriekCounit f L hL) := by
  let E := (((Etale.rightDerivedUpperShriekAdjunction A f).homEquiv K' _).symm.trans
    ((derivedComparisonAdjunction A Y).homEquiv _ L).symm).trans
      (((rightDerivedLowerShriekComparisonIso A f).app ⟨K', hK'⟩).symm.homFromEquiv (Z := L))
  have hcomp : (fun g : D(ν^*(X)[A]).obj K' ⟶ (R(f)^![A]).obj L ↦
      (ProEtale.rightDerivedLowerShriek A f).map g ≫ rightDerivedUpperShriekCounit f L hL) ∘
        (fun h ↦ D(ν^*(X)[A]).map h) = ⇑E := by
    ext h
    exact rightDerivedLowerShriek_map_mapDerivedCategory_map_comp_counit f hK' hL h
  have hν := bijective_comparisonUpperStar_mapDerivedCategory_map K' _
    (plus_etaleRightDerivedUpperShriek_obj f hL)
  refine (Function.Bijective.of_comp_iff _ hν).1 ?_
  rw [hcomp]
  exact E.bijective

/-- For `K` bounded below of étale origin and `L` bounded below, `g ↦ Rf_! g ≫ ε_L` is a
bijection `Hom(K, Rf^! L) ≃ Hom(Rf_! K, L)`. -/
lemma bijective_rightDerivedLowerShriek_map_comp_counit
    {K : DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)}
    (hK : DerivedCategory.plusEtaleOrigin A X K)
    {L : DerivedCategory (Sheaf (Scheme.ProEt.topology Y) A)}
    (hL : DerivedCategory.TStructure.t.plus L) :
    Function.Bijective (fun g : K ⟶ (R(f)^![A]).obj L ↦
      (ProEtale.rightDerivedLowerShriek A f).map g ≫ rightDerivedUpperShriekCounit f L hL) := by
  obtain ⟨K', hK', ⟨e⟩⟩ := hK
  have h : (fun g : K ⟶ (R(f)^![A]).obj L ↦
      (ProEtale.rightDerivedLowerShriek A f).map g ≫ rightDerivedUpperShriekCounit f L hL) =
      ⇑((ProEtale.rightDerivedLowerShriek A f).mapIso e).homFromEquiv ∘
        (fun g : D(ν^*(X)[A]).obj K' ⟶ (R(f)^![A]).obj L ↦
          (ProEtale.rightDerivedLowerShriek A f).map g ≫ rightDerivedUpperShriekCounit f L hL) ∘
        ⇑e.symm.homFromEquiv := by
    ext g
    simp only [Function.comp_apply, Iso.homFromEquiv_apply, Iso.symm_inv, Functor.mapIso_inv,
      Functor.map_comp, Category.assoc, Iso.map_inv_hom_id_assoc]
  rw [h]
  exact ((ProEtale.rightDerivedLowerShriek A f).mapIso e).homFromEquiv.bijective.comp
    ((bijective_rightDerivedLowerShriek_map_comp_counit_of_plus f hK' hL).comp
      e.symm.homFromEquiv.bijective)

/-- Blueprint `sk-prop-sf-existence` (c): the exceptional adjunction
`Hom(Rf_! K, L) ≃ Hom(K, Rf^! L)` for `K` bounded below of étale origin and `L` bounded below.
Its inverse is `g ↦ Rf_! g ≫ ε_L` (`rightDerivedUpperShriekHomEquiv_symm_apply`), so it is
natural in `K` and `L` (`rightDerivedUpperShriekHomEquiv_naturality_left_symm`,
`rightDerivedUpperShriekHomEquiv_naturality_right_symm`). -/
noncomputable def rightDerivedUpperShriekHomEquiv
    {K : DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)}
    (hK : DerivedCategory.plusEtaleOrigin A X K)
    {L : DerivedCategory (Sheaf (Scheme.ProEt.topology Y) A)}
    (hL : DerivedCategory.TStructure.t.plus L) :
    ((ProEtale.rightDerivedLowerShriek A f).obj K ⟶ L) ≃ (K ⟶ (R(f)^![A]).obj L) :=
  (Equiv.ofBijective _ (bijective_rightDerivedLowerShriek_map_comp_counit f hK hL)).symm

@[simp]
lemma rightDerivedUpperShriekHomEquiv_symm_apply
    {K : DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)}
    (hK : DerivedCategory.plusEtaleOrigin A X K)
    {L : DerivedCategory (Sheaf (Scheme.ProEt.topology Y) A)}
    (hL : DerivedCategory.TStructure.t.plus L) (g : K ⟶ (R(f)^![A]).obj L) :
    (rightDerivedUpperShriekHomEquiv f hK hL).symm g =
      (ProEtale.rightDerivedLowerShriek A f).map g ≫ rightDerivedUpperShriekCounit f L hL :=
  rfl

/-- The counit is the image of the identity under the exceptional adjunction. -/
lemma rightDerivedUpperShriekHomEquiv_symm_id
    {L : DerivedCategory (Sheaf (Scheme.ProEt.topology Y) A)}
    (hL : DerivedCategory.TStructure.t.plus L) :
    (rightDerivedUpperShriekHomEquiv f (plusEtaleOrigin_rightDerivedUpperShriek_obj f hL) hL).symm
        (𝟙 _) = rightDerivedUpperShriekCounit f L hL := by
  simp

/-- Naturality of the exceptional adjunction in the source. -/
lemma rightDerivedUpperShriekHomEquiv_naturality_left_symm
    {K K' : DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)}
    (hK : DerivedCategory.plusEtaleOrigin A X K) (hK' : DerivedCategory.plusEtaleOrigin A X K')
    {L : DerivedCategory (Sheaf (Scheme.ProEt.topology Y) A)}
    (hL : DerivedCategory.TStructure.t.plus L) (φ : K ⟶ K') (g : K' ⟶ (R(f)^![A]).obj L) :
    (rightDerivedUpperShriekHomEquiv f hK hL).symm (φ ≫ g) =
      (ProEtale.rightDerivedLowerShriek A f).map φ ≫
        (rightDerivedUpperShriekHomEquiv f hK' hL).symm g := by
  simp

/-- Naturality of the exceptional adjunction in the target. -/
lemma rightDerivedUpperShriekHomEquiv_naturality_right_symm
    {K : DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)}
    (hK : DerivedCategory.plusEtaleOrigin A X K)
    {L L' : DerivedCategory (Sheaf (Scheme.ProEt.topology Y) A)}
    (hL : DerivedCategory.TStructure.t.plus L) (hL' : DerivedCategory.TStructure.t.plus L')
    (g : K ⟶ (R(f)^![A]).obj L) (φ : L ⟶ L') :
    (rightDerivedUpperShriekHomEquiv f hK hL').symm (g ≫ (R(f)^![A]).map φ) =
      (rightDerivedUpperShriekHomEquiv f hK hL).symm g ≫ φ := by
  simp [rightDerivedUpperShriekCounit_naturality f hL hL']

/-- Naturality of the exceptional adjunction in the source, forward direction. -/
lemma rightDerivedUpperShriekHomEquiv_naturality_left
    {K K' : DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)}
    (hK : DerivedCategory.plusEtaleOrigin A X K) (hK' : DerivedCategory.plusEtaleOrigin A X K')
    {L : DerivedCategory (Sheaf (Scheme.ProEt.topology Y) A)}
    (hL : DerivedCategory.TStructure.t.plus L) (φ : K ⟶ K')
    (g : (ProEtale.rightDerivedLowerShriek A f).obj K' ⟶ L) :
    rightDerivedUpperShriekHomEquiv f hK hL ((ProEtale.rightDerivedLowerShriek A f).map φ ≫ g) =
      φ ≫ rightDerivedUpperShriekHomEquiv f hK' hL g := by
  rw [← Equiv.eq_symm_apply, rightDerivedUpperShriekHomEquiv_naturality_left_symm f hK hK',
    Equiv.symm_apply_apply]

/-- Naturality of the exceptional adjunction in the target, forward direction. -/
lemma rightDerivedUpperShriekHomEquiv_naturality_right
    {K : DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)}
    (hK : DerivedCategory.plusEtaleOrigin A X K)
    {L L' : DerivedCategory (Sheaf (Scheme.ProEt.topology Y) A)}
    (hL : DerivedCategory.TStructure.t.plus L) (hL' : DerivedCategory.TStructure.t.plus L')
    (g : (ProEtale.rightDerivedLowerShriek A f).obj K ⟶ L) (φ : L ⟶ L') :
    rightDerivedUpperShriekHomEquiv f hK hL' (g ≫ φ) =
      rightDerivedUpperShriekHomEquiv f hK hL g ≫ (R(f)^![A]).map φ := by
  rw [← Equiv.eq_symm_apply, rightDerivedUpperShriekHomEquiv_naturality_right_symm f hK hL hL',
    Equiv.symm_apply_apply]

/-- Blueprint `sk-prop-sf-existence` (c), on full subcategories: if `P` is a property of
objects of `D(X_proét)` contained in the bounded below objects of étale origin and `Q` a property
of objects of `D(Y_proét)` contained in the bounded below objects, such that `Rf_!` sends `P` to
`Q` and `Rf^!` sends `Q` to `P`, then the restrictions of `Rf_!` and `Rf^!` to the full
subcategories of `P` and `Q` are adjoint. This applies to the bounded constructible objects of
finite Tor amplitude. -/
noncomputable def rightDerivedUpperShriekAdjunction
    (P : ObjectProperty (DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)))
    (Q : ObjectProperty (DerivedCategory (Sheaf (Scheme.ProEt.topology Y) A)))
    (hP : P ≤ DerivedCategory.plusEtaleOrigin A X) (hQ : Q ≤ DerivedCategory.TStructure.t.plus)
    (h₁ : ∀ K, P K → Q ((ProEtale.rightDerivedLowerShriek A f).obj K))
    (h₂ : ∀ L, Q L → P ((R(f)^![A]).obj L)) :
    Q.lift (P.ι ⋙ ProEtale.rightDerivedLowerShriek A f) (fun K ↦ h₁ _ K.property) ⊣
      P.lift (Q.ι ⋙ R(f)^![A]) (fun L ↦ h₂ _ L.property) :=
  Adjunction.mkOfHomEquiv
    { homEquiv K L :=
        { toFun g := ObjectProperty.homMk
            (rightDerivedUpperShriekHomEquiv f (hP _ K.property) (hQ _ L.property) g.hom)
          invFun g := ObjectProperty.homMk
            ((rightDerivedUpperShriekHomEquiv f (hP _ K.property) (hQ _ L.property)).symm g.hom)
          left_inv g := by
            ext
            exact (rightDerivedUpperShriekHomEquiv f _ _).symm_apply_apply g.hom
          right_inv g := by
            ext
            exact (rightDerivedUpperShriekHomEquiv f _ _).apply_symm_apply g.hom }
      homEquiv_naturality_left_symm {K K' L} φ g := by
        ext
        exact rightDerivedUpperShriekHomEquiv_naturality_left_symm f _ _ _ φ.hom g.hom
      homEquiv_naturality_right {K L L'} g φ := by
        ext
        exact rightDerivedUpperShriekHomEquiv_naturality_right f _ _ _ g.hom φ.hom }

end Adjunction

end ProEtale

end AlgebraicGeometry
