/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan, Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.UpperShriek
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriekComparison

/-!

# Derived Upper Shriek

This is the pro-étale counterpart of
`WeilConjectures.SixFunctors.Etale.Derived.UpperShriek`.

The pro-étale derived lower shriek `Rf_!` is in general *not* a left adjoint, not even on `D⁺`:
for the structure morphism of an elliptic curve over `𝔽̄_p` and `𝔽_r`-module coefficients with
`r ≠ p`, `Rf_! = Rf_*` does not preserve coproducts (blueprint `sk-rem-sf-fullcd-scope`; see
`WeilConjectures.SixFunctors.ProEtale.ExceptionalAdjoint`). So the exceptional inverse image is
not defined as a right adjoint. Following blueprint `det-def-sf-operations` (vi), it is the
*constructible* exceptional inverse image, the étale right adjoint transported along the
comparison:

`Rf^! := ν_X^* ∘ f^× ∘ Rν_{Y,*} : D(Y_proét) ⥤ D(X_proét)`,

where `f^× = AlgebraicGeometry.Etale.rightDerivedUpperShriek` is the right adjoint of the étale
`Rf_!`. Its defining property is a theorem, not a hypothesis (an earlier form of blueprint
`sk-prop-sf-existence`): for `K` bounded below of étale origin and `L` bounded below,
`Hom(Rf_! K, L) ≃ Hom(K, Rf^! L)`, naturally in both
(`AlgebraicGeometry.ProEtale.rightDerivedUpperShriekHomEquiv`). Every bounded constructible
object is bounded below of étale origin, so the adjunction holds on the constructible
categories.

# Main Results

- `AlgebraicGeometry.ProEtale.rightDerivedUpperShriek` : `Rf^! : D(Y_proét) ⥤ D(X_proét)`,
  with scoped notation `R(f)^![Λ]`.
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
  the restriction of `R(f)^![Λ]`, with scoped notation `R(f)^![Λ]+`.

## Implementation notes

* `Rf^!` is defined by the same formula on the whole unbounded derived category, but it is only
  meaningful on `D⁺(Y_proét)`, where the blueprint defines it: the adjunction is only asserted for
  bounded below objects.
* The bijectivity in `rightDerivedUpperShriekHomEquiv` is the chain of bijections of the proof of
  an earlier form of blueprint `sk-prop-sf-existence`: the compact-support comparison
  `AlgebraicGeometry.ProEtale.rightDerivedLowerShriekComparisonIso`, the adjunction
  `ν^* ⊣ Rν_*`, the étale adjunction `Rf_! ⊣ f^×` and the full faithfulness of `ν^*` on `D⁺`
  (`AlgebraicGeometry.ProEtale.bijective_comparisonUpperStar_mapDerivedCategory_map`).
* The ambient right adjoint of `Rf_!` on all of `D(X_proét)` is not defined
  here: it does not exist for proper curves. The right adjoint of blueprint
  `sk-prop-sf-existence` lives on the localizing closures `Loc(Dctf)`, see
  `AlgebraicGeometry.ProEtale.rightDerivedUpperShriekLocalizing` in
  `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperShriekLocalizing`.
* The definition uses the étale exceptional inverse image `f^× = Rf^!` at a finite coefficient
  ring `Λ` (`AlgebraicGeometry.Etale.rightDerivedUpperShriek`). The results on bounded below
  objects and the adjunction take `[CompactSpace Y]`, under which `f^×` preserves bounded below
  objects (`AlgebraicGeometry.Etale.plus_rightDerivedUpperShriek_obj`); this rests on the finite
  cohomological amplitude of proper direct images.

-/

@[expose] public section

universe u' u

open CategoryTheory Abelian Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]

namespace ProEtale

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f]

section Definition

/-- Blueprint `det-def-sf-operations` (vi) and blueprint `def-weil-exceptional-inverse-image`:
(at a finite stage `A = A_{E,n}`) the exceptional inverse image
`Rf^! := ν_X^* ∘ f^× ∘ Rν_{Y,*} : D(Y_proét) ⥤ D(X_proét)` along a morphism `f : X ⟶ Y`
admitting a compactification, where `f^×` is the étale exceptional inverse image
`AlgebraicGeometry.Etale.rightDerivedUpperShriek`, the right adjoint of the étale `Rf_!`. It is
the constructible exceptional inverse image of the blueprint, meaningful on bounded below
complexes, where it is right adjoint to `Rf_!` on objects of étale origin
(`AlgebraicGeometry.ProEtale.rightDerivedUpperShriekHomEquiv`). For `f` separated of finite type
over a finite-type scheme over a field, it carries `D_c^[a, b]` into `D_c^[a - 2D, b + 2 dim Y + 1]`
and Tor amplitude `[a, b]` to `[a - 2D, b + 2 dim Y + 1]`, with `D` independent of the stage
(`AlgebraicGeometry.ProEtale.exists_preservationClauses`). -/
noncomputable def rightDerivedUpperShriek :
    DerivedCategory (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} Λ)) ⥤
      DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)) :=
  R(ν_*(Y)[ModuleCat.{u + 1} Λ]) ⋙ Etale.rightDerivedUpperShriek Λ f ⋙ D(ν^*(X)[ModuleCat.{u + 1}
      Λ])

@[inherit_doc rightDerivedUpperShriek]
scoped notation "R(" f ")^![" A "]" =>
  rightDerivedUpperShriek A f

end Definition

section BoundedBelow

variable {A} {Λ} [CompactSpace Y]

omit [CompactSpace Y] in
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
    {L : DerivedCategory (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} Λ))}
    (hL : DerivedCategory.TStructure.t.plus L) :
    DerivedCategory.TStructure.t.plus
      ((Etale.rightDerivedUpperShriek Λ f).obj (R(ν_*(Y)[ModuleCat.{u + 1} Λ]).obj L)) :=
  Etale.plus_rightDerivedUpperShriek_obj Λ f _ (plus_rightDerivedFunctor_comparisonLowerStar_obj hL)

/-- `Rf^!` sends a bounded below object to an object bounded below of étale origin. -/
lemma plusEtaleOrigin_rightDerivedUpperShriek_obj
    {L : DerivedCategory (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} Λ))}
    (hL : DerivedCategory.TStructure.t.plus L) :
    DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} Λ) X ((R(f)^![Λ]).obj L) :=
  DerivedCategory.plusEtaleOrigin_mapDerivedCategory_obj
    (plus_etaleRightDerivedUpperShriek_obj f hL)

/-- The exceptional inverse image `Rf^!` preserves bounded below objects. -/
lemma plus_rightDerivedUpperShriek_obj
    {L : DerivedCategory (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} Λ))}
    (hL : DerivedCategory.TStructure.t.plus L) :
    DerivedCategory.TStructure.t.plus ((R(f)^![Λ]).obj L) :=
  (plusEtaleOrigin_rightDerivedUpperShriek_obj f hL).plus

variable (A) (Λ)

/-- The exceptional inverse image `Rf^! : D⁺(Y_proét) ⥤ D⁺(X_proét)` on the *bounded below*
derived categories of pro-étale sheaves: the restriction of `R(f)^![Λ]`, which is well defined
by `plus_rightDerivedUpperShriek_obj`. -/
noncomputable def rightDerivedUpperShriekPlus :
    DerivedCategory.Plus (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} Λ)) ⥤
      DerivedCategory.Plus (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)) :=
  DerivedCategory.TStructure.t.plus.lift (DerivedCategory.Plus.ι ⋙ R(f)^![Λ])
    (fun K ↦ plus_rightDerivedUpperShriek_obj f K.property)

@[inherit_doc rightDerivedUpperShriekPlus]
scoped notation "R(" f ")^![" A "]+" =>
  rightDerivedUpperShriekPlus A f

end BoundedBelow

section Adjunction

/- The adjunction `ν^* ⊣ Rν_*` on the unbounded derived categories is obtained by deriving the
pullback via K-flat resolutions, hence the closed symmetric monoidal structure on `A`. -/
variable [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A] [CompactSpace Y]

variable {A} {Λ}

end Adjunction

end ProEtale

end AlgebraicGeometry
