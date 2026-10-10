/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.CategoryTheory.Adjunction.Restrict
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.PAdicAlgCl.Derived.LowerShriek
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.PAdicAlgCl.Derived.OpenImmersionLowerShriek

/-!

# Derived upper shriek on module objects over `ℚ̄_ℓ`

This is the module-object counterpart of
`WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperShriek`, for the
coefficient ring objects `ℚ̄_ℓ,X` of `WeilConjectures.CategoryTheory.RingObjects.EllAdic`.

As there, the exceptional inverse image `Rf^!` along a morphism `f : X ⟶ Y` admitting a
compactification is *constructed* out of the two halves of the derived lower shriek
`Rf_! = Di_! ⋙ Rg_*` attached to a compactification `c = (X ⟶[i] Z ⟶[g] Y)` of `f`:
```
Rf^! := Rg^! ⋙ Di^*,
```
where `Rg^!` is a chosen right adjoint of the derived pushforward `Rg_*` on module objects along
the *proper* morphism `g`, and `Di^*` is the levelwise pullback along the open immersion `i`,
which is right adjoint to `Di_!` by
`ProEtale.PadicAlgClRing.derivedOpenImmersionLowerShriekUpperStarAdjunction`. The adjunction
`Rf_! ⊣ Rf^!` is then the composite of these two adjunctions. The only input taken for granted
is that `Rg_*` on module objects is a left adjoint for proper `g`
(`ProEtale.PadicAlgClRing.isLeftAdjoint_rightDerivedLowerStar_of_isProper`); it is *not*
assumed that `Rf_!` is a left adjoint for a general `f`, that is a theorem here.

On the bounded below derived categories, `Rf^!` is the restriction of the unbounded `Rf^!`
along the inclusion `DerivedCategory.Plus.ι`, which makes sense because `Rf^!` preserves
bounded below objects; that the restriction is again a right adjoint, now of the bounded below
`Rf_!`, is then a theorem.

## Main results

- `ProEtale.PadicAlgClRing.isLeftAdjoint_rightDerivedLowerStar_of_isProper` : for `g`
  proper, `Rg_*` is a left adjoint on `D(Mod_{ℚ̄_ℓ,Z})`.
- `ProEtale.PadicAlgClRing.rightDerivedUpperShriekOfCompactification` : `Rf^!` with respect
  to a compactification `c`, with scoped notation `Rf^!(c)⟦ℚ̄_ℓ⟧`, and
  `ProEtale.PadicAlgClRing.rightDerivedUpperShriekOfCompactificationAdjunction` : the
  adjunction `Rf_!(c)⟦ℚ̄_ℓ⟧ ⊣ Rf^!(c)⟦ℚ̄_ℓ⟧`.
- `ProEtale.PadicAlgClRing.rightDerivedUpperShriek` : `Rf^! : D(Mod_{ℚ̄_ℓ,Y}) ⥤ D(Mod_{ℚ̄_ℓ,X})`
  for the chosen compactification, with scoped notation `R(f)^!⟦ℚ̄_ℓ⟧`, and
  `ProEtale.PadicAlgClRing.rightDerivedUpperShriekAdjunction` : the adjunction `Rf_! ⊣ Rf^!`
  on the unbounded derived categories;
  `ProEtale.PadicAlgClRing.isLeftAdjoint_rightDerivedLowerShriek` : `Rf_!` is a left adjoint.
- `ProEtale.PadicAlgClRing.rightDerivedUpperShriekPlus` : `Rf^!` on the bounded below derived
  categories, the restriction of `R(f)^!⟦ℚ̄_ℓ⟧`, with scoped notation `R(f)^!⟦ℚ̄_ℓ⟧+`, and
  `ProEtale.PadicAlgClRing.rightDerivedUpperShriekPlusAdjunction` : the adjunction `Rf_! ⊣ Rf^!`
  on the bounded below derived categories.

## Implementation notes

* `isLeftAdjoint_rightDerivedLowerStar_of_isProper` is `sorry` by design: this file only
  *states* that `Rg_*` has a right adjoint for `g` proper. The adjoint exists by Brown
  representability, `Rg_*` being, for `g` proper, a colimit preserving functor between
  compactly generated triangulated categories; alternatively it is obtained from the exceptional
  inverse image on abelian sheaves through the projection formula for the coefficient object
  `ℚ̄_ℓ,Y` and the coextension of scalars along `α_g`.
* `plus_rightDerivedUpperShriek_obj`, that `Rf^!` preserves bounded below objects, is also
  `sorry` for now.
* `Rg^!` for proper `g` is `Functor.rightAdjoint`, i.e. an arbitrary choice of right adjoint
  extracted from the instance, not a construction. Only the adjunction
  `Adjunction.ofIsLeftAdjoint` should be used about it. The composite `Rf^!` is a construction
  out of it and `Di^*`.
* By contrast with the unbounded `Rf^!`, the bounded below `R(f)^!⟦ℚ̄_ℓ⟧+` is a restriction of
  `R(f)^!⟦ℚ̄_ℓ⟧`: by `rightDerivedUpperShriekPlusCompatibility` it is compatible with the inclusions
  of the bounded below derived categories by definition.
* There is no underived `f^!`, but the notation still carries the `R` of `R(f)_!⟦ℚ̄_ℓ⟧` and
  `R((g)_*⟦ℚ̄_ℓ⟧)`, to mark that it lives on derived categories rather than on module objects.

-/

@[expose] public section

universe u

open CategoryTheory Abelian Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.PadicAlgClRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime]

section Proper

variable {Z Y : Scheme.{u}} (g : Z ⟶ Y) [IsProper g]

/-- For a proper morphism `g : Z ⟶ Y`, the derived pushforward
`Rg_* : D(Mod_{ℚ̄_ℓ,Z}) ⥤ D(Mod_{ℚ̄_ℓ,Y})` on module objects over `ℚ̄_ℓ` is a left adjoint;
its right adjoint is the exceptional inverse image `Rg^!` along `g`. -/
instance isLeftAdjoint_rightDerivedLowerStar_of_isProper : R((g)_*⟦ℚ̄_ℓ⟧).IsLeftAdjoint :=
  sorry

end Proper

section OfCompactification

variable {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)

/-- The exceptional inverse image `Rf^! : D(Mod_{ℚ̄_ℓ,Y}) ⥤ D(Mod_{ℚ̄_ℓ,X})` attached to a
compactification `c = (X ⟶[i] Z ⟶[g] Y)` of `f`, on the unbounded derived categories of module
objects over `ℚ̄_ℓ`: a chosen right adjoint `Rg^!` of the derived pushforward `Rg_*` along the
proper `g`, followed by the levelwise pullback `Di^*` along the open immersion `i`. -/
noncomputable def rightDerivedUpperShriekOfCompactification :
    DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (padicAlgClSheaf Y ℓ)) ⥤
      DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (padicAlgClSheaf X ℓ)) :=
  R((c.g)_*⟦ℚ̄_ℓ⟧).rightAdjoint ⋙ D((c.i)^*⟦ℚ̄_ℓ⟧)

@[inherit_doc rightDerivedUpperShriekOfCompactification]
scoped notation "Rf^!(" c ")⟦ℚ̄_" ℓ "⟧" => rightDerivedUpperShriekOfCompactification ℓ c

/-- The adjunction `Rf_! ⊣ Rf^!` attached to a compactification `c = (X ⟶[i] Z ⟶[g] Y)` of `f`:
the composite of the derived adjunction `Di_! ⊣ Di^*` along the open immersion `i` and of the
adjunction `Rg_* ⊣ Rg^!` along the proper `g`. -/
noncomputable def rightDerivedUpperShriekOfCompactificationAdjunction :
    Rf_!(c)⟦ℚ̄_ℓ⟧ ⊣ Rf^!(c)⟦ℚ̄_ℓ⟧ :=
  (derivedOpenImmersionLowerShriekUpperStarAdjunction ℓ c.i).comp (Adjunction.ofIsLeftAdjoint _)

end OfCompactification

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f]

section Unbounded

/-- The exceptional inverse image `Rf^! : D(Mod_{ℚ̄_ℓ,Y}) ⥤ D(Mod_{ℚ̄_ℓ,X})` along a morphism
`f : X ⟶ Y` admitting a compactification, on the unbounded derived categories of module objects
over `ℚ̄_ℓ`: the functor `rightDerivedUpperShriekOfCompactification` attached to the chosen
compactification `HasCompactification.compactification f`. -/
noncomputable def rightDerivedUpperShriek :
    DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (padicAlgClSheaf Y ℓ)) ⥤
      DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (padicAlgClSheaf X ℓ)) :=
  Rf^!(HasCompactification.compactification f)⟦ℚ̄_ℓ⟧

@[inherit_doc rightDerivedUpperShriek]
scoped notation "R(" f ")^!⟦ℚ̄_" ℓ "⟧" => rightDerivedUpperShriek ℓ f

lemma rightDerivedUpperShriek_eq :
    R(f)^!⟦ℚ̄_ℓ⟧ = Rf^!(HasCompactification.compactification f)⟦ℚ̄_ℓ⟧ := rfl

/-- The adjunction `Rf_! ⊣ Rf^!` on the unbounded derived categories of module objects. -/
noncomputable def rightDerivedUpperShriekAdjunction : R(f)_!⟦ℚ̄_ℓ⟧ ⊣ R(f)^!⟦ℚ̄_ℓ⟧ :=
  rightDerivedUpperShriekOfCompactificationAdjunction ℓ (HasCompactification.compactification f)

/-- The derived lower shriek `Rf_!` on module objects is a left adjoint, its right adjoint being
`R(f)^!⟦ℚ̄_ℓ⟧`. -/
instance isLeftAdjoint_rightDerivedLowerShriek : (R(f)_!⟦ℚ̄_ℓ⟧).IsLeftAdjoint :=
  (rightDerivedUpperShriekAdjunction ℓ f).isLeftAdjoint

instance : (R(f)^!⟦ℚ̄_ℓ⟧).IsRightAdjoint := (rightDerivedUpperShriekAdjunction ℓ f).isRightAdjoint

end Unbounded

section BoundedBelow

/-- The exceptional inverse image `Rf^!` on module objects preserves bounded below objects: if
`K ∈ D(Mod_{ℚ̄_ℓ,Y})` is bounded below, then so is `Rf^! K`. As in the finite-coefficient case
the bound is shifted by the cohomological amplitude of `Rf_!`, which is why the statement is
about `t.plus` rather than about `IsGE n` for a fixed `n`. -/
lemma plus_rightDerivedUpperShriek_obj
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (padicAlgClSheaf Y ℓ)))
    (hK : DerivedCategory.TStructure.t.plus K) :
    DerivedCategory.TStructure.t.plus ((R(f)^!⟦ℚ̄_ℓ⟧).obj K) := sorry

/-- The exceptional inverse image `Rf^! : D⁺(Mod_{ℚ̄_ℓ,Y}) ⥤ D⁺(Mod_{ℚ̄_ℓ,X})` on the *bounded
below* derived categories of module objects: the restriction of the unbounded `R(f)^!⟦ℚ̄_ℓ⟧` along
the inclusions of the bounded below derived categories, which is well defined by
`plus_rightDerivedUpperShriek_obj`. -/
noncomputable def rightDerivedUpperShriekPlus :
    DerivedCategory.Plus (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (padicAlgClSheaf Y ℓ)) ⥤
      DerivedCategory.Plus (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (padicAlgClSheaf X ℓ)) :=
  DerivedCategory.TStructure.t.plus.lift (DerivedCategory.Plus.ι ⋙ R(f)^!⟦ℚ̄_ℓ⟧)
    (fun K ↦ plus_rightDerivedUpperShriek_obj ℓ f K.obj K.property)

@[inherit_doc rightDerivedUpperShriekPlus]
scoped notation "R(" f ")^!⟦ℚ̄_" ℓ "⟧+" => rightDerivedUpperShriekPlus ℓ f

/-- The bounded below `R(f)^!⟦ℚ̄_ℓ⟧+` is compatible with the inclusions of the bounded below
derived categories, by construction. -/
noncomputable def rightDerivedUpperShriekPlusCompatibility :
    R(f)^!⟦ℚ̄_ℓ⟧+ ⋙ DerivedCategory.Plus.ι ≅ DerivedCategory.Plus.ι ⋙ R(f)^!⟦ℚ̄_ℓ⟧ :=
  ObjectProperty.liftCompιIso _ _ _

/-- The adjunction `Rf_! ⊣ Rf^!` on the bounded below derived categories of module objects: the
unbounded adjunction restricted along the fully faithful inclusions `DerivedCategory.Plus.ι`,
which is legitimate since both `Rf_!` and `Rf^!` preserve bounded below objects. -/
noncomputable def rightDerivedUpperShriekPlusAdjunction : R(f)_!⟦ℚ̄_ℓ⟧+ ⊣ R(f)^!⟦ℚ̄_ℓ⟧+ :=
  Adjunction.restrictFullyFaithful (rightDerivedUpperShriekAdjunction ℓ f)
    (ObjectProperty.fullyFaithfulι _) (ObjectProperty.fullyFaithfulι _)
    (rightDerivedLowerShriekPlusCompatibility ℓ f).symm
    (rightDerivedUpperShriekPlusCompatibility ℓ f).symm

/-- The derived lower shriek `Rf_!` on the bounded below derived categories of module objects
is a left adjoint, its right adjoint being `R(f)^!⟦ℚ̄_ℓ⟧+`. -/
instance isLeftAdjoint_rightDerivedLowerShriekPlus : (R(f)_!⟦ℚ̄_ℓ⟧+).IsLeftAdjoint :=
  (rightDerivedUpperShriekPlusAdjunction ℓ f).isLeftAdjoint

instance : (R(f)^!⟦ℚ̄_ℓ⟧+).IsRightAdjoint :=
  (rightDerivedUpperShriekPlusAdjunction ℓ f).isRightAdjoint

end BoundedBelow

end AlgebraicGeometry.ProEtale.PadicAlgClRing
