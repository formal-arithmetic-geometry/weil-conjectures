/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.Complete.OECoefficient
public import Mathlib.Algebra.Homology.DerivedCategory.Linear
public import Mathlib.Algebra.Module.LocalizedModule.Basic
public import Mathlib.Tactic.Module

/-!

# Derived complete objects with coefficients in an `ℓ`-adic field

Let `E` be a finite extension of `ℚ_ℓ` with ring of integers `𝒪_E`. This file passes from
the integral category `D_comp(J, 𝒪_E)` of `WeilConjectures.CategoryTheory.DerivedCategory.
Complete.OECoefficient` to the category with `E`-coefficients

```
  D_comp(J, E)  :=  D_comp(J, 𝒪_E) ⊗_{𝒪_E} E,
```

which has the same objects as `D_comp(J, 𝒪_E)` and whose `Hom` groups are the localizations

```
  Hom_{D_comp(J, E)}(K, L)  =  Hom_{D_comp(J, 𝒪_E)}(K, L) ⊗_{𝒪_E} E.
```

## Inverting the nonzero elements of `𝒪_E`

Tensoring the `Hom` groups with `E = Frac(𝒪_E)` over `𝒪_E` is localizing them at the
nonzero elements `nonZeroDivisors 𝒪_E`, which is what is done here. Since `𝒪_E` is a
discrete valuation ring in which `ℓ` is a nonzero element of the maximal ideal, every
nonzero element of `𝒪_E` divides a power of `ℓ`, so this is the same as inverting `ℓ` alone:
`D_comp(J, E) = D_comp(J, 𝒪_E)[1/ℓ]`. Inverting all nonzero elements, rather than `ℓ` or a
uniformizer `ϖ_E`, keeps `ℓ` out of the type of the category, as in
`WeilConjectures.CategoryTheory.DerivedCategory.Complete.OECoefficient`, and makes the
`E`-linear structure come directly from `IsFractionRing 𝒪[E] E`.

The construction is the general `CategoryTheory.Rationalization`: for an `R`-linear
category `C` and a submonoid `M` of `R`, `Rationalization M C` has the objects of `C` and
the localized modules `(X ⟶ Y)[M⁻¹]` as `Hom` groups; equivalently it is obtained from `C`
by inverting the morphisms `m • 𝟙 X` for `m ∈ M`. It is `A`-linear for every localization
`A` of `R` at `M`. Here `R = 𝒪_E` (in its universe `u + 1` copy `ULift 𝒪[E]`) and
`M = nonZeroDivisors R`.

## Main definitions

- `CategoryTheory.Rationalization` : the rationalization of an `R`-linear category at a
  submonoid of `R`, with its `Category`, `Preadditive` and `Linear` instances.
- `CategoryTheory.Rationalization.toRationalization` : the canonical additive functor
  `C ⥤ Rationalization M C`.
- `ValuativeRel.algebraULift`, `ValuativeRel.isFractionRing_uLift` : `E` is the fraction
  field of the universe `u + 1` copy `ULift 𝒪[E]` of its ring of integers.
- `DerivedCategoryDerivedCompleteE` : the category `D_comp(J, E) = D_comp(J, 𝒪_E) ⊗ E`.
- `DerivedCategoryDerivedCompleteE.fromOE` : the functor `D_comp(J, 𝒪_E) ⥤ D_comp(J, E)`,
  the identity on objects and `f ↦ f / 1` on morphisms.

-/

@[expose] public section

universe uA uR v u

open CategoryTheory Limits ValuativeRel

namespace CategoryTheory

open Category

variable {R : Type uR} [CommRing R]

/-- The rationalization of an `R`-linear category at a submonoid `M` of `R`: the objects
are those of `C`, and the morphisms are the localizations `(X ⟶ Y)[M⁻¹]`. -/
structure Rationalization (M : Submonoid R) (C : Type u) [Category.{v} C] [Preadditive C]
    [Linear R C] where
  /-- The underlying object of `C`. -/
  as : C

namespace Rationalization

variable {M : Submonoid R} {C : Type u} [Category.{v} C] [Preadditive C] [Linear R C]

section Comp

variable {X Y Z : Rationalization M C}

/-- Composition of morphisms of the rationalization: `(f / m) ≫ (g / n) = (f ≫ g) / (m n)`. -/
noncomputable def comp (x : LocalizedModule M (X.as ⟶ Y.as))
    (y : LocalizedModule M (Y.as ⟶ Z.as)) : LocalizedModule M (X.as ⟶ Z.as) :=
  LocalizedModule.liftOn x
    (fun p ↦ LocalizedModule.liftOn y
      (fun q ↦ LocalizedModule.mk (p.1 ≫ q.1) (p.2 * q.2))
      (fun q q' hq ↦ by
        obtain ⟨u, hu⟩ := hq
        refine LocalizedModule.mk_eq.mpr ⟨u, ?_⟩
        simp only [Submonoid.smul_def, Submonoid.coe_mul, smul_smul, ← Linear.comp_smul] at hu ⊢
        have h := congrArg (fun z : Y.as ⟶ Z.as ↦ (p.2 : R) • z) hu
        simp only [smul_smul] at h
        congr 1
        rw [show (u : R) * ((p.2 : R) * (q'.2 : R)) = (p.2 : R) * ((u : R) * (q'.2 : R)) by ring,
          show (u : R) * ((p.2 : R) * (q.2 : R)) = (p.2 : R) * ((u : R) * (q.2 : R)) by ring]
        exact h))
    (fun p p' hp ↦ by
      obtain ⟨u, hu⟩ := hp
      induction y using LocalizedModule.induction_on with | h g n
      simp only [LocalizedModule.liftOn_mk]
      refine LocalizedModule.mk_eq.mpr ⟨u, ?_⟩
      simp only [Submonoid.smul_def, Submonoid.coe_mul, smul_smul, ← Linear.smul_comp] at hu ⊢
      have h := congrArg (fun z : X.as ⟶ Y.as ↦ (n : R) • z) hu
      simp only [smul_smul] at h
      congr 1
      rw [show (u : R) * ((p'.2 : R) * (n : R)) = (n : R) * ((u : R) * (p'.2 : R)) by ring,
        show (u : R) * ((p.2 : R) * (n : R)) = (n : R) * ((u : R) * (p.2 : R)) by ring]
      exact h)

lemma comp_mk (f : X.as ⟶ Y.as) (m : M) (g : Y.as ⟶ Z.as) (n : M) :
    comp (LocalizedModule.mk f m) (LocalizedModule.mk g n) =
      LocalizedModule.mk (f ≫ g) (m * n) := by
  simp only [comp, LocalizedModule.liftOn_mk]

end Comp

noncomputable instance category : Category (Rationalization M C) where
  Hom X Y := LocalizedModule M (X.as ⟶ Y.as)
  id X := LocalizedModule.mk (𝟙 X.as) 1
  comp := comp
  id_comp {X Y} x := by
    induction x using LocalizedModule.induction_on with | h f m
    change comp (LocalizedModule.mk (𝟙 X.as) 1) _ = _
    rw [comp_mk]
    simp
  comp_id {X Y} x := by
    induction x using LocalizedModule.induction_on with | h f m
    change comp _ (LocalizedModule.mk (𝟙 Y.as) 1) = _
    rw [comp_mk]
    simp
  assoc {X Y Z W} x y z := by
    induction x using LocalizedModule.induction_on with | h f m
    induction y using LocalizedModule.induction_on with | h g n
    induction z using LocalizedModule.induction_on with | h h' p
    change comp (comp _ _) _ = comp _ (comp _ _)
    rw [comp_mk, comp_mk, comp_mk, comp_mk, Category.assoc, mul_assoc]

/-- The morphism `f / m` of the rationalization. -/
abbrev homMk {X Y : Rationalization M C} (f : X.as ⟶ Y.as) (m : M) : X ⟶ Y :=
  LocalizedModule.mk f m

@[simp]
lemma homMk_comp_homMk {X Y Z : Rationalization M C} (f : X.as ⟶ Y.as) (m : M)
    (g : Y.as ⟶ Z.as) (n : M) : homMk f m ≫ homMk g n = homMk (f ≫ g) (m * n) :=
  comp_mk f m g n

@[simp]
lemma id_eq (X : Rationalization M C) : 𝟙 X = homMk (𝟙 X.as) 1 := rfl

lemma homMk_eq_homMk_iff {X Y : Rationalization M C} (f f' : X.as ⟶ Y.as) (m m' : M) :
    homMk f m = homMk f' m' ↔ ∃ u : M, u • m' • f = u • m • f' :=
  LocalizedModule.mk_eq

/-- Every morphism of the rationalization is of the form `f / m`. -/
@[elab_as_elim]
lemma homMk_induction {X Y : Rationalization M C} {P : (X ⟶ Y) → Prop}
    (h : ∀ (f : X.as ⟶ Y.as) (m : M), P (homMk f m)) (x : X ⟶ Y) : P x :=
  LocalizedModule.induction_on h x

noncomputable instance homAddCommGroup (X Y : Rationalization M C) : AddCommGroup (X ⟶ Y) :=
  inferInstanceAs (AddCommGroup (LocalizedModule M (X.as ⟶ Y.as)))

@[simp]
lemma homMk_add_homMk {X Y : Rationalization M C} (f f' : X.as ⟶ Y.as) (m m' : M) :
    homMk f m + homMk f' m' = homMk (m' • f + m • f') (m * m') :=
  LocalizedModule.mk_add_mk

noncomputable instance preadditive : Preadditive (Rationalization M C) where
  homGroup := homAddCommGroup
  add_comp P Q S' x x' y := by
    induction x using homMk_induction with | _ f m
    induction x' using homMk_induction with | _ f' m'
    induction y using homMk_induction with | _ g n
    rw [homMk_add_homMk, homMk_comp_homMk, homMk_comp_homMk, homMk_comp_homMk,
      homMk_add_homMk]
    simp only [Preadditive.add_comp, Submonoid.smul_def, Linear.smul_comp]
    refine (homMk_eq_homMk_iff _ _ _ _).2 ⟨1, ?_⟩
    simp only [Submonoid.smul_def, Submonoid.coe_mul, one_smul, smul_add, smul_smul]
    module
  comp_add P Q S' x y y' := by
    induction x using homMk_induction with | _ f m
    induction y using homMk_induction with | _ g n
    induction y' using homMk_induction with | _ g' n'
    rw [homMk_add_homMk, homMk_comp_homMk, homMk_comp_homMk, homMk_comp_homMk,
      homMk_add_homMk]
    simp only [Preadditive.comp_add, Submonoid.smul_def, Linear.comp_smul]
    refine (homMk_eq_homMk_iff _ _ _ _).2 ⟨1, ?_⟩
    simp only [Submonoid.smul_def, Submonoid.coe_mul, one_smul, smul_add, smul_smul]
    module

/-- The canonical functor from `C` to its rationalization. -/
@[simps]
noncomputable def toRationalization : C ⥤ Rationalization M C where
  obj X := ⟨X⟩
  map f := homMk f 1
  map_id X := rfl
  map_comp f g := by rw [homMk_comp_homMk, mul_one]

instance : (toRationalization (M := M) (C := C)).Additive where
  map_add {X Y f g} := by
    simp only [toRationalization_map, homMk_add_homMk, mul_one]
    refine ((homMk_eq_homMk_iff _ _ _ _).2 ⟨1, ?_⟩).symm
    simp only [one_smul, smul_add]

section Linear

variable (A : Type uA) [CommRing A] [Algebra R A] [IsLocalization M A]

/-- If `A` is a localization of `R` at `M` — for instance `A = E` and `M` the powers of
`ℓ` inside `𝒪_E` — then the rationalization is `A`-linear. -/
noncomputable instance linear : Linear A (Rationalization M C) where
  homModule _ _ := LocalizedModule.moduleOfIsLocalization (T := A)
  smul_comp X Y Z a x y := by
    induction x using homMk_induction with | _ f m
    induction y using homMk_induction with | _ g n
    obtain ⟨r, s, rfl⟩ : ∃ (r : R) (s : M), a = IsLocalization.mk' A r s :=
      ⟨_, _, (IsLocalization.mk'_sec A a).symm⟩
    rw [LocalizedModule.mk'_smul_mk, homMk_comp_homMk, homMk_comp_homMk,
      LocalizedModule.mk'_smul_mk, Linear.smul_comp, ← mul_assoc]
  comp_smul X Y Z x a y := by
    induction x using homMk_induction with | _ f m
    induction y using homMk_induction with | _ g n
    obtain ⟨r, s, rfl⟩ : ∃ (r : R) (s : M), a = IsLocalization.mk' A r s :=
      ⟨_, _, (IsLocalization.mk'_sec A a).symm⟩
    rw [LocalizedModule.mk'_smul_mk, homMk_comp_homMk, homMk_comp_homMk,
      LocalizedModule.mk'_smul_mk, Linear.comp_smul, mul_left_comm m s n]

end Linear

end Rationalization

end CategoryTheory

section RingOfIntegers

variable (E : Type) [Field E] [ValuativeRel E]

/-- `E` as an algebra over the universe `u + 1` copy `ULift 𝒪[E]` of its ring of integers.
The scalar action is the one of `ULift.module`, `r • x = r.down • x`. -/
noncomputable instance ValuativeRel.algebraULift : Algebra (ULift.{u + 1} 𝒪[E]) E where
  algebraMap := (algebraMap 𝒪[E] E).comp (ValuativeRel.uliftRingEquiv.{u} E).symm.toRingHom
  commutes' _ _ := mul_comm _ _
  smul_def' r x := Algebra.smul_def r.down x

/-- `E` is the fraction field of the universe `u + 1` copy `ULift 𝒪[E]` of its ring of
integers, as it is of `𝒪[E]` itself. -/
instance ValuativeRel.isFractionRing_uLift : IsFractionRing (ULift.{u + 1} 𝒪[E]) E :=
  IsFractionRing.of_ringEquiv_left (ValuativeRel.uliftRingEquiv.{u} E).symm fun _ ↦ rfl

end RingOfIntegers

section ECoefficient

variable {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
  (J : GrothendieckTopology C) (E : Type) [Field E] [ValuativeRel E]

noncomputable instance : Preadditive (DerivedCategoryDerivedCompleteOE J E) :=
  inferInstanceAs <| Preadditive (DerivedCategory.derivedCompleteOE J E).FullSubcategory

/-- The `Hom` groups of `D_comp(J, 𝒪_E)` are `𝒪_E`-modules, as those of `D(J, 𝒪_E)` are. -/
noncomputable instance : Linear (ULift.{u + 1} 𝒪[E]) (DerivedCategoryDerivedCompleteOE J E) :=
  inferInstanceAs <|
    Linear (ULift.{u + 1} 𝒪[E]) (DerivedCategory.derivedCompleteOE J E).FullSubcategory

/-- The category `D_comp(J, E)` of derived complete objects with coefficients in the
`ℓ`-adic field `E`: the rationalization of the category `D_comp(J, 𝒪_E)` of
`DerivedCategoryDerivedCompleteOE` obtained by inverting the nonzero elements of `𝒪_E` in
its `Hom` groups. Its objects are those of `D_comp(J, 𝒪_E)`, and its `Hom` groups are
`Hom(K, L) ⊗_{𝒪_E} E`; since `E = 𝒪_E[1/ℓ]`, this is `D_comp(J, 𝒪_E)[1/ℓ]`. -/
noncomputable def DerivedCategoryDerivedCompleteE : Type _ :=
  Rationalization (nonZeroDivisors (ULift.{u + 1} 𝒪[E])) (DerivedCategoryDerivedCompleteOE J E)

noncomputable instance : Category (DerivedCategoryDerivedCompleteE J E) :=
  inferInstanceAs <| Category <|
    Rationalization (nonZeroDivisors (ULift.{u + 1} 𝒪[E])) (DerivedCategoryDerivedCompleteOE J E)

noncomputable instance : Preadditive (DerivedCategoryDerivedCompleteE J E) :=
  inferInstanceAs <| Preadditive <|
    Rationalization (nonZeroDivisors (ULift.{u + 1} 𝒪[E])) (DerivedCategoryDerivedCompleteOE J E)

/-- The `Hom` groups of `D_comp(J, E)` are modules over any fraction field `A` of `𝒪_E`, in
particular over `E` itself (`ValuativeRel.isFractionRing_uLift`). -/
noncomputable instance (A : Type uA) [CommRing A] [Algebra (ULift.{u + 1} 𝒪[E]) A]
    [IsFractionRing (ULift.{u + 1} 𝒪[E]) A] :
    Linear A (DerivedCategoryDerivedCompleteE J E) :=
  inferInstanceAs <| Linear A <|
    Rationalization (nonZeroDivisors (ULift.{u + 1} 𝒪[E])) (DerivedCategoryDerivedCompleteOE J E)

/-- The `Hom` groups of `D_comp(J, E)` are `E`-vector spaces. -/
noncomputable example : Linear E (DerivedCategoryDerivedCompleteE J E) := inferInstance

/-- The functor `D_comp(J, 𝒪_E) ⥤ D_comp(J, E)`, the identity on objects and the
localization map `f ↦ f / 1` on morphisms. -/
noncomputable def DerivedCategoryDerivedCompleteE.fromOE :
    DerivedCategoryDerivedCompleteOE J E ⥤ DerivedCategoryDerivedCompleteE J E :=
  Rationalization.toRationalization

instance : (DerivedCategoryDerivedCompleteE.fromOE J E).Additive :=
  inferInstanceAs <| (Rationalization.toRationalization
    (M := nonZeroDivisors (ULift.{u + 1} 𝒪[E]))
    (C := DerivedCategoryDerivedCompleteOE J E)).Additive

end ECoefficient
