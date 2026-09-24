/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.Complete.Defs
public import Mathlib.Algebra.Homology.DerivedCategory.Linear
public import Mathlib.CategoryTheory.Shift.Linear
public import Mathlib.CategoryTheory.Triangulated.Subcategory
public import Mathlib.NumberTheory.LocalField.Basic
public import Mathlib.NumberTheory.Padics.ValuativeRel
public import Mathlib.RingTheory.AdicCompletion.Topology

/-!

# Derived complete objects with coefficients in the ring of integers of an `ℓ`-adic field

This file specializes `DerivedCategory.derivedComplete` of
`WeilConjectures.CategoryTheory.DerivedCategory.Complete.Defs` to the coefficient ring of
the integral stage of the `ℓ`-adic formalism: `E` is a finite extension of `ℚ_ℓ`, `𝒪_E` is
its ring of integers and `𝔪_E` is the maximal ideal of `𝒪_E`. For a site `(C, J)` it
defines the full subcategory

```
  D_comp(J, 𝒪_E)  ⊆  D(J, 𝒪_E) := DerivedCategory (Sheaf J (ModuleCat 𝒪_E))
```

of those objects that are derived complete for `𝔪_E`, together with its inclusion functor.

## The hypotheses on `E`

"`E` is a finite extension of `ℚ_ℓ`" is packaged as `IsFiniteExtensionPadic l E`, which
bundles

* `IsNonarchimedeanLocalField E` — `E` is a field whose topology comes from a valuation
  (`ValuativeRel E`) and which is locally compact and non-discrete. This is what supplies
  the ring of integers `𝒪_E := 𝒪[E]` and its maximal ideal `𝓂[E]`, the fact that `𝒪_E` is
  a discrete valuation ring and the completeness `IsAdicComplete 𝓂[E] 𝒪[E]`;
* `ValuativeExtension ℚ_[l] E` — the valuation of `E` restricts to the `ℓ`-adic valuation
  of `ℚ_ℓ`, so that `𝒪_E` is the ring of integers of `E` *over* `ℤ_ℓ` and not the valuation
  ring of some unrelated valuation;
* `Module.Finite ℚ_[l] E` — the extension is finite.

Only the first of the three is used by the constructions below, which are therefore stated
for a nonarchimedean local field `E`; since `IsFiniteExtensionPadic l E` implies
`IsNonarchimedeanLocalField E`, they apply verbatim to a finite extension of `ℚ_ℓ` without
`ℓ` — on which nothing below depends — appearing in the type of the resulting category.
The other two fields record what the intended instantiation is.

## Universes

`WeilConjectures.CategoryTheory.DerivedCategory.Complete.Defs` takes its site `(C, J)` with
objects in `Type (u + 1)` and morphisms in `Type u` — the shape of the small étale site of
a `Scheme.{u}` — and its coefficient ring in `Type (u + 1)`. A finite extension of `ℚ_ℓ`
lives in `Type 0`, so `𝒪_E` has to be moved up, and the coefficient ring used below is
`ULift.{u + 1} 𝒪[E]`. `ULift` carries all of the algebraic structure across, so no instance
has to be replayed by hand; the one fact that does need transporting, `IsAdicComplete`, is
transported along `ValuativeRel.uliftRingEquiv` by `IsAdicComplete.congr_ringEquiv`.

## Main definitions

- `IsFiniteExtensionPadic` : the bundled hypothesis "`E` is a finite extension of `ℚ_ℓ`".
- `ValuativeRel.uliftRingEquiv` and `ValuativeRel.maximalIdealULift` : the identification
  of `𝒪_E` with its copy in `Type (u + 1)`, and the maximal ideal `𝔪_E` read in that copy.
- `DerivedCategory.derivedCompleteOE` : the property of an object of `D(J, 𝒪_E)` of being
  derived complete with respect to `𝔪_E`.
- `DerivedCategoryDerivedCompleteOE` : the full subcategory `D_comp(J, 𝒪_E)` of derived
  complete objects, and `DerivedCategoryDerivedCompleteOE.ι` its inclusion into
  `D(J, 𝒪_E)`.
- `CategoryTheory.ObjectProperty.linear_shiftFunctor_fullSubcategory` : the shift functors of
  a full subcategory stable under shifts are linear if those of the ambient category are.

## Main results

- `DerivedCategory.isTriangulated_derivedCompleteOE` : the derived complete objects form a
  triangulated subcategory of `D(J, 𝒪_E)` (currently `sorry`), so that `D_comp(J, 𝒪_E)` is
  an `𝒪_E`-linear triangulated category with `𝒪_E`-linear shift functors.
- `ValuativeRel.instIsAdicCompleteMaximalIdealULift` : the coefficient ring
  `ULift 𝒪[E]` is `𝔪_E`-adically complete. Through `Ideal.isLimitQuotPowCone` this says
  that `𝒪_E` is the limit of the tower `n ↦ 𝒪_E / 𝔪_Eⁿ`, which is the classical
  completeness of the coefficients underlying the definition of derived completeness.
- `DerivedCategory.derivedCompleteOE_iff_isIso_lift` : when `R lim_n (K ⊗ᴸ 𝒪_E/𝔪_Eⁿ)`
  exists, membership in `D_comp(J, 𝒪_E)` says exactly that the canonical map
  `K ⟶ R lim_n (K ⊗ᴸ 𝒪_E/𝔪_Eⁿ)` is an isomorphism.

-/

@[expose] public section

universe u

open CategoryTheory Limits ValuativeRel

section RingOfIntegers

/-- `E` is a *finite extension of `ℚ_ℓ`*: a nonarchimedean local field `E`, presented as a
`ℚ_ℓ`-algebra which is finite over `ℚ_ℓ` and whose valuation extends the `ℓ`-adic one. Its
ring of integers is then the valuation ring `𝒪[E]`, a complete discrete valuation ring with
finite residue field, and `𝓂[E]` is the maximal ideal of `𝒪[E]`. -/
class IsFiniteExtensionPadic (l : ℕ) [Fact l.Prime] (E : Type*) [Field E] [ValuativeRel E]
    [TopologicalSpace E] [Algebra ℚ_[l] E] : Prop extends
  IsNonarchimedeanLocalField E, ValuativeExtension ℚ_[l] E, Module.Finite ℚ_[l] E

variable (E : Type) [Field E] [ValuativeRel E]

/-- The identification of the ring of integers `𝒪_E` of a nonarchimedean local field with
its copy `ULift 𝒪_E` in the universe `u + 1`, where the coefficient ring of a sheaf on a
`u`-site has to live. -/
noncomputable def ValuativeRel.uliftRingEquiv : 𝒪[E] ≃+* ULift.{u + 1} 𝒪[E] :=
  ULift.ringEquiv.symm

/-- The maximal ideal `𝔪_E` of the ring of integers `𝒪_E` of a nonarchimedean local field,
read inside the universe `u + 1` copy `ULift 𝒪_E` along `ValuativeRel.uliftRingEquiv`. This
is the ideal with respect to which the objects of `D(J, 𝒪_E)` are asked to be derived
complete. -/
noncomputable def ValuativeRel.maximalIdealULift : Ideal (ULift.{u + 1} 𝒪[E]) :=
  𝓂[E].map (ValuativeRel.uliftRingEquiv.{u} E)

/-- The ring of integers of a nonarchimedean local field is `𝔪_E`-adically complete, and
hence so is its universe `u + 1` copy. Through `Ideal.isLimitQuotPowCone` this says that
the coefficient ring is the limit of the tower `n ↦ 𝒪_E / 𝔪_Eⁿ` of its reductions.

Only the topology of `E` is assumed, the one `IsNonarchimedeanLocalField` is stated over.
Mathlib's `IsAdicComplete 𝓂[E] 𝒪[E]` is phrased over a compatible uniformity on `E`, but
that uniformity is the canonical one of the topological additive group `E`, and
`IsAdicComplete` is a proposition, so the choice is immaterial. -/
instance ValuativeRel.instIsAdicCompleteMaximalIdealULift [TopologicalSpace E]
    [IsNonarchimedeanLocalField E] :
    IsAdicComplete (ValuativeRel.maximalIdealULift.{u} E) (ULift.{u + 1} 𝒪[E]) := by
  let := IsTopologicalAddGroup.rightUniformSpace E
  have := isUniformAddGroup_of_addCommGroup (G := E)
  exact (IsAdicComplete.congr_ringEquiv 𝓂[E] (ValuativeRel.uliftRingEquiv.{u} E)).mpr
    inferInstance

end RingOfIntegers

section ShiftLinear

variable {R : Type*} [Ring R] {D : Type*} [Category* D] [Preadditive D] [Linear R D]
  [HasShift D ℤ] [∀ n : ℤ, (shiftFunctor D n).Linear R] (P : ObjectProperty D)
  [P.IsStableUnderShift ℤ]

/-- The shift functors of a full subcategory stable under shifts are `R`-linear if those of
the ambient category are. -/
instance CategoryTheory.ObjectProperty.linear_shiftFunctor_fullSubcategory (n : ℤ) :
    (shiftFunctor P.FullSubcategory n).Linear R where
  map_smul {X Y} f r := P.ι.map_injective <| by
    rw [← cancel_mono ((P.ι.commShiftIso n).hom.app Y), P.ι.commShiftIso_hom_naturality,
      Functor.map_smul, Functor.map_smul, Linear.comp_smul, Functor.map_smul, Linear.smul_comp,
      P.ι.commShiftIso_hom_naturality]

end ShiftLinear

section DerivedComplete

variable {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
  (J : GrothendieckTopology C) (E : Type) [Field E] [ValuativeRel E]

/-- An object `K` of the derived category `D(J, 𝒪_E)` of sheaves of `𝒪_E`-modules on a site
`(C, J)` is *derived complete* if it is derived complete for the maximal ideal `𝔪_E` of
`𝒪_E` in the sense of `DerivedCategory.derivedComplete`: the cone of the reduction maps
`K ⟶ K ⊗ᴸ 𝒪_E/𝔪_Eⁿ`, whose point is `K` itself, is a limit cone. -/
noncomputable abbrev DerivedCategory.derivedCompleteOE :
    ObjectProperty
      (DerivedCategory (Sheaf J (ModuleCat.{u + 1} (ULift.{u + 1} 𝒪[E])))) :=
  DerivedCategory.derivedComplete J (ValuativeRel.maximalIdealULift.{u} E)

/-- The category `D_comp(J, 𝒪_E)` of derived complete objects, realized as the full
subcategory of `D(J, 𝒪_E)` cut out by `DerivedCategory.derivedCompleteOE`. This is the
integral stage of the `ℓ`-adic formalism: the coefficients are the ring of integers `𝒪_E`
of a finite extension `E` of `ℚ_ℓ` (`IsFiniteExtensionPadic`), and completeness is taken
with respect to the maximal ideal of `𝒪_E`. -/
noncomputable def DerivedCategoryDerivedCompleteOE : Type _ :=
  (DerivedCategory.derivedCompleteOE J E).FullSubcategory

noncomputable instance : Category (DerivedCategoryDerivedCompleteOE J E) :=
  inferInstanceAs <| Category (DerivedCategory.derivedCompleteOE J E).FullSubcategory

/-- The inclusion of `D_comp(J, 𝒪_E)` into the derived category of sheaves of
`𝒪_E`-modules. -/
noncomputable def DerivedCategoryDerivedCompleteOE.ι :
    DerivedCategoryDerivedCompleteOE J E ⥤
      DerivedCategory (Sheaf J (ModuleCat.{u + 1} (ULift.{u + 1} 𝒪[E]))) :=
  (DerivedCategory.derivedCompleteOE J E).ι

/-- The derived complete objects of `D(J, 𝒪_E)` form a triangulated subcategory: they
contain `0` and are stable under shifts and extensions.

The proof is currently `sorry`. -/
instance DerivedCategory.isTriangulated_derivedCompleteOE :
    (DerivedCategory.derivedCompleteOE J E).IsTriangulated :=
  sorry

noncomputable instance : Preadditive (DerivedCategoryDerivedCompleteOE J E) :=
  inferInstanceAs <| Preadditive (DerivedCategory.derivedCompleteOE J E).FullSubcategory

/-- The `Hom` groups of `D_comp(J, 𝒪_E)` are `𝒪_E`-modules, as those of `D(J, 𝒪_E)` are. -/
noncomputable instance : Linear (ULift.{u + 1} 𝒪[E]) (DerivedCategoryDerivedCompleteOE J E) :=
  inferInstanceAs <|
    Linear (ULift.{u + 1} 𝒪[E]) (DerivedCategory.derivedCompleteOE J E).FullSubcategory

noncomputable instance : HasZeroObject (DerivedCategoryDerivedCompleteOE J E) :=
  inferInstanceAs <| HasZeroObject (DerivedCategory.derivedCompleteOE J E).FullSubcategory

noncomputable instance : HasShift (DerivedCategoryDerivedCompleteOE J E) ℤ :=
  inferInstanceAs <| HasShift (DerivedCategory.derivedCompleteOE J E).FullSubcategory ℤ

instance (n : ℤ) : (shiftFunctor (DerivedCategoryDerivedCompleteOE J E) n).Additive :=
  inferInstanceAs <|
    (shiftFunctor (DerivedCategory.derivedCompleteOE J E).FullSubcategory n).Additive

/-- The shift functors of `D_comp(J, 𝒪_E)` are `𝒪_E`-linear, as those of `D(J, 𝒪_E)` are. -/
instance (n : ℤ) :
    (shiftFunctor (DerivedCategoryDerivedCompleteOE J E) n).Linear (ULift.{u + 1} 𝒪[E]) :=
  inferInstanceAs <|
    (shiftFunctor (DerivedCategory.derivedCompleteOE J E).FullSubcategory n).Linear
      (ULift.{u + 1} 𝒪[E])

noncomputable instance : Pretriangulated (DerivedCategoryDerivedCompleteOE J E) :=
  inferInstanceAs <| Pretriangulated (DerivedCategory.derivedCompleteOE J E).FullSubcategory

instance : IsTriangulated (DerivedCategoryDerivedCompleteOE J E) :=
  inferInstanceAs <| IsTriangulated (DerivedCategory.derivedCompleteOE J E).FullSubcategory

variable {J E}

/-- If the limit `R lim_n (K ⊗ᴸ 𝒪_E/𝔪_Eⁿ)` exists, then `K` lies in `D_comp(J, 𝒪_E)`
precisely when the canonical map `K ⟶ R lim_n (K ⊗ᴸ 𝒪_E/𝔪_Eⁿ)` is an isomorphism. -/
lemma DerivedCategory.derivedCompleteOE_iff_isIso_lift
    (K : DerivedCategory (Sheaf J (ModuleCat.{u + 1} (ULift.{u + 1} 𝒪[E]))))
    [HasLimit (derivedCompletionDiagram J (ValuativeRel.maximalIdealULift.{u} E) K)] :
    derivedCompleteOE J E K ↔
      IsIso (limit.lift (derivedCompletionDiagram J (ValuativeRel.maximalIdealULift.{u} E) K)
        (derivedCompletionCone J (ValuativeRel.maximalIdealULift.{u} E) K)) :=
  derivedComplete_iff_isIso_lift K

end DerivedComplete
