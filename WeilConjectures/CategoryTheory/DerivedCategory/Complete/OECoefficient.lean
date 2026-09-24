/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.Complete.Defs
public import Mathlib.Algebra.Homology.DerivedCategory.Linear
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.CategoryTheory.Shift.Linear
public import Mathlib.CategoryTheory.Triangulated.Subcategory
public import Mathlib.NumberTheory.LocalField.Basic
public import Mathlib.NumberTheory.Padics.Complex
public import Mathlib.NumberTheory.Padics.ProperSpace
public import Mathlib.NumberTheory.Padics.ValuativeRel
public import Mathlib.RingTheory.AdicCompletion.Topology
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Mathlib.Topology.Algebra.Valued.NormedValued

/-!

# Derived complete objects with coefficients in the ring of integers of an `ℓ`-adic field

This file specializes `DerivedCategory.derivedComplete` of
`WeilConjectures.CategoryTheory.DerivedCategory.Complete.Defs` to the coefficient ring of
the integral stage of the `ℓ`-adic formalism: `E` is an extension of `ℚ_ℓ` inside `ℚ̄_ℓ`,
`𝒪_E` is its ring of integers and `𝔪_E` is the maximal ideal of `𝒪_E`. For a site `(C, J)`
it defines the full subcategory

```
  D_comp(J, 𝒪_E)  ⊆  D(J, 𝒪_E) := DerivedCategory (Sheaf J (ModuleCat 𝒪_E))
```

of those objects that are derived complete for `𝔪_E`, together with its inclusion functor.

## The hypotheses on `E`

The field `E` is given together with `[Algebra ℚ_[l] E] [Algebra E (PadicAlgCl l)]
[IsScalarTower ℚ_[l] E (PadicAlgCl l)]`: an extension of `ℚ_ℓ` with a `ℚ_ℓ`-embedding into
the fixed algebraic closure `ℚ̄_ℓ = PadicAlgCl l`. Its valuation and topology are not
separate data but are restricted from `ℚ̄_ℓ` along the embedding: `PadicAlgCl.valuationOfAlgebra`,
`PadicAlgCl.normedFieldOfAlgebra` and `PadicAlgCl.valuedOfAlgebra`. The ring of integers
`PadicAlgCl.integers l E` is the valuation subring of the restricted valuation. These
structures are definitions rather than instances, since `ℓ` cannot be recovered from `E`.
The structure is phrased with `Valued`, pending the move of this part of mathlib to
`ValuativeRel`.

The ring of integers and the categories below only use the embedding `E → ℚ̄_ℓ`. The
`ℚ_ℓ`-algebra structure, the scalar tower and finiteness `[FiniteDimensional ℚ_[l] E]` are
used for the completeness of `𝒪_E` (`PadicAlgCl.isAdicComplete_integers`): through them the
restricted valuation extends the `ℓ`-adic one, and `E` becomes a nonarchimedean local field.

## Universes

`WeilConjectures.CategoryTheory.DerivedCategory.Complete.Defs` takes its site `(C, J)` with
objects in `Type (u + 1)` and morphisms in `Type u` — the shape of the small étale site of
a `Scheme.{u}` — and its coefficient ring in `Type (u + 1)`. The field `E` lives in an
arbitrary universe `Type w` and is assumed `Small.{u + 1}`, so the coefficient ring used
below is the copy `Shrink.{u + 1} (PadicAlgCl.integers l E)` of `𝒪_E` in `Type (u + 1)`.
`Shrink` carries the ring structure across (`Shrink.ringEquiv`), so no instance has to be
replayed by hand; the one fact that does need transporting, `IsAdicComplete`, is
transported along `PadicAlgCl.shrinkRingEquiv` by `IsAdicComplete.congr_ringEquiv`.

## Main definitions

- `PadicAlgCl.normedFieldOfAlgebra`, `PadicAlgCl.valuationOfAlgebra` and
  `PadicAlgCl.valuedOfAlgebra` : the norm, valuation and valued field structure of `E`,
  restricted from `ℚ̄_ℓ`.
- `PadicAlgCl.integers` : the ring of integers `𝒪_E`.
- `PadicAlgCl.shrinkRingEquiv` and `PadicAlgCl.maximalIdealShrink` : the identification of
  `𝒪_E` with its copy in `Type (u + 1)`, and the maximal ideal `𝔪_E` read in that copy.
- `DerivedCategory.derivedCompleteOE` : the property of an object of `D(J, 𝒪_E)` of being
  derived complete with respect to `𝔪_E`.
- `DerivedCategoryDerivedCompleteOE` : the full subcategory `D_comp(J, 𝒪_E)` of derived
  complete objects, and `DerivedCategoryDerivedCompleteOE.ι` its inclusion into
  `D(J, 𝒪_E)`.
- `CategoryTheory.ObjectProperty.linear_shiftFunctor_fullSubcategory` : the shift functors of
  a full subcategory stable under shifts are linear if those of the ambient category are.

## Main results

- `PadicAlgCl.isAdicComplete_integers` and `PadicAlgCl.isAdicComplete_maximalIdealShrink` :
  if `E` is finite over `ℚ_ℓ`, then `𝒪_E` and its copy `Shrink 𝒪_E` are `𝔪_E`-adically
  complete. Through `Ideal.isLimitQuotPowCone` this says that `𝒪_E` is the limit of the
  tower `n ↦ 𝒪_E / 𝔪_Eⁿ`, which is the classical completeness of the coefficients
  underlying the definition of derived completeness.
- `DerivedCategory.isTriangulated_derivedCompleteOE` : the derived complete objects form a
  triangulated subcategory of `D(J, 𝒪_E)` (currently `sorry`), so that `D_comp(J, 𝒪_E)` is
  an `𝒪_E`-linear triangulated category with `𝒪_E`-linear shift functors.
- `DerivedCategory.derivedCompleteOE_iff_isIso_lift` : when `R lim_n (K ⊗ᴸ 𝒪_E/𝔪_Eⁿ)`
  exists, membership in `D_comp(J, 𝒪_E)` says exactly that the canonical map
  `K ⟶ R lim_n (K ⊗ᴸ 𝒪_E/𝔪_Eⁿ)` is an isomorphism.

-/


@[expose] public section

universe w u

open CategoryTheory Limits NNReal

section RingOfIntegers

namespace PadicAlgCl

variable (l : ℕ) [Fact l.Prime] (E : Type w) [Field E] [Algebra E (PadicAlgCl l)]

/-- The normed field structure on a subfield `E` of `ℚ̄_ℓ = PadicAlgCl l`, restricted from
the `ℓ`-adic norm of `PadicAlgCl l` along the embedding `E → PadicAlgCl l`. Its topology is
the subspace topology of `E` in `PadicAlgCl l`. -/
@[reducible]
noncomputable def normedFieldOfAlgebra : NormedField E :=
  NormedField.induced E (PadicAlgCl l) (algebraMap E (PadicAlgCl l))
    (algebraMap E (PadicAlgCl l)).injective

/-- The `ℓ`-adic valuation on a subfield `E` of `ℚ̄_ℓ = PadicAlgCl l`, restricted from the
valuation of `PadicAlgCl l` along the embedding `E → PadicAlgCl l`. -/
noncomputable def valuationOfAlgebra : Valuation E ℝ≥0 :=
  (Valued.v : Valuation (PadicAlgCl l) ℝ≥0).comap (algebraMap E (PadicAlgCl l))

variable {l E} in
lemma valuationOfAlgebra_apply (x : E) :
    valuationOfAlgebra l E x = ‖algebraMap E (PadicAlgCl l) x‖₊ := rfl

lemma isUltrametricDist_ofAlgebra :
    letI := normedFieldOfAlgebra l E
    IsUltrametricDist E := by
  let := normedFieldOfAlgebra l E
  exact IsUltrametricDist.isUltrametricDist_of_isNonarchimedean_norm fun x y ↦ by
    have := PadicAlgCl.isNonarchimedean l (algebraMap E (PadicAlgCl l) x)
      (algebraMap E (PadicAlgCl l) y)
    rwa [← map_add] at this

/-- The valued field structure on a subfield `E` of `ℚ̄_ℓ = PadicAlgCl l`, restricted from
`PadicAlgCl l`: its valuation is `PadicAlgCl.valuationOfAlgebra` and its uniformity that of
`PadicAlgCl.normedFieldOfAlgebra`.

It is not an instance, since `ℓ` cannot be recovered from `E`. -/
@[reducible]
noncomputable def valuedOfAlgebra : Valued E ℝ≥0 :=
  letI := normedFieldOfAlgebra l E
  haveI := isUltrametricDist_ofAlgebra l E
  NormedField.toValued

lemma valuedOfAlgebra_v : (valuedOfAlgebra l E).v = valuationOfAlgebra l E := rfl

/-- The ring of integers `𝒪_E` of a subfield `E` of `ℚ̄_ℓ = PadicAlgCl l`: the valuation
subring of the valuation `PadicAlgCl.valuationOfAlgebra` restricted from `PadicAlgCl l`. -/
noncomputable def integers : ValuationSubring E :=
  (valuationOfAlgebra l E).valuationSubring

lemma mem_integers_iff (x : E) :
    x ∈ integers l E ↔ ‖algebraMap E (PadicAlgCl l) x‖₊ ≤ 1 := Iff.rfl

/-- The identification of the ring of integers `𝒪_E` with its copy `Shrink 𝒪_E` in the
universe `u + 1`, where the coefficient ring of a sheaf on a `u`-site has to live. -/
noncomputable def shrinkRingEquiv [Small.{u + 1} E] :
    integers l E ≃+* Shrink.{u + 1} (integers l E) :=
  (Shrink.ringEquiv (integers l E)).symm

/-- The maximal ideal `𝔪_E` of the ring of integers `𝒪_E`, read inside the universe `u + 1`
copy `Shrink 𝒪_E` along `PadicAlgCl.shrinkRingEquiv`. This is the ideal with respect to which
the objects of `D(J, 𝒪_E)` are asked to be derived complete. -/
noncomputable def maximalIdealShrink [Small.{u + 1} E] : Ideal (Shrink.{u + 1} (integers l E)) :=
  (IsLocalRing.maximalIdeal (integers l E)).map (shrinkRingEquiv l E)

section Complete

variable [Algebra ℚ_[l] E] [IsScalarTower ℚ_[l] E (PadicAlgCl l)]

lemma valuationOfAlgebra_algebraMap (x : ℚ_[l]) :
    valuationOfAlgebra l E (algebraMap ℚ_[l] E x) = ‖x‖₊ := by
  rw [valuationOfAlgebra_apply, ← IsScalarTower.algebraMap_apply]
  exact NNReal.eq (PadicAlgCl.norm_extends l x)

open ValuativeRel in
/-- If `E` is a finite extension of `ℚ_ℓ` inside `ℚ̄_ℓ`, its ring of integers is
`𝔪_E`-adically complete.

The proof equips `E` with the valuative relation and the topology restricted from
`PadicAlgCl l`, checks that this makes `E` a nonarchimedean local field (it is locally
compact, being a finite-dimensional normed space over `ℚ_ℓ`), and transports mathlib's
`IsAdicComplete 𝓂[E] 𝒪[E]` to `PadicAlgCl.integers l E`. -/
instance isAdicComplete_integers [FiniteDimensional ℚ_[l] E] :
    IsAdicComplete (IsLocalRing.maximalIdeal (integers l E)) (integers l E) := by
  let w := valuationOfAlgebra l E
  let := normedFieldOfAlgebra l E
  have := isUltrametricDist_ofAlgebra l E
  let : ValuativeRel E := .ofValuation w
  have : w.Compatible := .ofValuation w
  let : NormedSpace ℚ_[l] E :=
    { norm_smul_le c x := by
        change ‖algebraMap E (PadicAlgCl l) (c • x)‖ ≤ ‖c‖ * ‖algebraMap E (PadicAlgCl l) x‖
        rw [Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply, norm_mul,
          PadicAlgCl.norm_extends] }
  have : ProperSpace E := FiniteDimensional.proper ℚ_[l] E
  have : w.IsNontrivial := ⟨algebraMap ℚ_[l] E l, by
    rw [valuationOfAlgebra_algebraMap]
    refine ⟨by simp [(Fact.out : l.Prime).ne_zero], fun h ↦ ?_⟩
    have := congrArg (fun r : ℝ≥0 ↦ (r : ℝ)) h
    simp [Padic.norm_p, (Fact.out : l.Prime).one_lt.ne'] at this⟩
  have : IsNontrivial E := (isNontrivial_iff_isNontrivial w).mpr inferInstance
  have : IsValuativeTopology E := by
    refine IsValuativeTopology.of_mem_nhds_zero_iff_vle w fun {s} ↦ ?_
    have hnorm (z : E) : ‖z‖ = (w z : ℝ) := rfl
    rw [Metric.mem_nhds_iff]
    constructor
    · rintro ⟨ε, hε, hs⟩
      have hl : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
      obtain ⟨n, hn⟩ : ∃ n : ℕ, ((l : ℝ)⁻¹) ^ n < ε :=
        exists_pow_lt_of_lt_one hε (inv_lt_one_of_one_lt₀ hl)
      let x : E := algebraMap ℚ_[l] E ((l : ℚ_[l]) ^ n)
      have hx : (w x : ℝ) = ((l : ℝ)⁻¹) ^ n := by
        simp only [w, x]
        rw [valuationOfAlgebra_algebraMap]
        simp [Padic.norm_p]
      have hx0 : w.restrict x ≠ 0 :=
        ((Valuation.restrict_pos_iff w x).mpr (NNReal.coe_pos.mp (hx ▸ by positivity))).ne'
      refine ⟨Units.mk0 _ hx0, fun z hz ↦ hs ?_⟩
      simp only [Set.mem_ofPred_eq, Units.val_mk0, Valuation.restrict_lt_iff] at hz
      rw [mem_ball_zero_iff, hnorm]
      exact (NNReal.coe_lt_coe.mpr hz).trans_eq hx |>.trans hn
    · rintro ⟨γ, hγ⟩
      refine ⟨MonoidWithZeroHom.ValueGroup₀.embedding (f := MonoidWithZeroHom.ofClass w) γ.val,
        ?_, fun z hz ↦ hγ ?_⟩
      · exact NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr ((map_ne_zero _).mpr γ.ne_zero))
      rw [Set.mem_ofPred_eq, Valuation.restrict_lt_iff_lt_embedding, ← NNReal.coe_lt_coe,
        ← hnorm]
      simpa using hz
  have : IsNonarchimedeanLocalField E := {}
  have heq : 𝒪[E] = (integers l E).toSubring := by
    ext x
    exact (isEquiv (valuation E) w).le_one_iff_le_one
  let e : 𝒪[E] ≃+* integers l E := RingEquiv.subringCongr heq
  rw [← IsLocalRing.map_ringEquiv_maximalIdeal e]
  exact (IsAdicComplete.congr_ringEquiv _ e).mpr inferInstance

/-- If `E` is a finite extension of `ℚ_ℓ` inside `ℚ̄_ℓ`, the universe `u + 1` copy of its ring
of integers is `𝔪_E`-adically complete. Through `Ideal.isLimitQuotPowCone` this says that
the coefficient ring is the limit of the tower `n ↦ 𝒪_E / 𝔪_Eⁿ` of its reductions. -/
instance isAdicComplete_maximalIdealShrink [FiniteDimensional ℚ_[l] E] [Small.{u + 1} E] :
    IsAdicComplete (maximalIdealShrink l E) (Shrink.{u + 1} (integers l E)) :=
  (IsAdicComplete.congr_ringEquiv _ (shrinkRingEquiv l E)).mpr inferInstance

end Complete

end PadicAlgCl

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
  (J : GrothendieckTopology C) (l : ℕ) [Fact l.Prime] (E : Type w) [Field E]
  [Algebra E (PadicAlgCl l)] [Small.{u + 1} E]

/-- An object `K` of the derived category `D(J, 𝒪_E)` of sheaves of `𝒪_E`-modules on a site
`(C, J)` is *derived complete* if it is derived complete for the maximal ideal `𝔪_E` of
`𝒪_E` in the sense of `DerivedCategory.derivedComplete`: the cone of the reduction maps
`K ⟶ K ⊗ᴸ 𝒪_E/𝔪_Eⁿ`, whose point is `K` itself, is a limit cone. -/
noncomputable abbrev DerivedCategory.derivedCompleteOE :
    ObjectProperty
      (DerivedCategory (Sheaf J (ModuleCat.{u + 1} (Shrink.{u + 1} (PadicAlgCl.integers l E))))) :=
  DerivedCategory.derivedComplete J (PadicAlgCl.maximalIdealShrink l E)

/-- The category `D_comp(J, 𝒪_E)` of derived complete objects, realized as the full
subcategory of `D(J, 𝒪_E)` cut out by `DerivedCategory.derivedCompleteOE`. This is the
integral stage of the `ℓ`-adic formalism: the coefficients are the ring of integers `𝒪_E`
of an extension `E` of `ℚ_ℓ` inside `ℚ̄_ℓ = PadicAlgCl l`, and completeness is taken with
respect to the maximal ideal of `𝒪_E`. -/
noncomputable def DerivedCategoryDerivedCompleteOE : Type _ :=
  (DerivedCategory.derivedCompleteOE J l E).FullSubcategory

noncomputable instance : Category (DerivedCategoryDerivedCompleteOE J l E) :=
  inferInstanceAs <| Category (DerivedCategory.derivedCompleteOE J l E).FullSubcategory

/-- The inclusion of `D_comp(J, 𝒪_E)` into the derived category of sheaves of
`𝒪_E`-modules. -/
noncomputable def DerivedCategoryDerivedCompleteOE.ι :
    DerivedCategoryDerivedCompleteOE J l E ⥤
      DerivedCategory (Sheaf J (ModuleCat.{u + 1} (Shrink.{u + 1} (PadicAlgCl.integers l E)))) :=
  (DerivedCategory.derivedCompleteOE J l E).ι

/-- The derived complete objects of `D(J, 𝒪_E)` form a triangulated subcategory: they
contain `0` and are stable under shifts and extensions.

The proof is currently `sorry`. -/
instance DerivedCategory.isTriangulated_derivedCompleteOE :
    (DerivedCategory.derivedCompleteOE J l E).IsTriangulated :=
  sorry

noncomputable instance : Preadditive (DerivedCategoryDerivedCompleteOE J l E) :=
  inferInstanceAs <| Preadditive (DerivedCategory.derivedCompleteOE J l E).FullSubcategory

/-- The `Hom` groups of `D_comp(J, 𝒪_E)` are `𝒪_E`-modules, as those of `D(J, 𝒪_E)` are. -/
noncomputable instance :
    Linear (Shrink.{u + 1} (PadicAlgCl.integers l E)) (DerivedCategoryDerivedCompleteOE J l E) :=
  inferInstanceAs <| Linear (Shrink.{u + 1} (PadicAlgCl.integers l E))
    (DerivedCategory.derivedCompleteOE J l E).FullSubcategory

noncomputable instance : HasZeroObject (DerivedCategoryDerivedCompleteOE J l E) :=
  inferInstanceAs <| HasZeroObject (DerivedCategory.derivedCompleteOE J l E).FullSubcategory

noncomputable instance : HasShift (DerivedCategoryDerivedCompleteOE J l E) ℤ :=
  inferInstanceAs <| HasShift (DerivedCategory.derivedCompleteOE J l E).FullSubcategory ℤ

instance (n : ℤ) : (shiftFunctor (DerivedCategoryDerivedCompleteOE J l E) n).Additive :=
  inferInstanceAs <|
    (shiftFunctor (DerivedCategory.derivedCompleteOE J l E).FullSubcategory n).Additive

/-- The shift functors of `D_comp(J, 𝒪_E)` are `𝒪_E`-linear, as those of `D(J, 𝒪_E)` are. -/
instance (n : ℤ) :
    (shiftFunctor (DerivedCategoryDerivedCompleteOE J l E) n).Linear
      (Shrink.{u + 1} (PadicAlgCl.integers l E)) :=
  inferInstanceAs <|
    (shiftFunctor (DerivedCategory.derivedCompleteOE J l E).FullSubcategory n).Linear
      (Shrink.{u + 1} (PadicAlgCl.integers l E))

noncomputable instance : Pretriangulated (DerivedCategoryDerivedCompleteOE J l E) :=
  inferInstanceAs <| Pretriangulated (DerivedCategory.derivedCompleteOE J l E).FullSubcategory

instance : IsTriangulated (DerivedCategoryDerivedCompleteOE J l E) :=
  inferInstanceAs <| IsTriangulated (DerivedCategory.derivedCompleteOE J l E).FullSubcategory

variable {J l E}

/-- If the limit `R lim_n (K ⊗ᴸ 𝒪_E/𝔪_Eⁿ)` exists, then `K` lies in `D_comp(J, 𝒪_E)`
precisely when the canonical map `K ⟶ R lim_n (K ⊗ᴸ 𝒪_E/𝔪_Eⁿ)` is an isomorphism. -/
lemma DerivedCategory.derivedCompleteOE_iff_isIso_lift
    (K : DerivedCategory (Sheaf J (ModuleCat.{u + 1} (Shrink.{u + 1} (PadicAlgCl.integers l E)))))
    [HasLimit (derivedCompletionDiagram J (PadicAlgCl.maximalIdealShrink l E) K)] :
    derivedCompleteOE J l E K ↔
      IsIso (limit.lift (derivedCompletionDiagram J (PadicAlgCl.maximalIdealShrink l E) K)
        (derivedCompletionCone J (PadicAlgCl.maximalIdealShrink l E) K)) :=
  derivedComplete_iff_isIso_lift K

end DerivedComplete
