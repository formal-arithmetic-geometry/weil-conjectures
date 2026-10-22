/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C3
-/
module

public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.HomologyProperty
public import Mathlib.CategoryTheory.ObjectProperty.Retract
public import Mathlib.RingTheory.Nilpotent.Defs

/-!
# Nilpotent monodromy in cohomology

Source: the monodromy obstruction in the proof of blueprint
`lem-trf-devissage-generation`, Step 3. Nilpotence of monodromy minus identity is
preserved under subobjects, quotients and extensions.
-/

@[expose] public section

set_option autoImplicit false

universe u v u' v' w

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [Abelian C]
  {D : Type u'} [Category.{v'} D] [Abelian D]

/-- Objects on whose exact fibre a natural endomorphism is nilpotent.
Source: blueprint `lem-trf-devissage-generation`, Step 3
(blueprint: lem-trf-nilpotent-fiber-homology). -/
def nilpotentFiber (F : C ⥤ D) (t : F ⟶ F) : ObjectProperty C :=
  fun X ↦ IsNilpotent (End.of (t.app X))

/-- Complexes with nilpotent monodromy in every cohomology degree.
Source: blueprint `lem-trf-devissage-generation`, Step 3
(blueprint: lem-trf-nilpotent-fiber-homology). -/
def nilpotentFiberHomology [HasDerivedCategory.{w} C] (F : C ⥤ D) (t : F ⟶ F) :
    ObjectProperty (DerivedCategory C) :=
  DerivedCategory.homologyProperty (nilpotentFiber F t)

omit [Abelian C] [Abelian D] in
private lemma naturality_pow (F : C ⥤ D) (t : F ⟶ F)
    {X Y : C} (f : X ⟶ Y) (n : ℕ) :
    ((End.of (t.app X)) ^ n) ≫ F.map f = F.map f ≫ ((End.of (t.app Y)) ^ n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [pow_succ, End.mul_def]
    rw [Category.assoc, ih, ← Category.assoc, ← t.naturality, Category.assoc]

omit [Abelian C] in
private lemma nilpotentFiber_mono (F : C ⥤ D) [PreservesFiniteLimits F]
    (t : F ⟶ F) {X Y : C} (f : X ⟶ Y) [Mono f]
    (hY : nilpotentFiber F t Y) : nilpotentFiber F t X := by
  obtain ⟨n, hn⟩ := hY
  refine ⟨n, (cancel_mono (F.map f)).mp ?_⟩
  rw [naturality_pow, hn, comp_zero, zero_comp]

omit [Abelian C] in
private lemma nilpotentFiber_epi (F : C ⥤ D) [PreservesFiniteColimits F]
    (t : F ⟶ F) {X Y : C} (f : X ⟶ Y) [Epi f]
    (hX : nilpotentFiber F t X) : nilpotentFiber F t Y := by
  obtain ⟨n, hn⟩ := hX
  refine ⟨n, (cancel_epi (F.map f)).mp ?_⟩
  rw [← naturality_pow, hn, zero_comp, comp_zero]

private lemma nilpotentFiber_extension (F : C ⥤ D) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] (t : F ⟶ F)
    {S : ShortComplex C} (hS : S.ShortExact)
    (h₁ : nilpotentFiber F t S.X₁) (h₃ : nilpotentFiber F t S.X₃) :
    nilpotentFiber F t S.X₂ := by
  obtain ⟨a, ha⟩ := h₁
  obtain ⟨b, hb⟩ := h₃
  have := hS.mono_f
  have := hS.epi_g
  let R := S.map F
  have hR : R.ShortExact := hS.map F
  have := hR.mono_f
  have hk : ((End.of (t.app S.X₂)) ^ b) ≫ R.g = 0 := by
    change ((End.of (t.app S.X₂)) ^ b) ≫ F.map S.g = 0
    rw [naturality_pow, hb, comp_zero]
  let k := hR.exact.lift ((End.of (t.app S.X₂)) ^ b) hk
  refine ⟨a + b, ?_⟩
  rw [pow_add, End.mul_def, ← hR.exact.lift_f _ hk, Category.assoc]
  change k ≫ F.map S.f ≫ (End.of (t.app S.X₂)) ^ a = 0
  rw [← naturality_pow, ha, zero_comp, comp_zero]

/-- Nilpotent monodromy in cohomology defines a thick subcategory.
Source: blueprint `lem-trf-devissage-generation`, proof Step 3; the five-term
cohomology argument is Stacks, Tag 06UQ
(blueprint: lem-trf-nilpotent-fiber-homology).

Proof: naturality intertwines every power of the endomorphism with every fibre map.
Monomorphisms and epimorphisms therefore inherit a nilpotence exponent. In an extension,
if the left and right terms have exponents a and b, the b-th power on the middle term
factors through the left term by exactness. Its composite with the a-th power is zero,
so a+b is an exponent. The zero object is killed by the first power. Thus the sheaf-level
property is a Serre class. The long exact cohomology sequence gives triangle closure,
and shifts reindex cohomology. A retract gives a monomorphism on each cohomology object,
so the same exponents pass to it. No common exponent over all degrees is required. -/
theorem nilpotentFiberHomology_thick [HasDerivedCategory.{w} C]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (t : F ⟶ F) :
    (nilpotentFiberHomology F t).IsTriangulated ∧
      (nilpotentFiberHomology F t).IsStableUnderRetracts := by
  let P := nilpotentFiber F t
  let : P.IsClosedUnderSubobjects := ⟨nilpotentFiber_mono F t⟩
  let : P.IsClosedUnderQuotients := ⟨nilpotentFiber_epi F t⟩
  let : P.IsClosedUnderExtensions := ⟨nilpotentFiber_extension F t⟩
  let : Zero C := HasZeroObject.zero' _
  let : P.ContainsZero := ⟨0, isZero_zero _, 1, by
    simpa only [pow_one] using
      (F.map_isZero (isZero_zero C)).eq_of_src (t.app 0) 0⟩
  refine ⟨inferInstanceAs (DerivedCategory.homologyProperty P).IsTriangulated, ⟨?_⟩⟩
  intro X Y r hY n
  exact P.prop_of_mono ((DerivedCategory.homologyFunctor C n).map r.i) (hY n)

end CategoryTheory
