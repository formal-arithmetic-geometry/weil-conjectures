/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M8
-/
module

public import Sheaf.Algebra.Homology.FiniteFilteredModuleHomotopy
import WeilConjectures.FromJoel.Algebra.Homology.BicomplexColumns

/-! # Graded comparison for finite filtered complexes

Source: Stacks Project, Derived Categories, Tag 05S3.
(blueprint: lem-kun-finite-filtered-graded-comparison).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace CochainComplex

private theorem restriction_arrow {C : Type*} [Category C] [Abelian C]
    {K L : FilteredObject C} (f : K ⟶ L) (i : ℤ) :
    FilteredObject.restrictionSteps f i ≫ (L.filtration.step i).arrow =
      (K.filtration.step i).arrow ≫ f.hom :=
  Classical.choose_spec (f.preserves i)

private theorem graded_projection {C : Type*} [Category C] [Abelian C]
    {K L : FilteredObject C} (f : K ⟶ L) (i : ℤ) :
    cokernel.π (Subobject.ofLE (K.filtration.step (i + 1)) (K.filtration.step i)
      (K.filtration.antitone_step (by omega))) ≫ FilteredObject.gradedMapSteps f i =
    FilteredObject.restrictionSteps f i ≫
      cokernel.π (Subobject.ofLE (L.filtration.step (i + 1)) (L.filtration.step i)
        (L.filtration.antitone_step (by omega))) :=
  Classical.choose_spec (FilteredObject.exists_gradedMap_steps K L f i)

private theorem restriction_naturality {C : Type*} [Category C] [Abelian C]
    {K L : FilteredObject C} (f : K ⟶ L) (p : ℤ) :
    Subobject.ofLE (K.filtration.step (p + 1)) (K.filtration.step p)
        (K.filtration.antitone_step (by omega)) ≫ FilteredObject.restrictionSteps f p =
      FilteredObject.restrictionSteps f (p + 1) ≫ Subobject.ofLE
        (L.filtration.step (p + 1)) (L.filtration.step p)
        (L.filtration.antitone_step (by omega)) := by
  apply (cancel_mono (L.filtration.step p).arrow).1
  simp only [Category.assoc, restriction_arrow, Subobject.ofLE_arrow]
  rw [← Category.assoc, Subobject.ofLE_arrow]

private theorem restriction_quasiIso_succ {R : Type u} [CommRing R]
    {K L : FiniteFilteredModuleComplex R} (f : K ⟶ L) (p : ℤ)
    (hs : QuasiIso (FilteredObject.restrictionSteps f.hom (p + 1)))
    (hg : QuasiIso (FilteredObject.gradedMapSteps f.hom p)) :
    QuasiIso (FilteredObject.restrictionSteps f.hom p) := by
  let iK := Subobject.ofLE (K.obj.filtration.step (p + 1)) (K.obj.filtration.step p)
    (K.obj.filtration.antitone_step (by omega))
  let iL := Subobject.ofLE (L.obj.filtration.step (p + 1)) (L.obj.filtration.step p)
    (L.obj.filtration.antitone_step (by omega))
  let SK := ShortComplex.cokernelSequence iK
  let SL := ShortComplex.cokernelSequence iL
  have hK : SK.ShortExact :=
    { exact := ShortComplex.cokernelSequence_exact iK
      mono_f := by dsimp [SK, ShortComplex.cokernelSequence, iK]; infer_instance }
  have hL : SL.ShortExact :=
    { exact := ShortComplex.cokernelSequence_exact iL
      mono_f := by dsimp [SL, ShortComplex.cokernelSequence, iL]; infer_instance }
  let α : SK ⟶ SL :=
    { τ₁ := FilteredObject.restrictionSteps f.hom (p + 1)
      τ₂ := FilteredObject.restrictionSteps f.hom p
      τ₃ := FilteredObject.gradedMapSteps f.hom p
      comm₁₂ := (restriction_naturality f.hom p).symm
      comm₂₃ := (graded_projection f.hom p).symm }
  exact HomologicalComplex.HomologySequence.quasiIso_τ₂ α hK hL hs hg

private theorem restriction_quasiIso {R : Type u} [CommRing R]
    {K L : FiniteFilteredModuleComplex R} (f : K ⟶ L)
    (hg : ∀ p : ℤ, QuasiIso (FilteredObject.gradedMapSteps f.hom p)) :
    ∀ p : ℤ, QuasiIso (FilteredObject.restrictionSteps f.hom p) := by
  obtain ⟨_, mK, _, hmK⟩ := K.property
  obtain ⟨_, mL, _, hmL⟩ := L.property
  let m := max mK mL
  have hzero (p : ℤ) (hp : m ≤ p) :
      QuasiIso (FilteredObject.restrictionSteps f.hom p) := by
    have hKp : K.obj.filtration.step p = ⊥ := by
      apply bot_unique
      rw [← hmK]
      exact K.obj.filtration.antitone_step (by dsimp [m] at hp; omega)
    have hLp : L.obj.filtration.step p = ⊥ := by
      apply bot_unique
      rw [← hmL]
      exact L.obj.filtration.antitone_step (by dsimp [m] at hp; omega)
    have hKz : IsZero (K.obj.filtration.step p : CochainComplex (ModuleCat R) ℤ) := by
      rw [hKp]
      exact (isZero_zero _).of_iso Subobject.botCoeIsoZero
    have hLz : IsZero (L.obj.filtration.step p : CochainComplex (ModuleCat R) ℤ) := by
      rw [hLp]
      exact (isZero_zero _).of_iso Subobject.botCoeIsoZero
    have : IsIso (FilteredObject.restrictionSteps f.hom p) :=
      isIso_of_source_target_iso_zero _ hKz.isoZero hLz.isoZero
    infer_instance
  have hi : ∀ k : ℕ, ∀ p : ℤ, m ≤ p + k →
      QuasiIso (FilteredObject.restrictionSteps f.hom p) := by
    intro k
    induction k with
    | zero => intro p hp; exact hzero p (by simpa using hp)
    | succ k ih =>
      intro p hp
      exact restriction_quasiIso_succ f p (ih (p + 1) (by omega)) (hg p)
  exact fun p ↦ hi (m - p).toNat p (by omega)

private theorem underlying_quasiIso {R : Type u} [CommRing R]
    {K L : FiniteFilteredModuleComplex R} (f : K ⟶ L)
    (hg : ∀ p : ℤ, QuasiIso (FilteredObject.gradedMapSteps f.hom p)) :
    QuasiIso f.hom.hom := by
  obtain ⟨nK, _, hnK, _⟩ := K.property
  obtain ⟨nL, _, hnL, _⟩ := L.property
  let n := min nK nL
  have hKn : K.obj.filtration.step n = ⊤ := by
    apply top_unique
    rw [← hnK]
    exact K.obj.filtration.antitone_step (min_le_left _ _)
  have hLn : L.obj.filtration.step n = ⊤ := by
    apply top_unique
    rw [← hnL]
    exact L.obj.filtration.antitone_step (min_le_right _ _)
  have : IsIso (K.obj.filtration.step n).arrow :=
    (Subobject.isIso_arrow_iff_eq_top _).2 hKn
  have : IsIso (L.obj.filtration.step n).arrow :=
    (Subobject.isIso_arrow_iff_eq_top _).2 hLn
  have := restriction_quasiIso f hg n
  have heq : f.hom.hom = inv (K.obj.filtration.step n).arrow ≫
      FilteredObject.restrictionSteps f.hom n ≫ (L.obj.filtration.step n).arrow := by
    rw [restriction_arrow, IsIso.inv_hom_id_assoc]
  rw [heq]
  infer_instance

/-- A graded quasi-isomorphism between uniformly finite filtered complexes is a
quasi-isomorphism on every filtration step and on the underlying complexes.
Source: Stacks Project, Derived Categories, Tag 05S3.
(blueprint: lem-kun-finite-filtered-graded-comparison).

Proof. Choose a common upper zero bound. At and above this bound the step maps
are maps between zero complexes and hence quasi-isomorphisms. Descend by integer
induction through the short exact sequences of successive steps and graded pieces.
The long exact cohomology sequences and the five lemma show that a step map is a
quasi-isomorphism if the next step map and its graded map are quasi-isomorphisms.
This proves the assertion for every integer filtration index. Finally choose a
common lower whole bound; the two step inclusions are isomorphisms, and their
commutative square identifies the underlying map with the step map up to these
isomorphisms. The argument imposes no bound on cochain degrees. -/
theorem finiteFilteredModule_graded_comparison {R : Type u} [CommRing R]
    {K L : FiniteFilteredModuleComplex R} (f : K ⟶ L)
    (hg : ∀ p : ℤ, QuasiIso (FilteredObject.gradedMapSteps f.hom p)) :
    QuasiIso f.hom.hom ∧
      ∀ p : ℤ, QuasiIso (FilteredObject.restrictionSteps f.hom p) :=
  ⟨underlying_quasiIso f hg, restriction_quasiIso f hg⟩

end CochainComplex
