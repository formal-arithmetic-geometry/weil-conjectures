/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.ProfiniteCondensedRing
public import WeilConjectures.CategoryTheory.DerivedCategory.TorAmplitude
import WeilConjectures.AlgebraicGeometry.IntegralCtfEqualsBc

/-! # The ambient realization at condensed field coefficients

The coefficient object is `Λ_Y = p_Y^* Λ`. Bounded constructible complexes form a
full subcategory of its ordinary internal-module derived category. Their realization
is its canonical inclusion, retaining the underlying objects and morphisms.

Source: current blueprint `lem-integral-ctf-equals-bc`, field case of clauses (1), (2),
and `det-def-sfb-bounded-constructible`.
(blueprint: lem-sf-field-stage-ordinary-realization).
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj

namespace WeilConjectures.OrdinaryFieldRealization.Condensed

/-- The ambient category over the pulled-back condensed coefficient ring.
Source: blueprint `det-def-sfb-derived-categories`
(blueprint: lem-sf-field-stage-ordinary-realization). -/
abbrev Ambient (Y : Scheme.{u}) (Λ : Profinite.CondensedRing.{u}) :=
  DerivedCategory
    (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ.X Y))

/-- Bounded constructibility uses the blueprint's finite constant local models.
Source: blueprint `det-def-sfb-bounded-constructible`
(blueprint: lem-sf-field-stage-ordinary-realization). -/
abbrev Constructible (Y : Scheme.{u}) (Λ : Profinite.CondensedRing.{u})
    [IsCommMonObj Λ.X] :=
  ConstantModelBoundedConstructible Λ.X Y

/-- Realization is the actual full-subcategory inclusion.
Source: blueprint `det-def-sfb-bounded-constructible`
(blueprint: lem-sf-field-stage-ordinary-realization). -/
def realization (Y : Scheme.{u}) (Λ : Profinite.CondensedRing.{u})
    [IsCommMonObj Λ.X] :
    Constructible Y Λ ⥤ Ambient Y Λ :=
  (constantModelBoundedConstructible Λ.X Y).ι

/-- The inclusion retains every ambient morphism.
Source: the full-subcategory definition
(blueprint: lem-sf-field-stage-ordinary-realization).
Proof: the inverse on each Hom set wraps the same ambient morphism. -/
def realizationFullyFaithful (Y : Scheme.{u}) (Λ : Profinite.CondensedRing.{u})
    [IsCommMonObj Λ.X] :
    (realization Y Λ).FullyFaithful :=
  ObjectProperty.fullyFaithfulι _

/-- Realization leaves the underlying complex unchanged.
Source: the full-subcategory definition
(blueprint: lem-sf-field-stage-ordinary-realization). -/
theorem realization_obj (Y : Scheme.{u}) (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]
    (K : Constructible Y Λ) : (realization Y Λ).obj K = K.obj := rfl

/-- Realization leaves the ambient derived morphism unchanged.
Source: the full-subcategory definition
(blueprint: lem-sf-field-stage-ordinary-realization). -/
theorem realization_map (Y : Scheme.{u}) (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]
    {K L : Constructible Y Λ} (f : K ⟶ L) :
    (realization Y Λ).map f = f.hom := rfl

/-- A single ordered cohomological interval bounds each realized object.
Source: blueprint `det-def-sfb-bounded-constructible`
(blueprint: lem-sf-field-stage-ordinary-realization).
Proof: take the lower and upper bounds in the bounded t-structure predicate and
replace the lower bound by its minimum with the upper bound. This also handles zero
objects, whose originally chosen bounds need not be ordered. -/
theorem realization_bounded (Y : Scheme.{u}) (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]
    (K : Constructible Y Λ) :
    ∃ a b : ℤ, a ≤ b ∧ DerivedCategory.homologyConcentratedIn a b
      ((realization Y Λ).obj K) := by
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := K.property.1
  refine ⟨min a b, b, min_le_right _ _, ?_, hb⟩
  exact (DerivedCategory.isGE_iff K.obj _).2 fun q hq ↦
    (DerivedCategory.isGE_iff K.obj a).1 ha q (lt_of_lt_of_le hq (min_le_left _ _))

/-- The field families of the current blueprint, allowing coefficient isomorphisms.
Source: blueprint `lem-integral-ctf-equals-bc`
(blueprint: lem-sf-field-stage-ordinary-realization). -/
def IsFieldCoefficient (ℓ : ℕ) [Fact ℓ.Prime] (Λ : Profinite.CondensedRing.{u}) : Prop :=
  Nonempty (Λ ≅ Mon.mk (Profinite.continuousMapRingObj ℚ_[ℓ])) ∨
    (∃ E : PadicAlgCl.FiniteIntermediateField ℓ,
      Nonempty (Λ ≅ Mon.mk (Profinite.continuousMapRingObj E))) ∨
    Nonempty (Λ ≅ Mon.mk (Profinite.padicAlgClRingObj ℓ))

/-- Over condensed field coefficients realization preserves the precise Tor interval.
Source: blueprint `lem-integral-ctf-equals-bc`, clause (2), field case
(blueprint: lem-sf-field-stage-ordinary-realization).
Proof: apply the field clause of the integral/field Tor criterion to the unchanged
ambient object and its defining bounded-constructibility proof. That criterion uses
flat finite constant field models, stratification, and finite truncation triangles. -/
theorem realization_torAmplitude (ℓ : ℕ) [Fact ℓ.Prime]
    (Y : Scheme.{u}) [CompactSpace Y] [QuasiSeparatedSpace Y]
    (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]
    (hΛ : IsFieldCoefficient ℓ Λ) (K : Constructible Y Λ)
    (a b : ℤ) (hab : a ≤ b)
    (hK : DerivedCategory.homologyConcentratedIn a b ((realization Y Λ).obj K)) :
    DerivedCategory.torAmplitudeIn _ a b ((realization Y Λ).obj K) := by
  have h := integral_ctf_equals_bc ℓ Y Λ (by
    rcases hΛ with h | ⟨E, h⟩ | h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl ⟨E, Or.inr h⟩))
    · exact Or.inr (Or.inr (Or.inr h)))
  exact (h.2.2.1 hΛ).2 K.obj a b hab K.property hK

/-- The ambient realization exists canonically, is fully faithful, has bounded values,
and every cohomological interval is a Tor interval over condensed field coefficients.
Consequently `Dctf = Dbc` in this same ambient category.

Source: blueprint `lem-integral-ctf-equals-bc`, field case of clause (2)
(blueprint: lem-sf-field-stage-ordinary-realization).

Proof: use the full-subcategory inclusion, whose object and morphism maps are identities.
Boundedness supplies an ordered cohomological interval independently of any tensor test
module. The field Tor criterion gives the identical Tor interval. Conversely the
finite-Tor constructible predicate implies bounded constructibility by its definition;
these two implications give equality of object predicates. -/
theorem exists_ordinaryFieldRealization (ℓ : ℕ) [Fact ℓ.Prime]
    (Y : Scheme.{u}) [CompactSpace Y] [QuasiSeparatedSpace Y]
    (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]
    (hΛ : IsFieldCoefficient ℓ Λ) :
    Nonempty ((realization Y Λ).FullyFaithful) ∧
    (∀ K : Constructible Y Λ, ∃ a b : ℤ, a ≤ b ∧
      DerivedCategory.homologyConcentratedIn a b ((realization Y Λ).obj K) ∧
      DerivedCategory.torAmplitudeIn _ a b ((realization Y Λ).obj K)) ∧
    (constantModelBoundedConstructible Λ.X Y ⊓ DerivedCategory.finiteTorAmplitude _) =
      constantModelBoundedConstructible Λ.X Y := by
  have hfinite (K : Constructible Y Λ) : ∃ a b : ℤ, a ≤ b ∧
      DerivedCategory.homologyConcentratedIn a b ((realization Y Λ).obj K) ∧
      DerivedCategory.torAmplitudeIn _ a b ((realization Y Λ).obj K) := by
    obtain ⟨a, b, hab, hK⟩ := realization_bounded Y Λ K
    exact ⟨a, b, hab, hK, realization_torAmplitude ℓ Y Λ hΛ K a b hab hK⟩
  refine ⟨⟨realizationFullyFaithful Y Λ⟩, hfinite, ?_⟩
  funext K
  apply propext
  constructor
  · exact And.left
  · intro hK
    obtain ⟨a, b, _, _, ht⟩ := hfinite ⟨K, hK⟩
    exact ⟨hK, a, b, ht⟩

end WeilConjectures.OrdinaryFieldRealization.Condensed
