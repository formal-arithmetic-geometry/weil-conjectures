/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import WeilConjectures.Mathlib.RingTheory.Valuation.LocalSubring
public import WeilConjectures.Mathlib.RingTheory.Valuation.ValuationSubring

/-!

# The dense-source valuative criterion

This file provides the scheme-theoretic inputs of the two-open compactification
theorem, following the blueprint chapter "Nagata compactification", section
"The dense-source valuative criterion" (proof order items 38–42):

- `AlgebraicGeometry.ValuationProbe` and `AlgebraicGeometry.nonempty_valuationProbe`:
  the **valuation probe through a schematically dense source** (Stacks Project
  Tag 02JQ; blueprint: `lemma:nagata-dense-valuation-probe-exists`; proof order
  item 38);
- `AlgebraicGeometry.ValuativeCriterion.universallyClosed_of_isDominant` and
  `AlgebraicGeometry.ValuativeCriterion.isSeparated_of_isDominant`: the
  **dense-source valuative criterion** (Stacks Project Tag 0894; blueprint:
  `lemma:nagata-dense-source-valuative`; proof order item 42): unique valuation
  lifting against squares whose generic point passes through a dense source implies
  universal closedness, and separatedness when the morphism is quasi-separated.

The valuation-theoretic inputs (proof order items 39–41) live in the Mathlib helper
files:

- the **composite of two valuation rings** `ValuationSubring.comapResidue` (blueprint:
  `lemma:nagata-composite-valuation-ring`; item 39) in
  `WeilConjectures.Mathlib.RingTheory.Valuation.ValuationSubring`;
- the **intersection with a dominating valuation ring**
  `ValuationSubring.comap_eq_of_le_comap` (Stacks Tag 052K; blueprint:
  `lemma:nagata-valuation-intersection`; item 40) and the **extension of a valuation
  ring to a field extension** `ValuationSubring.exists_comap_eq` (Stacks Tag 00IA;
  blueprint: `lemma:nagata-valuation-ring-extension`; item 41) in
  `WeilConjectures.Mathlib.RingTheory.Valuation.LocalSubring`;
- the topological core of the probe,
  `AlgebraicGeometry.exists_specializes_of_mem_closure_range`, in
  `WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`.

Items 38–41 are fully proved. The dense-source valuative criterion itself (item 42,
Stacks Tag 0894) is recorded with `sorry`: its proof is the reduction of an arbitrary
valuative square to one through the dense source, whose ingredients — the valuation
probe (item 38), the composite valuation ring (item 39), the extension lemma
(item 41) and the intersection lemma (item 40) — are all available.

-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

open IsLocalRing

/-- The data of a **valuation probe** for a morphism `h : T ⟶ P` centred at `z ∈ P`:
a valuation ring `R` with fraction field `K`, a generic lift `η : Spec K ⟶ T`, and a
map `α : Spec R ⟶ P` forming a commutative square with `h` and taking the closed
point of `Spec R` to `z`.
(Blueprint: `def:nagata-dense-valuation-probe`.) -/
structure ValuationProbe {T P : Scheme.{u}} (h : T ⟶ P) (z : P) where
  /-- The valuation ring of the probe. -/
  R : Type u
  [commRing : CommRing R]
  [domain : IsDomain R]
  [valuationRing : ValuationRing R]
  /-- The fraction field of the probe. -/
  K : Type u
  [field : Field K]
  [algebra : Algebra R K]
  [isFractionRing : IsFractionRing R K]
  /-- The generic lift through the source. -/
  η : Spec (CommRingCat.of K) ⟶ T
  /-- The centred valuation map to the target. -/
  α : Spec (CommRingCat.of R) ⟶ P
  commSq : CommSq η (Spec.map (CommRingCat.ofHom (algebraMap R K))) h α
  closedPoint_eq : α (IsLocalRing.closedPoint R) = z

namespace ValuationProbe

attribute [instance] commRing domain valuationRing field algebra isFractionRing

end ValuationProbe

/-- **Existence of a valuation probe through a schematically dense source** (Stacks
Project Tag 02JQ): let `h : T ⟶ P` be quasi-compact and scheme-theoretically
dominant, with `P` affine, and let `z ∈ P`. Then there is a valuation probe for `h`
centred at `z`.

The proof combines `exists_specializes_of_mem_closure_range` (the range of `h` is
dense, so `z` is a specialization of some `h t`) with the stalk construction of
Mathlib's valuative criterion: the composite `𝒪_{P,z} ⟶ 𝒪_{T,t} ⟶ κ(t)` factors
through a valuation subring `A ⊆ κ(t)` by Chevalley extension
(`IsLocalRing.exists_factor_valuationRing`), and the induced maps `Spec κ(t) ⟶ T`
and `Spec A ⟶ Spec 𝒪_{P,z} ⟶ P` form the probe.
(Blueprint: `lemma:nagata-dense-valuation-probe-exists`; proof order item 38.) -/
theorem nonempty_valuationProbe {T P : Scheme.{u}} (h : T ⟶ P) [QuasiCompact h]
    [IsSchemeTheoreticallyDominant h] [IsAffine P] (z : P) :
    Nonempty (ValuationProbe h z) := by
  have hz : z ∈ closure (Set.range h) := by
    rw [h.denseRange.closure_range]
    trivial
  obtain ⟨t, ht⟩ := exists_specializes_of_mem_closure_range h hz
  -- the stalk composite `𝒪_{P,z} ⟶ 𝒪_{T,t} ⟶ κ(t)` and its valuation factorization
  let ρ : P.presheaf.stalk z ⟶ T.residueField t :=
    P.presheaf.stalkSpecializes ht ≫ h.stalkMap t ≫ T.residue t
  obtain ⟨A, hA, hA_local⟩ := IsLocalRing.exists_factor_valuationRing ρ.hom
  let toA : P.presheaf.stalk z ⟶ .of A := CommRingCat.ofHom (ρ.hom.codRestrict _ hA)
  have w : T.fromSpecResidueField t ≫ h =
      Spec.map (CommRingCat.ofHom (algebraMap A (T.residueField t))) ≫
        Spec.map toA ≫ P.fromSpecStalk z := by
    rw [Scheme.fromSpecResidueField, Category.assoc, ← Scheme.SpecMap_stalkMap_fromSpecStalk,
      ← Scheme.SpecMap_stalkSpecializes_fromSpecStalk ht]
    simp_rw [← Spec.map_comp_assoc]
    rfl
  refine ⟨{ R := A
            K := T.residueField t
            η := T.fromSpecResidueField t
            α := Spec.map toA ≫ P.fromSpecStalk z
            commSq := ⟨w⟩
            closedPoint_eq := ?_ }⟩
  have h1 : Spec.map toA (IsLocalRing.closedPoint A) =
      IsLocalRing.closedPoint (P.presheaf.stalk z) :=
    IsLocalRing.comap_closedPoint (S := A) (ρ.hom.codRestrict A.toSubring hA)
  rw [Scheme.Hom.comp_apply, h1, Scheme.fromSpecStalk_closedPoint]

namespace ValuativeCriterion

/-- **The dense-source valuative criterion, universal closedness** (Stacks Project
Tag 0894): let `f : X ⟶ S` be quasi-compact and let `h : U ⟶ X` be quasi-compact,
quasi-separated and dominant. If every valuative commutative square for `f` whose
generic point factors through `U` admits a unique lift, then `f` is universally
closed.

The Stacks Project proof reduces an arbitrary valuative square to one through `U` by
the valuation probe (`nonempty_valuationProbe`) applied to a flat polynomial
presentation of the generic point, the composite valuation ring
(`ValuationSubring.comapResidue`), the extension lemma
(`ValuationSubring.exists_comap_eq`) and the intersection lemma
(`ValuationSubring.comap_eq_of_le_comap`).
(Blueprint: `lemma:nagata-dense-source-valuative`; proof order item 42.) -/
theorem universallyClosed_of_isDominant {U X S : Scheme.{u}} (f : X ⟶ S)
    [QuasiCompact f] (h : U ⟶ X) [QuasiCompact h] [QuasiSeparated h] [IsDominant h]
    (H : ∀ (sq : ValuativeCommSq f) (ηU : Spec (CommRingCat.of sq.K) ⟶ U),
      ηU ≫ h = sq.i₁ →
      ∃! l : Spec (CommRingCat.of sq.R) ⟶ X,
        Spec.map (CommRingCat.ofHom (algebraMap sq.R sq.K)) ≫ l = sq.i₁ ∧
        l ≫ f = sq.i₂) :
    UniversallyClosed f := by
  sorry

/-- **The dense-source valuative criterion, separatedness** (Stacks Project Tag 0894):
under the hypotheses of `universallyClosed_of_isDominant`, if `f` is moreover
quasi-separated then it is separated: the uniqueness hypothesis makes the diagonal
satisfy the dense-source criterion for universal closedness, and a universally closed
immersion is a closed immersion.
(Blueprint: `lemma:nagata-dense-source-valuative`; proof order item 42.) -/
theorem isSeparated_of_isDominant {U X S : Scheme.{u}} (f : X ⟶ S) [QuasiCompact f]
    [QuasiSeparated f] (h : U ⟶ X) [QuasiCompact h] [QuasiSeparated h] [IsDominant h]
    (H : ∀ (sq : ValuativeCommSq f) (ηU : Spec (CommRingCat.of sq.K) ⟶ U),
      ηU ≫ h = sq.i₁ →
      ∃! l : Spec (CommRingCat.of sq.R) ⟶ X,
        Spec.map (CommRingCat.ofHom (algebraMap sq.R sq.K)) ≫ l = sq.i₁ ∧
        l ≫ f = sq.i₂) :
    IsSeparated f := by
  sorry

end ValuativeCriterion

end AlgebraicGeometry
