/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import WeilConjectures.Compactification.TwoOpenSetup
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.IsIso

/-!

# The comparison space of the two-open compactification theorem

This file builds the comparison layer of the two-open compactification theorem,
following the blueprint chapter "Nagata compactification", section "The two-open
compactification theorem" (`def:nagata-two-open-comparison-space` through
`lemma:nagata-one-valuation-avoids-boundary`):

Given two sides `σ₁ : TwoOpenSide u O₁ O₂` and `σ₂ : TwoOpenSide u O₂ O₁`,

- `AlgebraicGeometry.TwoOpenSide.comparisonMap`: the canonical morphism
  `V₁ ×_U V₂ ⟶ X₁ ×_S X₂` (blueprint: `def:nagata-two-open-comparison-space`);
- `AlgebraicGeometry.TwoOpenSide.comparisonSpace`: its scheme-theoretic image `X₁₂`,
  with the two proper projections `comparisonFst`/`comparisonSnd` (blueprint:
  `lemma:nagata-comparison-projections-proper`);
- `AlgebraicGeometry.TwoOpenSide.KeyDisjoint`: the **key boundary disjointness**
  `X₁₂ ∩ (Z̄₁,₂ ×_S Z̄₂,₁) = ∅` in pointwise form (blueprint:
  `lemma:nagata-key-boundary-disjointness`);
- `AlgebraicGeometry.TwoOpenSide.KeyDisjoint.avoids`: key disjointness implies that of
  any pair of valuation-ring extensions of a common generic point of `O₁ ∩ O₂` to the
  two ambient models, at least one avoids its forbidden boundary (blueprint:
  `lemma:nagata-valuation-pair-factors-comparison`,
  `lemma:nagata-valuation-open-closed-point`,
  `lemma:nagata-one-valuation-avoids-boundary`);
- `AlgebraicGeometry.TwoOpenPreparation`: the bundled output of the comparison layer,
  consumed by the final assembly of the two-open theorem;
- `AlgebraicGeometry.nonempty_twoOpenPreparation`: existence. The construction of a
  key-disjoint prepared pair (`exists_prepared_keyDisjoint_twoOpenSide`) is the
  improved-comparison chain of the blueprint
  (`lemma:nagata-comparison-restrict-proper-open`,
  `def:nagata-two-open-improved-comparison` via Stacks Project Tags 0F3W and 0F3Y,
  `lemma:nagata-comparison-boundary-density`,
  `lemma:nagata-key-boundary-disjointness`); it consumes the modification inputs
  `exists_admissibleBlowup_strictTransform_isIso_near_closure` and
  `Scheme.Hom.schemeTheoreticImage_after_admissibleBlowup`, and therefore, through
  them, Stacks Tag 081S — see the "Dependency structure" section of the module
  docstring of `WeilConjectures.Compactification.Modification`.

## The one obligation of this file

`AlgebraicGeometry.exists_admissibleBlowup_comparisonBoundary_subset_selfBoundary` is
the **only** `sorry` here, and everything else in the improved-comparison chain is
proved around it:

- `TwoOpenSide.comparisonBoundary` names the locus of the comparison space lying over
  the forbidden boundary of the first side, and `isClosed_comparisonBoundary` records
  that it is closed;
- `TwoOpenSide.comparisonBoundary_subset_preimage_selfBoundary` is the density
  criterion `lemma:nagata-comparison-boundary-density`: controlling the second
  projection on a subset whose closure swallows the comparison boundary suffices,
  because the self boundary is itself a closure;
- `TwoOpenSide.keyDisjoint_of_comparisonBoundary_subset` is
  `lemma:nagata-key-boundary-disjointness`: a comparison boundary landing in the self
  boundary `Z̄₂,₂` of a *prepared* second side cannot meet its forbidden boundary
  `Z̄₂,₁`. This is the final link of the chain and the only one needing neither
  Tag 0F3W nor Tag 0F3Y;
- `exists_prepared_keyDisjoint_twoOpenSide` then assembles the pair from
  `exists_prepared_twoOpenSide` (proved) and `TwoOpenSide.Prepared.admissibleBlowup`
  (proved), so the obligation carries none of that bookkeeping: what is left is
  exactly the geometric step that improves the first side.

-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory Limits IsLocalRing

namespace AlgebraicGeometry

variable {U S : Scheme.{u}} {u : U ⟶ S} {O₁ O₂ : U.Opens}

namespace TwoOpenSide

variable (σ₁ : TwoOpenSide u O₁ O₂) (σ₂ : TwoOpenSide u O₂ O₁)

/-- The canonical morphism `V₁ ×_U V₂ ⟶ X₁ ×_S X₂` from the fibre product of the two
proper extensions to the product of the two ambient models.
(Blueprint: `def:nagata-two-open-comparison-space`.) -/
def comparisonMap : pullback σ₁.ψ σ₂.ψ ⟶ pullback σ₁.s σ₂.s :=
  pullback.map σ₁.ψ σ₂.ψ σ₁.s σ₂.s σ₁.V.ι σ₂.V.ι u σ₁.ψ_u σ₂.ψ_u

/-- The **comparison space** `X₁₂`: the scheme-theoretic image of `V₁ ×_U V₂` in
`X₁ ×_S X₂`. (Blueprint: `def:nagata-two-open-comparison-space`.) -/
def comparisonSpace : Scheme.{u} := (comparisonMap σ₁ σ₂).image

/-- The first projection `X₁₂ ⟶ X₁` of the comparison space. -/
def comparisonFst : comparisonSpace σ₁ σ₂ ⟶ σ₁.X :=
  (comparisonMap σ₁ σ₂).imageι ≫ pullback.fst σ₁.s σ₂.s

/-- The second projection `X₁₂ ⟶ X₂` of the comparison space. -/
def comparisonSnd : comparisonSpace σ₁ σ₂ ⟶ σ₂.X :=
  (comparisonMap σ₁ σ₂).imageι ≫ pullback.snd σ₁.s σ₂.s

@[simp]
lemma comparisonFst_eq :
    comparisonFst σ₁ σ₂ = (comparisonMap σ₁ σ₂).imageι ≫ pullback.fst σ₁.s σ₂.s := rfl

@[simp]
lemma comparisonSnd_eq :
    comparisonSnd σ₁ σ₂ = (comparisonMap σ₁ σ₂).imageι ≫ pullback.snd σ₁.s σ₂.s := rfl

/-- **Properness of the comparison projections** (blueprint:
`lemma:nagata-comparison-projections-proper`): the projection `X₁₂ ⟶ X₁` is a closed
immersion followed by a base change of the proper structure morphism of `X₂`. -/
theorem isProper_comparisonFst : IsProper (comparisonFst σ₁ σ₂) := by
  have := σ₂.isProper_s
  rw [comparisonFst_eq]
  infer_instance

/-- **Properness of the comparison projections**, second projection: `X₁₂ ⟶ X₂` is a
closed immersion followed by a base change of the proper structure morphism of `X₁`. -/
theorem isProper_comparisonSnd : IsProper (comparisonSnd σ₁ σ₂) := by
  have := σ₁.isProper_s
  rw [comparisonSnd_eq]
  infer_instance

/-- The **key boundary disjointness** (blueprint:
`lemma:nagata-key-boundary-disjointness`): no point of the comparison space projects
into the forbidden boundary on both sides, i.e.
`X₁₂ ∩ (Z̄₁,₂ ×_S Z̄₂,₁) = ∅` inside `X₁ ×_S X₂`. -/
def KeyDisjoint : Prop :=
  ∀ z : comparisonSpace σ₁ σ₂,
    comparisonFst σ₁ σ₂ z ∈ σ₁.forbiddenBoundary →
    comparisonSnd σ₁ σ₂ z ∉ σ₂.forbiddenBoundary

/-- The **comparison boundary** of the pair `(σ₁, σ₂)`: the locus of the comparison
space lying over the forbidden boundary `Z̄₁,₂` of the first side. Key boundary
disjointness is the assertion that its second projection avoids the forbidden boundary
of the second side. (Blueprint: `lemma:nagata-comparison-boundary-density`.) -/
def comparisonBoundary : Set (comparisonSpace σ₁ σ₂) :=
  comparisonFst σ₁ σ₂ ⁻¹' σ₁.forbiddenBoundary

lemma isClosed_comparisonBoundary : IsClosed (comparisonBoundary σ₁ σ₂) :=
  isClosed_closure.preimage (comparisonFst σ₁ σ₂).continuous

variable {σ₁ σ₂} in
lemma mem_comparisonBoundary_iff {z : comparisonSpace σ₁ σ₂} :
    z ∈ comparisonBoundary σ₁ σ₂ ↔
      comparisonFst σ₁ σ₂ z ∈ σ₁.forbiddenBoundary :=
  Iff.rfl

variable {σ₁ σ₂} in
/-- **Key boundary disjointness from the self boundary** (blueprint:
`lemma:nagata-key-boundary-disjointness`): if the second projection of the comparison
boundary lands in the self boundary `Z̄₂,₂` of the second side, then key disjointness
holds, because a prepared side has disjoint self and forbidden boundaries.

This is the final link of the improved-comparison chain, and the only one of its links
that needs neither Stacks Project Tag 0F3W nor Tag 0F3Y. -/
theorem keyDisjoint_of_comparisonBoundary_subset (h₂ : σ₂.Prepared)
    (h : comparisonBoundary σ₁ σ₂ ⊆ comparisonSnd σ₁ σ₂ ⁻¹' σ₂.selfBoundary) :
    KeyDisjoint σ₁ σ₂ :=
  fun _ hz ↦ Set.disjoint_left.mp h₂ (h hz)

variable {σ₁ σ₂} in
/-- **The comparison boundary density criterion** (blueprint:
`lemma:nagata-comparison-boundary-density`): it suffices to control the second
projection on a subset `D` in which the comparison boundary is contained after taking
closures. The locus where the second projection lands in the self boundary is closed,
since the self boundary is a closure, so it swallows `closure D`. -/
theorem comparisonBoundary_subset_preimage_selfBoundary {D : Set (comparisonSpace σ₁ σ₂)}
    (hD : comparisonBoundary σ₁ σ₂ ⊆ closure D)
    (hmem : ∀ z ∈ D, comparisonSnd σ₁ σ₂ z ∈ σ₂.selfBoundary) :
    comparisonBoundary σ₁ σ₂ ⊆ comparisonSnd σ₁ σ₂ ⁻¹' σ₂.selfBoundary :=
  hD.trans <| closure_minimal hmem <|
    isClosed_closure.preimage (comparisonSnd σ₁ σ₂).continuous

variable {σ₁ σ₂} in
/-- **Key boundary disjointness by density** (blueprint:
`lemma:nagata-comparison-boundary-density`, `lemma:nagata-key-boundary-disjointness`):
the combination of the two previous lemmas, which is the shape the improved-comparison
chain of the blueprint produces. -/
theorem keyDisjoint_of_dense_comparisonBoundary (h₂ : σ₂.Prepared)
    {D : Set (comparisonSpace σ₁ σ₂)} (hD : comparisonBoundary σ₁ σ₂ ⊆ closure D)
    (hmem : ∀ z ∈ D, comparisonSnd σ₁ σ₂ z ∈ σ₂.selfBoundary) :
    KeyDisjoint σ₁ σ₂ :=
  keyDisjoint_of_comparisonBoundary_subset h₂
    (comparisonBoundary_subset_preimage_selfBoundary hD hmem)

section Avoids

variable {σ₁ σ₂}
variable {A K : Type u} [CommRing A] [IsDomain A] [ValuationRing A] [Field K]
  [Algebra A K] [IsFractionRing A K]
  (η : Spec (CommRingCat.of K) ⟶ (O₁ ⊓ O₂ : U.Opens).toScheme)
  (g₁ : Spec (CommRingCat.of A) ⟶ σ₁.X) (g₂ : Spec (CommRingCat.of A) ⟶ σ₂.X)

/-- **One valuation extension avoids its forbidden boundary** (blueprint:
`lemma:nagata-valuation-pair-factors-comparison`,
`lemma:nagata-valuation-open-closed-point`,
`lemma:nagata-one-valuation-avoids-boundary`): let `A` be a valuation ring with
fraction field `K`, let `η : Spec K ⟶ O₁ ∩ O₂` be a generic point, and let `g₁`, `g₂`
be extensions of `η` to `Spec A` in the two ambient models, lying over the same
morphism to `S`. If the key boundary disjointness holds, then at least one `gᵢ` factors
through the complement `Xᵢ°` of the forbidden boundary. -/
theorem KeyDisjoint.avoids (hkey : KeyDisjoint σ₁ σ₂)
    (hg₁ : Spec.map (CommRingCat.ofHom (algebraMap A K)) ≫ g₁ =
      η ≫ U.homOfLE inf_le_left ≫ σ₁.embX)
    (hg₂ : Spec.map (CommRingCat.ofHom (algebraMap A K)) ≫ g₂ =
      η ≫ U.homOfLE inf_le_right ≫ σ₂.embX)
    (hS : g₁ ≫ σ₁.s = g₂ ≫ σ₂.s) :
    Set.range g₁ ⊆ (σ₁.interior : Set σ₁.X) ∨
      Set.range g₂ ⊆ (σ₂.interior : Set σ₂.X) := by
  have := σ₁.isOpenImmersion_υ
  have := σ₂.isOpenImmersion_υ
  -- it suffices that one closed point avoids its forbidden boundary
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨h₁, h₂⟩ := hcon
  have hclosed : ∀ {X₀ : Scheme.{u}} (g : Spec (CommRingCat.of A) ⟶ X₀)
      {F : Set X₀}, IsClosed F → ¬ Set.range g ⊆ Fᶜ →
      g (closedPoint (CommRingCat.of A)) ∈ F := by
    intro X₀ g F hF hne
    rw [Set.not_subset] at hne
    obtain ⟨-, ⟨a, rfl⟩, ha⟩ := hne
    rw [Set.mem_compl_iff, not_not] at ha
    exact ((specializes_closedPoint a).map g.continuous).mem_closed hF ha
  have hz₁ : g₁ (closedPoint (CommRingCat.of A)) ∈ σ₁.forbiddenBoundary :=
    hclosed g₁ isClosed_closure h₁
  have hz₂ : g₂ (closedPoint (CommRingCat.of A)) ∈ σ₂.forbiddenBoundary :=
    hclosed g₂ isClosed_closure h₂
  -- the pair of extensions as a morphism to `X₁ ×_S X₂`
  let ĝ : Spec (CommRingCat.of A) ⟶ pullback σ₁.s σ₂.s := pullback.lift g₁ g₂ hS
  have hĝ₁ : ĝ ≫ pullback.fst σ₁.s σ₂.s = g₁ := pullback.lift_fst _ _ _
  have hĝ₂ : ĝ ≫ pullback.snd σ₁.s σ₂.s = g₂ := pullback.lift_snd _ _ _
  -- the generic pair factors through `V₁ ×_U V₂`
  have hψ : (η ≫ U.homOfLE inf_le_left ≫ σ₁.υ) ≫ σ₁.ψ =
      (η ≫ U.homOfLE inf_le_right ≫ σ₂.υ) ≫ σ₂.ψ := by
    simp only [Category.assoc, σ₁.υ_ψ, σ₂.υ_ψ, Scheme.homOfLE_ι]
  let ηV : Spec (CommRingCat.of K) ⟶ pullback σ₁.ψ σ₂.ψ :=
    pullback.lift (η ≫ U.homOfLE inf_le_left ≫ σ₁.υ)
      (η ≫ U.homOfLE inf_le_right ≫ σ₂.υ) hψ
  have hηV₁ : ηV ≫ pullback.fst σ₁.ψ σ₂.ψ = η ≫ U.homOfLE inf_le_left ≫ σ₁.υ :=
    pullback.lift_fst _ _ _
  have hηV₂ : ηV ≫ pullback.snd σ₁.ψ σ₂.ψ = η ≫ U.homOfLE inf_le_right ≫ σ₂.υ :=
    pullback.lift_snd _ _ _
  have hcmp₁ : comparisonMap σ₁ σ₂ ≫ pullback.fst σ₁.s σ₂.s =
      pullback.fst σ₁.ψ σ₂.ψ ≫ σ₁.V.ι := pullback.lift_fst _ _ _
  have hcmp₂ : comparisonMap σ₁ σ₂ ≫ pullback.snd σ₁.s σ₂.s =
      pullback.snd σ₁.ψ σ₂.ψ ≫ σ₂.V.ι := pullback.lift_snd _ _ _
  -- the whole `Spec A` factors through the comparison space
  have hcomm : (ηV ≫ (comparisonMap σ₁ σ₂).toImage) ≫ (comparisonMap σ₁ σ₂).imageι =
      Spec.map (CommRingCat.ofHom (algebraMap A K)) ≫ ĝ := by
    rw [Category.assoc, Scheme.Hom.toImage_imageι]
    apply pullback.hom_ext
    · rw [Category.assoc, hcmp₁, reassoc_of% hηV₁, Category.assoc, hĝ₁, hg₁]
      simp only [embX]
    · rw [Category.assoc, hcmp₂, reassoc_of% hηV₂, Category.assoc, hĝ₂, hg₂]
      simp only [embX]
  obtain ⟨l, hl⟩ := IsClosedImmersion.exists_lift_of_isFractionRing
    (comparisonMap σ₁ σ₂).imageι ĝ (ηV ≫ (comparisonMap σ₁ σ₂).toImage) hcomm
  -- the closed point of the factorization violates the key disjointness
  have hl₁ : l ≫ comparisonFst σ₁ σ₂ = g₁ := by
    rw [comparisonFst, ← Category.assoc, hl, hĝ₁]
  have hl₂ : l ≫ comparisonSnd σ₁ σ₂ = g₂ := by
    rw [comparisonSnd, ← Category.assoc, hl, hĝ₂]
  have heq₁ : comparisonFst σ₁ σ₂ (l (closedPoint (CommRingCat.of A))) =
      g₁ (closedPoint (CommRingCat.of A)) :=
    calc comparisonFst σ₁ σ₂ (l (closedPoint (CommRingCat.of A)))
        = (l ≫ comparisonFst σ₁ σ₂) (closedPoint (CommRingCat.of A)) :=
          (Scheme.Hom.comp_apply _ _ _).symm
      _ = g₁ (closedPoint (CommRingCat.of A)) := by rw [hl₁]
  have heq₂ : comparisonSnd σ₁ σ₂ (l (closedPoint (CommRingCat.of A))) =
      g₂ (closedPoint (CommRingCat.of A)) :=
    calc comparisonSnd σ₁ σ₂ (l (closedPoint (CommRingCat.of A)))
        = (l ≫ comparisonSnd σ₁ σ₂) (closedPoint (CommRingCat.of A)) :=
          (Scheme.Hom.comp_apply _ _ _).symm
      _ = g₂ (closedPoint (CommRingCat.of A)) := by rw [hl₂]
  refine hkey (l (closedPoint (CommRingCat.of A))) ?_ ?_
  · rwa [heq₁]
  · rwa [heq₂]

end Avoids

end TwoOpenSide

open TwoOpenSide in
/-- **The improved comparison** (Stacks Project Tags 0F3W and 0F3Y; blueprint:
`lemma:nagata-comparison-restrict-proper-open`,
`def:nagata-two-open-improved-comparison`,
`lemma:nagata-comparison-isIso-near-boundary`,
`lemma:nagata-comparison-boundary-density`): two prepared sides can be improved, by a
`V₁`-admissible blow-up of the ambient model of the first side, so that the comparison
boundary of the improved pair projects into the self boundary of the second side.

This is the geometric core of the comparison layer and the **one remaining obligation**
of this file. The construction of the blueprint applies the isomorphism-near-closure
blow-up (Tag 0F3W) to the proper first comparison projection
(`isProper_comparisonFst`) at the forbidden boundary locus of the first side; under
that blow-up the comparison space becomes the strict transform of the old one
(Tag 0F3Y, `Scheme.Hom.schemeTheoreticImage_after_admissibleBlowup`), the comparison
space is isomorphic to a neighbourhood of the boundary, and the comparison boundary is
dense in the inverse image of the boundary closure — so
`keyDisjoint_of_dense_comparisonBoundary` reduces the conclusion to the second
projection of that dense locus, which lands in the self boundary of the second side.

The blow-up shape of the conclusion is the one the surrounding API was built for:
`TwoOpenSide.admissibleBlowup` and `TwoOpenSide.Prepared.admissibleBlowup` both cite
`def:nagata-two-open-improved-comparison`, and preparedness of the improved first side
is exactly what the latter supplies. -/
theorem exists_admissibleBlowup_comparisonBoundary_subset_selfBoundary [IsNoetherian S]
    {u : U ⟶ S} [IsSeparated u] [LocallyOfFiniteType u] [QuasiCompact u]
    {O₁ O₂ : U.Opens} (σ₁ : TwoOpenSide u O₁ O₂) (σ₂ : TwoOpenSide u O₂ O₁)
    (h₁ : σ₁.Prepared) (h₂ : σ₂.Prepared) (hcov : O₁ ⊔ O₂ = ⊤) :
    ∃ B : AdmissibleBlowup σ₁.X σ₁.V,
      comparisonBoundary (σ₁.admissibleBlowup B) σ₂ ⊆
        comparisonSnd (σ₁.admissibleBlowup B) σ₂ ⁻¹' σ₂.selfBoundary := by
  sorry

open TwoOpenSide in
/-- **Existence of a prepared, key-disjoint pair of sides** (blueprint:
`lemma:nagata-comparison-restrict-proper-open`,
`def:nagata-two-open-improved-comparison`,
`lemma:nagata-comparison-isIso-near-boundary`,
`lemma:nagata-comparison-boundary-density`,
`lemma:nagata-key-boundary-disjointness`): after improving the first side by the
isomorphism-near-closure blow-up (Stacks Project Tag 0F3W) of the first comparison
projection at the forbidden boundary locus — under which the comparison space becomes
the strict transform (Stacks Project Tag 0F3Y) — the two prepared sides satisfy the
key boundary disjointness: over the improved first projection the comparison space is
isomorphic to a neighbourhood of the boundary, the comparison boundary is dense in the
inverse image of the boundary closure, and its second projection lands in the self
boundary of the second side, which is disjoint from the forbidden one.

The proof consumes the sorried modification inputs
(`exists_admissibleBlowup_strictTransform_isIso_near_closure`,
`Scheme.Hom.schemeTheoreticImage_after_admissibleBlowup`) through
`exists_admissibleBlowup_comparisonBoundary_subset_selfBoundary`, which is the only
remaining obligation of this file; see the module docstring. -/
theorem exists_prepared_keyDisjoint_twoOpenSide [IsNoetherian S] (u : U ⟶ S)
    [IsSeparated u] [LocallyOfFiniteType u] [QuasiCompact u] (O₁ O₂ : U.Opens)
    (hcov : O₁ ⊔ O₂ = ⊤) [HasCompactification (O₁.ι ≫ u)]
    [HasCompactification (O₂.ι ≫ u)] :
    ∃ (σ₁ : TwoOpenSide u O₁ O₂) (σ₂ : TwoOpenSide u O₂ O₁),
      σ₁.Prepared ∧ σ₂.Prepared ∧ KeyDisjoint σ₁ σ₂ := by
  obtain ⟨σ₁, h₁⟩ := exists_prepared_twoOpenSide u O₁ O₂ hcov
  obtain ⟨σ₂, h₂⟩ := exists_prepared_twoOpenSide u O₂ O₁ (by rw [sup_comm]; exact hcov)
  obtain ⟨B, hB⟩ :=
    exists_admissibleBlowup_comparisonBoundary_subset_selfBoundary σ₁ σ₂ h₁ h₂ hcov
  exact ⟨σ₁.admissibleBlowup B, σ₂, TwoOpenSide.Prepared.admissibleBlowup σ₁ B h₁,
    h₂, keyDisjoint_of_comparisonBoundary_subset h₂ hB⟩

/-- The bundled output of the comparison layer of the two-open compactification
theorem: two prepared sides satisfying the key boundary disjointness. This is the
input of the final assembly. -/
structure TwoOpenPreparation (u : U ⟶ S) (O₁ O₂ : U.Opens) where
  /-- The prepared side over the first open. -/
  side₁ : TwoOpenSide u O₁ O₂
  /-- The prepared side over the second open. -/
  side₂ : TwoOpenSide u O₂ O₁
  prepared₁ : side₁.Prepared
  prepared₂ : side₂.Prepared
  keyDisjoint : TwoOpenSide.KeyDisjoint side₁ side₂

/-- Existence of the comparison-layer data of the two-open compactification
theorem. -/
theorem nonempty_twoOpenPreparation [IsNoetherian S] (u : U ⟶ S) [IsSeparated u]
    [LocallyOfFiniteType u] [QuasiCompact u] (O₁ O₂ : U.Opens) (hcov : O₁ ⊔ O₂ = ⊤)
    [HasCompactification (O₁.ι ≫ u)] [HasCompactification (O₂.ι ≫ u)] :
    Nonempty (TwoOpenPreparation u O₁ O₂) := by
  obtain ⟨σ₁, σ₂, h₁, h₂, hkey⟩ :=
    exists_prepared_keyDisjoint_twoOpenSide u O₁ O₂ hcov
  exact ⟨⟨σ₁, σ₂, h₁, h₂, hkey⟩⟩

end AlgebraicGeometry
