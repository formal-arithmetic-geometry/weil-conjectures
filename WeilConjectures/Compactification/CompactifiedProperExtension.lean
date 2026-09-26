/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import WeilConjectures.Blowup.Density
public import WeilConjectures.Compactification.Defs
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Proper
public import WeilConjectures.Mathlib.AlgebraicGeometry.Restrict
public import WeilConjectures.Mathlib.Topology.Continuous

/-!

# Compactified proper extensions and their transport along an admissible blow-up

The structure `AlgebraicGeometry.CompactifiedProperExtension u O` records, for a morphism
`u : U ⟶ S` and an open `O` of `U`, a proper extension `ψ : V ⟶ U` of the inclusion of an
embedded copy of `O`, which is an isomorphism over `O`, together with a compactification `X`
of `V` over `S` in which that copy of `O` is scheme-theoretically dominant. This is one *side*
of the two-open compactification theorem (blueprint:
`def:nagata-two-open-graph-extensions`, the density condition being that of
`lemma:nagata-two-open-dense-compactifications`).

The other open `O'` of the two-open construction enters only through the boundary loci, so it
is a parameter of those and not of the structure itself
(blueprint: `def:nagata-two-open-boundary-loci`):

* `CompactifiedProperExtension.selfBoundary O'` — the closure in `X.Z` of `ψ ⁻¹ (U ∖ O')`;
* `CompactifiedProperExtension.forbiddenBoundary` — the closure in `X.Z` of `ψ ⁻¹ (U ∖ O)`.

The predicate `CompactifiedProperExtension.Prepared O'` states that the two boundary closures
are disjoint (blueprint: `def:nagata-two-open-prepared-boundaries`). The complement of the
forbidden boundary is the open `CompactifiedProperExtension.interiorLocus` (the `Xᵢ°` of
`def:nagata-two-open-intermediate-schemes`), which contains the embedded copy of `O`
(`CompactifiedProperExtension.interiorLocusEmb`).

The main results are `CompactifiedProperExtension.admissibleBlowup`, transporting a side along
a `V`-admissible blow-up of the ambient scheme, and
`CompactifiedProperExtension.Prepared.admissibleBlowup`, saying that preparedness persists:
boundary loci transport to preimages
(`CompactifiedProperExtension.admissibleBlowup_image_preimage`), so disjointness is preserved
(blueprint: `def:nagata-two-open-side-transport`,
`lemma:nagata-two-open-side-transport-prepared`).

-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory

namespace AlgebraicGeometry

variable {U S : Scheme.{u}}

/-- A **compactified proper extension** of an open `O` of `U` along `u : U ⟶ S`: a proper
extension `ψ : V ⟶ U` of the inclusion of `O`, which is an isomorphism over `O`, together
with a compactification of `V` over `S` in which the copy of `O` is scheme-theoretically
dominant (blueprint: `def:nagata-two-open-graph-extensions`, with the density condition of
`lemma:nagata-two-open-dense-compactifications`).

```
   O ───υ──→ V              V ───ψ──→ U
    ╲        │              │         │
 O.ι ╲       │ ψ        X.i │         │ u
      ↘      ↓              ↓         ↓
             U             X.Z ──X.g→ S
```

In the two-open construction, the second open plays no role in this data; it enters only as a
parameter of the boundary locus `CompactifiedProperExtension.selfBoundary` and of the
preparedness predicate `CompactifiedProperExtension.Prepared`. -/
structure CompactifiedProperExtension (u : U ⟶ S) (O : U.Opens) where
  /-- The proper extension of `O` over `U`. -/
  V : Scheme.{u}
  /-- The structure morphism of `V` over `U`. -/
  ψ : V ⟶ U
  /-- `ψ` is proper. -/
  isProper_ψ : IsProper ψ
  /-- The embedded copy of `O` inside `V`. -/
  υ : O.toScheme ⟶ V
  /-- `ψ` extends the inclusion of `O` into `U`. -/
  υ_ψ : υ ≫ ψ = O.ι
  /-- Over `O`, the extension `ψ` is an isomorphism. -/
  isIso_ψ_restrict : IsIso (ψ ∣_ O)
  /-- The ambient proper model, as a compactification of `V ⟶ U ⟶ S`. -/
  X : Compactification (ψ ≫ u)
  /-- The embedded copy of `O` is dense in the ambient model. -/
  isSchemeTheoreticallyDominant_emb : IsSchemeTheoreticallyDominant (υ ≫ X.i)

namespace CompactifiedProperExtension

attribute [instance] isProper_ψ isIso_ψ_restrict isSchemeTheoreticallyDominant_emb

variable {u : U ⟶ S} {O : U.Opens} (σ : CompactifiedProperExtension u O)

/-- Over the range of `O.ι`, the extension `ψ` is an isomorphism. -/
lemma isIso_ψ_restrict_opensRange : IsIso (σ.ψ ∣_ O.ι.opensRange) := by
  rw [Scheme.Opens.opensRange_ι]
  infer_instance

/-- **The embedded copy of `O` is an open immersion**: it is a lift of the open immersion
`O.ι` along `ψ`, which is an isomorphism over `O`. -/
instance isOpenImmersion_υ : IsOpenImmersion σ.υ :=
  have := σ.isIso_ψ_restrict_opensRange
  isOpenImmersion_of_comp_eq σ.ψ σ.υ σ.υ_ψ

/-- The embedded copy of `O` is exactly the part of `V` lying over `O`. -/
lemma range_υ : Set.range σ.υ = σ.ψ ⁻¹' (O : Set U) := by
  have := σ.isIso_ψ_restrict_opensRange
  rw [range_eq_preimage_range_of_comp_eq σ.ψ σ.υ σ.υ_ψ, Scheme.Opens.range_ι]

/-- The ambient model over a Noetherian base is Noetherian. -/
lemma isNoetherian_Z [IsNoetherian S] : IsNoetherian σ.X.Z :=
  isNoetherian_of_isProper σ.X.g

section Boundary

/-- The **self boundary** of a side, relative to the other open `O'`: the closure in the
ambient scheme of the inverse image under `ψ` of the closed complement `U ∖ O'`.
(Blueprint: `Z̄_{i,i}` of `def:nagata-two-open-boundary-loci`.) -/
def selfBoundary (O' : U.Opens) : Set σ.X.Z := closure (σ.X.i '' (σ.ψ ⁻¹' ((O' : Set U)ᶜ)))

/-- The **forbidden boundary** of a side: the closure in the ambient scheme of the
inverse image under `ψ` of the closed complement `U ∖ O` of its own open. Removing it
yields the intermediate locus `Xᵢ°` of the blueprint.
(Blueprint: `Z̄_{i,j}` of `def:nagata-two-open-boundary-loci`.) -/
def forbiddenBoundary : Set σ.X.Z := closure (σ.X.i '' (σ.ψ ⁻¹' ((O : Set U)ᶜ)))

/-- A side is **prepared** relative to the other open `O'` if its two boundary closures
are disjoint. (Blueprint: `def:nagata-two-open-prepared-boundaries`.) -/
def Prepared (O' : U.Opens) : Prop := Disjoint (σ.selfBoundary O') σ.forbiddenBoundary

/-- The embedded copy of `O` avoids the forbidden boundary. -/
lemma disjoint_range_υ_comp_i_forbiddenBoundary :
    Disjoint (Set.range (σ.υ ≫ σ.X.i)) σ.forbiddenBoundary := by
  refine Disjoint.closure_right ?_ (σ.υ ≫ σ.X.i).isOpenEmbedding.isOpen_range
  have hrange : Set.range (σ.υ ≫ σ.X.i) = σ.X.i '' Set.range σ.υ := by
    simp [Set.range_comp]
  rw [hrange, Set.disjoint_image_iff σ.X.i.isOpenEmbedding.injective, σ.range_υ]
  exact Set.disjoint_left.mpr fun x hx hx' ↦ hx' hx

/-- The complement of the forbidden boundary, i.e. the locus `Xᵢ°` of the blueprint.
(Blueprint: `def:nagata-two-open-intermediate-schemes`.) -/
def interiorLocus : σ.X.Z.Opens := ⟨σ.forbiddenBoundaryᶜ, isClosed_closure.isOpen_compl⟩

/-- The embedded copy of `O` lies in the complement of the forbidden boundary. -/
lemma range_υ_comp_i_subset_interiorLocus :
    Set.range (σ.υ ≫ σ.X.i) ⊆ (σ.interiorLocus : Set σ.X.Z) :=
  σ.disjoint_range_υ_comp_i_forbiddenBoundary.subset_compl_right

/-- The embedded copy of `O` inside the complement of the forbidden boundary. -/
def interiorLocusEmb : O.toScheme ⟶ σ.interiorLocus.toScheme :=
  IsOpenImmersion.lift σ.interiorLocus.ι (σ.υ ≫ σ.X.i) <| by
    rw [Scheme.Opens.range_ι]
    exact σ.range_υ_comp_i_subset_interiorLocus

@[reassoc (attr := simp)]
lemma interiorLocusEmb_ι : σ.interiorLocusEmb ≫ σ.interiorLocus.ι = σ.υ ≫ σ.X.i :=
  IsOpenImmersion.lift_fac _ _ _

instance : IsOpenImmersion σ.interiorLocusEmb := by
  rw [interiorLocusEmb]
  infer_instance

end Boundary

section AdmissibleBlowup

attribute [local instance] IsAdmissible.isProper_blowupMap IsAdmissible.isIso_blowupMap_restrict

variable [IsNoetherian S] (B : IsAdmissible σ.X.Z σ.X.i.opensRange)

/-- **Transport of a compactified proper extension along a `V`-admissible blow-up** of the
ambient scheme (blueprint: `def:nagata-two-open-side-transport`).

```
        i'
   V ───────→ Bl_I X.Z       b : Bl_I X.Z ⟶ X.Z the V-admissible blow-up,
    ╲         │              an isomorphism over the copy of V
 X.i ╲        │ b
      ↘       ↓
             X.Z
```

The proper extension `ψ : V ⟶ U` and the embedded copy of `O` are unchanged; only the ambient
compactification is replaced by the blow-up, into which `V` maps by the lift `i'` of `X.i`
along `b` (`AlgebraicGeometry.liftOfIsIsoRestrict`). Scheme-theoretic density transports
because the preimage of a scheme-theoretically dense open contained in the copy of `V` stays
scheme-theoretically dense
(`AlgebraicGeometry.IsSchemeTheoreticallyDominant.preimage_ι_of_le`). -/
def admissibleBlowup : CompactifiedProperExtension u O where
  V := σ.V
  ψ := σ.ψ
  isProper_ψ := σ.isProper_ψ
  υ := σ.υ
  υ_ψ := σ.υ_ψ
  isIso_ψ_restrict := σ.isIso_ψ_restrict
  X :=
    { Z := B.I.blowup
      g := B.I.blowupMap ≫ σ.X.g
      i := liftOfIsIsoRestrict B.I.blowupMap σ.X.i
      comm := by rw [← Category.assoc, liftOfIsIsoRestrict_comp]; exact σ.X.comm
      isProper := inferInstance
      isOpenImmersion := inferInstance }
  isSchemeTheoreticallyDominant_emb := by
    have := σ.isNoetherian_Z
    -- the open range of the embedded copy of `O`, an open of `X.Z` contained in the copy of `V`
    have hle : (σ.υ ≫ σ.X.i).opensRange ≤ σ.X.i.opensRange := by
      rintro - ⟨o, rfl⟩
      exact ⟨σ.υ o, (Scheme.Hom.comp_apply _ _ _).symm⟩
    have : IsIso (B.I.blowupMap ∣_ (σ.υ ≫ σ.X.i).opensRange) :=
      isIso_morphismRestrict_of_le B.I.blowupMap hle B.isIso_blowupMap_restrict
    have : IsSchemeTheoreticallyDominant (σ.υ ≫ σ.X.i).opensRange.ι :=
      (isSchemeTheoreticallyDominant_iff_opensRange_ι (σ.υ ≫ σ.X.i)).mp inferInstance
    have : IsSchemeTheoreticallyDominant (B.I.blowupMap ⁻¹ᵁ B.preservedOpen).ι :=
      B.I.isSchemeTheoreticallyDominant_blowupMap_preimage_compl_support
    have hpre : IsSchemeTheoreticallyDominant
        (B.I.blowupMap ⁻¹ᵁ (σ.υ ≫ σ.X.i).opensRange).ι :=
      .preimage_ι_of_le B.I.blowupMap (hle.trans B.le_preservedOpen)
        B.I.isIso_blowupMap_restrict_support_compl
    -- the transported copy of `O` has open range the preimage of that open
    have hq : (σ.υ ≫ liftOfIsIsoRestrict B.I.blowupMap σ.X.i) ≫ B.I.blowupMap =
        σ.υ ≫ σ.X.i := by
      rw [Category.assoc, liftOfIsIsoRestrict_comp]
    refine (isSchemeTheoreticallyDominant_iff_opensRange_ι
      (σ.υ ≫ liftOfIsIsoRestrict B.I.blowupMap σ.X.i)).mpr ?_
    rwa [opensRange_eq_preimage_of_comp_eq B.I.blowupMap _ hq]

/-- **Boundary loci transport along an admissible blow-up to their full preimages.** -/
lemma admissibleBlowup_image_preimage (A : Set U) :
    (σ.admissibleBlowup B).X.i '' ((σ.admissibleBlowup B).ψ ⁻¹' A) =
      B.I.blowupMap ⁻¹' (σ.X.i '' (σ.ψ ⁻¹' A)) :=
  image_eq_preimage_image_of_comp_eq B.I.blowupMap _ (liftOfIsIsoRestrict_comp _ _) _

/-- The self boundary of a transported side is the closure of the preimage of the self
boundary locus of the original side. -/
lemma admissibleBlowup_selfBoundary (O' : U.Opens) :
    (σ.admissibleBlowup B).selfBoundary O' =
      closure (B.I.blowupMap ⁻¹' (σ.X.i '' (σ.ψ ⁻¹' ((O' : Set U)ᶜ)))) :=
  congrArg closure (σ.admissibleBlowup_image_preimage B _)

/-- The forbidden boundary of a transported side is the closure of the preimage of the
forbidden boundary locus of the original side. -/
lemma admissibleBlowup_forbiddenBoundary :
    (σ.admissibleBlowup B).forbiddenBoundary =
      closure (B.I.blowupMap ⁻¹' (σ.X.i '' (σ.ψ ⁻¹' ((O : Set U)ᶜ)))) :=
  congrArg closure (σ.admissibleBlowup_image_preimage B _)

/-- **Preparedness persists along admissible blow-ups**: the transported boundary
closures are the closures of the preimages of the original ones, so disjointness is
preserved. (Blueprint: `lemma:nagata-two-open-side-transport-prepared`.) -/
lemma Prepared.admissibleBlowup {σ : CompactifiedProperExtension u O}
    (B : IsAdmissible σ.X.Z σ.X.i.opensRange) {O' : U.Opens} (hσ : σ.Prepared O') :
    (σ.admissibleBlowup B).Prepared O' := by
  rw [Prepared, σ.admissibleBlowup_selfBoundary B O', σ.admissibleBlowup_forbiddenBoundary]
  exact hσ.closure_preimage B.I.blowupMap.continuous

end AdmissibleBlowup

end CompactifiedProperExtension

end AlgebraicGeometry
