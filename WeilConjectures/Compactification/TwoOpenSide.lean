/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import WeilConjectures.Blowup.Density
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Proper
public import WeilConjectures.Mathlib.AlgebraicGeometry.Restrict
public import WeilConjectures.Mathlib.Topology.Continuous

/-!

# Transport of a side of the two-open construction along an admissible blow-up

The structure `AlgebraicGeometry.TwoOpenSide u O` records one *side* of the two-open
compactification theorem for a morphism `u : U ⟶ S` and an open `O` of `U`: a proper
ambient scheme `X ⟶ S`, an open `V ⊆ X` with a proper morphism `ψ : V ⟶ U` extending
the inclusion of an embedded copy of `O`, that copy being scheme-theoretically dense
in `X` (blueprint: `def:nagata-two-open-graph-extensions`, the density condition being
that of `lemma:nagata-two-open-dense-compactifications`).

The other open `O'` of the two-open construction enters only through the boundary loci,
so it is a parameter of those and not of the structure itself
(blueprint: `def:nagata-two-open-boundary-loci`):

* `TwoOpenSide.selfBoundary O'` — the closure in `X` of `ψ ⁻¹ (U ∖ O')`;
* `TwoOpenSide.forbiddenBoundary` — the closure in `X` of `ψ ⁻¹ (U ∖ O)`.

The predicate `TwoOpenSide.Prepared O'` states that the two boundary closures are
disjoint (blueprint: `def:nagata-two-open-prepared-boundaries`). The complement of the
forbidden boundary is the open `TwoOpenSide.interiorLocus` (the `Xᵢ°` of
`def:nagata-two-open-intermediate-schemes`), which contains the embedded copy of `O`
(`TwoOpenSide.interiorLocusEmb`).

The main results are `TwoOpenSide.admissibleBlowup`, transporting a side along a
`V`-admissible blow-up of the ambient scheme, and `TwoOpenSide.Prepared.admissibleBlowup`,
saying that preparedness persists: boundary loci transport to preimages
(`TwoOpenSide.admissibleBlowup_image_preimage`), so disjointness is preserved
(blueprint: `def:nagata-two-open-side-transport`,
`lemma:nagata-two-open-side-transport-prepared`).

-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory

namespace AlgebraicGeometry

variable {U S : Scheme.{u}}

/-- The data of one **side of the two-open compactification theorem** for a morphism
`u : U ⟶ S` and an open `O` of `U` (blueprint: `def:nagata-two-open-graph-extensions`,
with the density condition of `lemma:nagata-two-open-dense-compactifications`).

```
   O ───υ──→ V              V ───ψ──→ U
    ╲        │              │         │
 O.ι ╲       │ ψ        V.ι │         │ u
      ↘      ↓              ↓         ↓
             U              X ───s──→ S
```

The second open of the two-open construction plays no role in this data; it enters only
as a parameter of the boundary loci `TwoOpenSide.selfBoundary` and of the preparedness
predicate `TwoOpenSide.Prepared`. -/
structure TwoOpenSide (u : U ⟶ S) (O : U.Opens) where
  /-- The proper ambient model. -/
  X : Scheme.{u}
  /-- The structure morphism of the ambient model. -/
  s : X ⟶ S
  /-- The ambient model is proper over `S`. -/
  isProper_s : IsProper s
  /-- The open on which the proper extension of the inclusion of `O` is defined. -/
  V : X.Opens
  /-- The proper extension `ψ : V ⟶ U` of the inclusion of `O`. -/
  ψ : V.toScheme ⟶ U
  /-- The extension `ψ` is proper. -/
  isProper_ψ : IsProper ψ
  /-- `ψ` is a morphism over `S`, for the structure morphism `s` of the ambient model. -/
  comm_s : ψ ≫ u = V.ι ≫ s
  /-- The embedded copy of `O` inside `V`. -/
  υ : O.toScheme ⟶ V.toScheme
  /-- The embedding of `O` into `V` is compatible with `ψ`, i.e. `ψ` extends the inclusion
  of `O` into `U`. -/
  comm_ι : υ ≫ ψ = O.ι
  /-- Over `O`, the extension `ψ` is an isomorphism. -/
  isIso_ψ_restrict : IsIso (ψ ∣_ O)
  /-- The embedded copy of `O` is scheme-theoretically dense in the ambient model. -/
  isSchemeTheoreticallyDominant_emb : IsSchemeTheoreticallyDominant (υ ≫ V.ι)

namespace TwoOpenSide

attribute [instance] isProper_s isProper_ψ isIso_ψ_restrict isSchemeTheoreticallyDominant_emb

variable {u : U ⟶ S} {O : U.Opens} (σ : TwoOpenSide u O)

/-- Over the range of `O.ι`, the extension `ψ` is an isomorphism. -/
lemma isIso_ψ_restrict_opensRange : IsIso (σ.ψ ∣_ O.ι.opensRange) := by
  rw [Scheme.Opens.opensRange_ι]
  infer_instance

/-- **The embedded copy of `O` is an open immersion**: it is a lift of the open immersion
`O.ι` along `ψ`, which is an isomorphism over `O`. -/
instance isOpenImmersion_υ : IsOpenImmersion σ.υ :=
  have := σ.isIso_ψ_restrict_opensRange
  isOpenImmersion_of_comp_eq σ.υ σ.ψ σ.comm_ι

/-- The embedded copy of `O` is exactly the part of `V` lying over `O`. -/
lemma range_υ : Set.range σ.υ = σ.ψ ⁻¹' (O : Set U) := by
  have := σ.isIso_ψ_restrict_opensRange
  rw [range_eq_preimage_range_of_comp_eq σ.υ σ.ψ σ.comm_ι, Scheme.Opens.range_ι]

/-- The embedded copy of `O` in the ambient scheme. -/
def embX : O.toScheme ⟶ σ.X := σ.υ ≫ σ.V.ι

instance : IsOpenImmersion σ.embX :=
  inferInstanceAs (IsOpenImmersion (σ.υ ≫ σ.V.ι))

instance : IsSchemeTheoreticallyDominant σ.embX :=
  inferInstanceAs (IsSchemeTheoreticallyDominant (σ.υ ≫ σ.V.ι))

/-- The ambient model of a side over a Noetherian base is Noetherian. -/
lemma isNoetherian_X [IsNoetherian S] : IsNoetherian σ.X :=
  isNoetherian_of_isProper σ.s

section Boundary

/-- The **self boundary** of a side, relative to the other open `O'`: the closure in the
ambient scheme of the inverse image under `ψ` of the closed complement `U ∖ O'`.
(Blueprint: `Z̄_{i,i}` of `def:nagata-two-open-boundary-loci`.) -/
def selfBoundary (O' : U.Opens) : Set σ.X := closure (σ.V.ι '' (σ.ψ ⁻¹' ((O' : Set U)ᶜ)))

/-- The **forbidden boundary** of a side: the closure in the ambient scheme of the
inverse image under `ψ` of the closed complement `U ∖ O` of its own open. Removing it
yields the intermediate locus `Xᵢ°` of the blueprint.
(Blueprint: `Z̄_{i,j}` of `def:nagata-two-open-boundary-loci`.) -/
def forbiddenBoundary : Set σ.X := closure (σ.V.ι '' (σ.ψ ⁻¹' ((O : Set U)ᶜ)))

/-- A side is **prepared** relative to the other open `O'` if its two boundary closures
are disjoint. (Blueprint: `def:nagata-two-open-prepared-boundaries`.) -/
def Prepared (O' : U.Opens) : Prop := Disjoint (σ.selfBoundary O') σ.forbiddenBoundary

/-- The embedded copy of `O` avoids the forbidden boundary. -/
lemma disjoint_range_embX_forbiddenBoundary :
    Disjoint (Set.range σ.embX) σ.forbiddenBoundary := by
  refine Disjoint.closure_right ?_ σ.embX.isOpenEmbedding.isOpen_range
  have hrange : Set.range σ.embX = σ.V.ι '' Set.range σ.υ := by
    simp [embX, Set.range_comp]
  rw [hrange, Set.disjoint_image_iff σ.V.ι.isOpenEmbedding.injective, σ.range_υ]
  exact Set.disjoint_left.mpr fun x hx hx' ↦ hx' hx

/-- The complement of the forbidden boundary, i.e. the locus `Xᵢ°` of the blueprint.
(Blueprint: `def:nagata-two-open-intermediate-schemes`.) -/
def interiorLocus : σ.X.Opens := ⟨σ.forbiddenBoundaryᶜ, isClosed_closure.isOpen_compl⟩

/-- The embedded copy of `O` lies in the complement of the forbidden boundary. -/
lemma range_embX_subset_interiorLocus : Set.range σ.embX ⊆ (σ.interiorLocus : Set σ.X) :=
  σ.disjoint_range_embX_forbiddenBoundary.subset_compl_right

/-- The embedded copy of `O` inside the complement of the forbidden boundary. -/
def interiorLocusEmb : O.toScheme ⟶ σ.interiorLocus.toScheme :=
  IsOpenImmersion.lift σ.interiorLocus.ι σ.embX <| by
    rw [Scheme.Opens.range_ι]
    exact σ.range_embX_subset_interiorLocus

@[reassoc (attr := simp)]
lemma interiorLocusEmb_ι : σ.interiorLocusEmb ≫ σ.interiorLocus.ι = σ.embX :=
  IsOpenImmersion.lift_fac _ _ _

instance : IsOpenImmersion σ.interiorLocusEmb := by
  rw [interiorLocusEmb]
  infer_instance

end Boundary

section AdmissibleBlowup

attribute [local instance] IsAdmissible.isProper_blowupMap IsAdmissible.isIso_blowupMap_restrict

variable [IsNoetherian S] (B : IsAdmissible σ.X σ.V)

/-- **Transport of a side along a `V`-admissible blow-up** of the ambient scheme
(blueprint: `def:nagata-two-open-side-transport`).

```
        b ∣_ V
   b⁻¹V ──────→ V ⊆ X       b : Bl_I X ⟶ X the V-admissible blow-up,
     ╲          │           an isomorphism over V
   ψ' ╲         │ ψ
       ↘        ↓
                U
```

The open `V`, the proper extension `ψ` and the embedded copy of `O` transport along the
isomorphism over `V`; scheme-theoretic density transports because the preimage of a
scheme-theoretically dense open contained in `V` stays scheme-theoretically dense
(`AlgebraicGeometry.IsSchemeTheoreticallyDominant.preimage_ι_of_le`). -/
def admissibleBlowup : TwoOpenSide u O where
  X := B.I.blowup
  s := B.I.blowupMap ≫ σ.s
  isProper_s := inferInstance
  V := B.I.blowupMap ⁻¹ᵁ σ.V
  ψ := (B.I.blowupMap ∣_ σ.V) ≫ σ.ψ
  isProper_ψ := by
    rw [MorphismProperty.cancel_left_of_respectsIso (P := @IsProper)]
    exact σ.isProper_ψ
  comm_s := by
    rw [Category.assoc, σ.comm_s, morphismRestrict_ι_assoc]
  υ := σ.υ ≫ inv (B.I.blowupMap ∣_ σ.V)
  comm_ι := by
    rw [Category.assoc, IsIso.inv_hom_id_assoc, σ.comm_ι]
  isIso_ψ_restrict := by
    have h : IsIso ((B.I.blowupMap ∣_ σ.V) ∣_ (σ.ψ ⁻¹ᵁ O) ≫ σ.ψ ∣_ O) := inferInstance
    rwa [← morphismRestrict_comp] at h
  isSchemeTheoreticallyDominant_emb := by
    have hX := σ.isNoetherian_X
    -- the open range of the embedded copy of `O`, an open of `X` contained in `V`
    have hle : σ.embX.opensRange ≤ σ.V := by
      rintro - ⟨o, rfl⟩
      change σ.embX o ∈ σ.V
      rw [show σ.embX o = σ.V.ι (σ.υ o) from Scheme.Hom.comp_apply _ _ _]
      exact (σ.υ o).2
    have : IsIso (B.I.blowupMap ∣_ σ.embX.opensRange) :=
      isIso_morphismRestrict_of_le B.I.blowupMap hle B.isIso_blowupMap_restrict
    have : IsSchemeTheoreticallyDominant σ.embX.opensRange.ι :=
      (isSchemeTheoreticallyDominant_iff_opensRange_ι σ.embX).mp inferInstance
    have : IsSchemeTheoreticallyDominant
        (B.I.blowupMap ⁻¹ᵁ B.preservedOpen).ι :=
      B.I.isSchemeTheoreticallyDominant_blowupMap_preimage_compl_support
    have hpre : IsSchemeTheoreticallyDominant (B.I.blowupMap ⁻¹ᵁ σ.embX.opensRange).ι :=
      .preimage_ι_of_le B.I.blowupMap (hle.trans B.le_preservedOpen)
        B.I.isIso_blowupMap_restrict_support_compl
    -- the transported copy of `O` has open range the preimage of that open
    have hq : ((σ.υ ≫ inv (B.I.blowupMap ∣_ σ.V)) ≫ (B.I.blowupMap ⁻¹ᵁ σ.V).ι) ≫
        B.I.blowupMap = σ.embX := by
      rw [embX, Category.assoc, Category.assoc, ← morphismRestrict_ι, IsIso.inv_hom_id_assoc]
    rw [isSchemeTheoreticallyDominant_iff_opensRange_ι,
      opensRange_eq_preimage_of_comp_eq _ B.I.blowupMap hq]
    exact hpre

/-- **Boundary loci transport along an admissible blow-up to their full preimages.** -/
lemma admissibleBlowup_image_preimage (A : Set U) :
    (σ.admissibleBlowup B).V.ι '' ((σ.admissibleBlowup B).ψ ⁻¹' A) =
      B.I.blowupMap ⁻¹' (σ.V.ι '' (σ.ψ ⁻¹' A)) := by
  change (B.I.blowupMap ⁻¹ᵁ σ.V).ι '' (((B.I.blowupMap ∣_ σ.V) ≫ σ.ψ) ⁻¹' A) = _
  rw [show ⇑((B.I.blowupMap ∣_ σ.V) ≫ σ.ψ) = ⇑σ.ψ ∘ ⇑(B.I.blowupMap ∣_ σ.V) from rfl,
    Set.preimage_comp, image_preimage_morphismRestrict]

/-- The self boundary of a transported side is the closure of the preimage of the self
boundary locus of the original side. -/
lemma admissibleBlowup_selfBoundary (O' : U.Opens) :
    (σ.admissibleBlowup B).selfBoundary O' =
      closure (B.I.blowupMap ⁻¹' (σ.V.ι '' (σ.ψ ⁻¹' ((O' : Set U)ᶜ)))) :=
  congrArg closure (σ.admissibleBlowup_image_preimage B _)

/-- The forbidden boundary of a transported side is the closure of the preimage of the
forbidden boundary locus of the original side. -/
lemma admissibleBlowup_forbiddenBoundary :
    (σ.admissibleBlowup B).forbiddenBoundary =
      closure (B.I.blowupMap ⁻¹' (σ.V.ι '' (σ.ψ ⁻¹' ((O : Set U)ᶜ)))) :=
  congrArg closure (σ.admissibleBlowup_image_preimage B _)

/-- **Preparedness persists along admissible blow-ups**: the transported boundary
closures are the closures of the preimages of the original ones, so disjointness is
preserved. (Blueprint: `lemma:nagata-two-open-side-transport-prepared`.) -/
lemma Prepared.admissibleBlowup {σ : TwoOpenSide u O} (B : IsAdmissible σ.X σ.V)
    {O' : U.Opens} (hσ : σ.Prepared O') : (σ.admissibleBlowup B).Prepared O' := by
  rw [Prepared, σ.admissibleBlowup_selfBoundary B O', σ.admissibleBlowup_forbiddenBoundary]
  exact hσ.closure_preimage B.I.blowupMap.continuous

end AdmissibleBlowup

end TwoOpenSide

end AlgebraicGeometry
