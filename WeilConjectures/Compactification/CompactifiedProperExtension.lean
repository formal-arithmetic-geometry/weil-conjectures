/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import WeilConjectures.Blowup.Density
public import WeilConjectures.Compactification.AdmissibleBlowup
public import WeilConjectures.Mathlib.AlgebraicGeometry.Restrict
public import WeilConjectures.Mathlib.Topology.Continuous

/-!

# Compactified proper extensions and their transport along an admissible blow-up

The structure `AlgebraicGeometry.CompactifiedProperExtension u O` records, for a morphism
`u : U ⟶ S` and an open `O` of `U`, a proper extension `ψ : V ⟶ U` of the inclusion of `O`
which is an isomorphism over `O`, together with a compactification of `V` over `S` in which
the copy of `O` is scheme-theoretically dominant:

```
   O ──υ──→ V ──ψ──→ U          υ ≫ ψ = O.ι
            │        │          i ≫ g = ψ ≫ u
          i │        │ u
            ↓        ↓
            Z ──g──→ S
```

Here `Z`, `g` and `i` are the data of the field `compactification`, and the embedded copy `υ`
of `O` is not part of the data: it is the unique lift of `O.ι` through `ψ`.

This is the data attached to one of the two opens in the two-open step of Nagata's
compactification theorem: in the notation of [Conrad][ConradNagata], the diagram
`U ⊆ V_i ⊆ X_i` set up in §3 before Lemma 3.2. The second open enters only through the
boundary loci, so it is a parameter of those and not of the structure itself.

## Main definitions

* `CompactifiedProperExtension`: the data above (blueprint:
  `def:nagata-two-open-graph-extensions`, with the density condition of
  `lemma:nagata-two-open-dense-compactifications`);
* `CompactifiedProperExtension.υ`: the embedded copy of `O` in `V`;
* `CompactifiedProperExtension.boundary O'`: the boundary relative to an open `O'` of `U`,
  i.e. the closure in `Z` of the part of `V` lying over `U ∖ O'` (blueprint: `Z̄_{i,k}` of
  `def:nagata-two-open-boundary-loci`). The blueprint's *self* boundary is `boundary O'` and
  its *forbidden* boundary is `boundary O`;
* `CompactifiedProperExtension.Prepared O'`: the two boundaries are disjoint (blueprint:
  `def:nagata-two-open-prepared-boundaries`);
* `CompactifiedProperExtension.interiorLocus`: the complement of the boundary relative to
  `O`, the `Xᵢ°` of `def:nagata-two-open-intermediate-schemes`;
* `CompactifiedProperExtension.admissibleBlowup`: the transport along a blow-up of the
  ambient scheme admissible for the copy of `V` (blueprint:
  `def:nagata-two-open-side-transport`). In [Conrad][ConradNagata] this is the passage
  "replace each `X_i` by a `V_i`-admissible blow-up" of the paragraph preceding Lemma 3.2.

## Main results

* `CompactifiedProperExtension.isSchemeTheoreticallyDominant_υ_comp_admissibleBlowup_i`: the
  copy of `O` stays scheme-theoretically dense after the transport, which is what makes the
  transport well defined (blueprint: `lemma:nagata-two-open-side-transport`);
* `CompactifiedProperExtension.Prepared.admissibleBlowup`: preparedness persists along the
  transport, the boundary loci transporting to their full inverse images
  (`CompactifiedProperExtension.admissibleBlowup_boundaryLocus`) (blueprint:
  `lemma:nagata-two-open-side-transport-prepared`).

## References

* [B. Conrad, *Deligne's notes on Nagata compactifications*][ConradNagata],
  J. Ramanujan Math. Soc. **22** (2007), 205–257,
  <https://math.stanford.edu/~conrad/papers/nagatafinal.pdf>. The relevant part is §3: the
  data recorded here is the diagram `U ⊆ V_i ⊆ X_i` set up before Lemma 3.2, and the transport
  below is the observation, in the paragraph preceding that lemma, that the hypotheses are
  preserved after replacing each `X_i` by a `V_i`-admissible blow-up.

-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory

namespace AlgebraicGeometry

variable {U S : Scheme.{u}}

/-- A **compactified proper extension** of an open `O` of `U` along `u : U ⟶ S`: a proper
extension `ψ : V ⟶ U` of the inclusion of `O`, which is an isomorphism over `O`, together
with a compactification of `V` over `S` in which the copy `υ` of `O` is scheme-theoretically
dominant (blueprint: `def:nagata-two-open-graph-extensions`, with the density condition of
`lemma:nagata-two-open-dense-compactifications`).

```
   O ──υ──→ V ──ψ──→ U          υ ≫ ψ = O.ι
            │        │          i ≫ g = ψ ≫ u
          i │        │ u
            ↓        ↓
            Z ──g──→ S
```

The copy `υ` of `O` is determined by the other fields: it is the unique lift of `O.ι` through
`ψ` (`AlgebraicGeometry.CompactifiedProperExtension.υ`).

In the two-open construction, the second open plays no role in this data; it enters only as a
parameter of the boundary `AlgebraicGeometry.CompactifiedProperExtension.boundary` and of the
preparedness predicate `AlgebraicGeometry.CompactifiedProperExtension.Prepared`. -/
structure CompactifiedProperExtension (u : U ⟶ S) (O : U.Opens) where
  /-- The proper extension of `O` over `U`. -/
  V : Scheme.{u}
  /-- The structure morphism of `V` over `U`. -/
  ψ : V ⟶ U
  /-- `ψ` is proper. -/
  [isProper_ψ : IsProper ψ]
  /-- Over `O`, the extension `ψ` is an isomorphism. -/
  [isIso_ψ_restrict : IsIso (ψ ∣_ O)]
  /-- The ambient proper model, as a compactification of `V ⟶ U ⟶ S`. -/
  compactification : Compactification (ψ ≫ u)
  /-- The embedded copy of `O` is dense in the ambient model. -/
  isSchemeTheoreticallyDominant_υ_comp_i :
    IsSchemeTheoreticallyDominant (liftOfIsIsoRestrict ψ O.ι ≫ compactification.i)

namespace CompactifiedProperExtension

attribute [instance] isProper_ψ isIso_ψ_restrict

variable {u : U ⟶ S} {O : U.Opens} (σ : CompactifiedProperExtension u O)

/-- **The embedded copy of `O` inside `V`**: since `ψ` is an isomorphism over `O`, the
inclusion `O.ι` lifts through `ψ` (`AlgebraicGeometry.liftOfIsIsoRestrict`), and it is the
only morphism `O.toScheme ⟶ V` over `O.ι` (`AlgebraicGeometry.eq_liftOfIsIsoRestrict`). -/
def υ : O.toScheme ⟶ σ.V := liftOfIsIsoRestrict σ.ψ O.ι

instance isOpenImmersion_υ : IsOpenImmersion σ.υ :=
  isOpenImmersion_liftOfIsIsoRestrict _ _

/-- `ψ` extends the inclusion of `O` into `U`. -/
@[reassoc (attr := simp)]
lemma υ_ψ : σ.υ ≫ σ.ψ = O.ι :=
  liftOfIsIsoRestrict_comp _ _

/-- The embedded copy of `O` is exactly the part of `V` lying over `O`. -/
lemma range_υ : Set.range σ.υ = σ.ψ ⁻¹' (O : Set U) := by
  rw [range_eq_preimage_range_of_comp_eq σ.ψ σ.υ σ.υ_ψ, Scheme.Opens.range_ι]

section Boundary

/-- The **boundary locus** of a compactified proper extension, relative to an open `O'` of
`U`: the image in the ambient scheme of the part of `V` lying over the closed complement
`U ∖ O'`. (Blueprint: `Z_{i,k}` of `def:nagata-two-open-boundary-loci`.) -/
def boundaryLocus (O' : U.Opens) : Set σ.compactification.Z :=
  σ.compactification.i '' (σ.ψ ⁻¹' ((O' : Set U)ᶜ))

lemma boundaryLocus_eq_image (O' : U.Opens) :
    σ.boundaryLocus O' = σ.compactification.i '' (σ.ψ ⁻¹' ((O' : Set U)ᶜ)) := rfl

/-- The **boundary** of a compactified proper extension, relative to an open `O'` of `U`: the
closure of the boundary locus. For `O' = O` this is the *forbidden* boundary, whose complement
is the interior locus `AlgebraicGeometry.CompactifiedProperExtension.interiorLocus`; for the
other open of the two-open construction it is the *self* boundary.
(Blueprint: `Z̄_{i,k}` of `def:nagata-two-open-boundary-loci`.) -/
def boundary (O' : U.Opens) : Set σ.compactification.Z := closure (σ.boundaryLocus O')

/-- The boundary is closed, being a closure. -/
lemma isClosed_boundary (O' : U.Opens) : IsClosed (σ.boundary O') := isClosed_closure

/-- A compactified proper extension is **prepared** relative to another open `O'` if its
boundary relative to `O'` and its boundary relative to its own open `O` are disjoint.
(Blueprint: `def:nagata-two-open-prepared-boundaries`.) -/
def Prepared (O' : U.Opens) : Prop := Disjoint (σ.boundary O') (σ.boundary O)

/-- Preparedness spelled out, to avoid rewriting with the definition. -/
lemma prepared_iff (O' : U.Opens) :
    σ.Prepared O' ↔ Disjoint (σ.boundary O') (σ.boundary O) := Iff.rfl

/-- The embedded copy of `O` avoids the boundary relative to `O`. -/
lemma disjoint_range_υ_comp_i_boundary :
    Disjoint (Set.range (σ.υ ≫ σ.compactification.i)) (σ.boundary O) := by
  refine Disjoint.closure_right ?_ (σ.υ ≫ σ.compactification.i).isOpenEmbedding.isOpen_range
  have hrange : Set.range (σ.υ ≫ σ.compactification.i) =
      σ.compactification.i '' Set.range σ.υ := by
    simp [Set.range_comp]
  rw [hrange, σ.boundaryLocus_eq_image,
    Set.disjoint_image_iff σ.compactification.i.isOpenEmbedding.injective, σ.range_υ]
  exact disjoint_compl_right.preimage _

/-- The complement of the boundary relative to `O`, i.e. the locus `Xᵢ°` of the blueprint.
(Blueprint: `def:nagata-two-open-intermediate-schemes`.) -/
def interiorLocus : σ.compactification.Z.Opens :=
  ⟨(σ.boundary O)ᶜ, (σ.isClosed_boundary O).isOpen_compl⟩

@[simp]
lemma coe_interiorLocus : (σ.interiorLocus : Set σ.compactification.Z) = (σ.boundary O)ᶜ := rfl

/-- The embedded copy of `O` lies in the interior locus. -/
lemma range_υ_comp_i_subset_interiorLocus :
    Set.range (σ.υ ≫ σ.compactification.i) ⊆ (σ.interiorLocus : Set σ.compactification.Z) :=
  σ.disjoint_range_υ_comp_i_boundary.subset_compl_right

/-- The embedded copy of `O` inside the interior locus. -/
def interiorLocusLift : O.toScheme ⟶ σ.interiorLocus.toScheme :=
  IsOpenImmersion.lift σ.interiorLocus.ι (σ.υ ≫ σ.compactification.i) <| by
    rw [Scheme.Opens.range_ι]
    exact σ.range_υ_comp_i_subset_interiorLocus

@[reassoc (attr := simp)]
lemma interiorLocusLift_ι :
    σ.interiorLocusLift ≫ σ.interiorLocus.ι = σ.υ ≫ σ.compactification.i :=
  IsOpenImmersion.lift_fac _ _ _

instance isOpenImmersion_interiorLocusLift : IsOpenImmersion σ.interiorLocusLift := by
  delta interiorLocusLift
  infer_instance

end Boundary

section AdmissibleBlowup

/-- The copy of `O` in the ambient scheme is contained in the copy of `V`. -/
lemma opensRange_υ_comp_i_le :
    (σ.υ ≫ σ.compactification.i).opensRange ≤ σ.compactification.i.opensRange := by
  rintro - ⟨o, rfl⟩
  exact ⟨σ.υ o, (Scheme.Hom.comp_apply _ _ _).symm⟩

/-- Over a Noetherian base the copy of `O` in the ambient scheme is quasi-compact, the ambient
scheme being Noetherian (`AlgebraicGeometry.Compactification.isNoetherian_Z`). This is how the
quasi-compactness hypothesis of the transport below is met in practice. -/
instance quasiCompact_opensRange_υ_comp_i_ι [IsNoetherian S] :
    QuasiCompact (σ.υ ≫ σ.compactification.i).opensRange.ι := by
  have := σ.compactification.isNoetherian_Z
  infer_instance

variable [QuasiCompact (σ.υ ≫ σ.compactification.i).opensRange.ι]
  (B : IsAdmissible σ.compactification.Z σ.compactification.i.opensRange)

/-- **The copy of `O` stays scheme-theoretically dense after an admissible blow-up** of the
ambient scheme (blueprint: `lemma:nagata-two-open-side-transport`): the copy of `O` is a
scheme-theoretically dense open contained in the copy of `V`, over which the blow-up is an
isomorphism, so its inverse image stays scheme-theoretically dense
(`AlgebraicGeometry.IsAdmissible.isSchemeTheoreticallyDominant_preimage_ι` applied to the
`(υ ≫ i).opensRange`-admissible blow-up `B.mono`); and that inverse image is exactly the
transported copy of `O`. -/
lemma isSchemeTheoreticallyDominant_υ_comp_admissibleBlowup_i :
    IsSchemeTheoreticallyDominant (σ.υ ≫ (σ.compactification.admissibleBlowup B).i) := by
  have hle := σ.opensRange_υ_comp_i_le
  have : IsSchemeTheoreticallyDominant (σ.υ ≫ σ.compactification.i).opensRange.ι :=
    (isSchemeTheoreticallyDominant_iff_opensRange_ι _).mp
      σ.isSchemeTheoreticallyDominant_υ_comp_i
  have : IsIso (B.I.blowupMap ∣_ (σ.υ ≫ σ.compactification.i).opensRange) :=
    (B.mono hle).isIso_blowupMap_restrict
  have : IsSchemeTheoreticallyDominant
      (B.I.blowupMap ⁻¹ᵁ (σ.υ ≫ σ.compactification.i).opensRange).ι :=
    (B.mono hle).isSchemeTheoreticallyDominant_preimage_ι
  refine (isSchemeTheoreticallyDominant_iff_opensRange_ι _).mpr ?_
  rwa [opensRange_eq_preimage_opensRange_of_comp_eq B.I.blowupMap _
    (by rw [Category.assoc, Compactification.admissibleBlowup_i_comp])]

/-- **Transport of a compactified proper extension along an admissible blow-up** of the
ambient scheme (blueprint: `def:nagata-two-open-side-transport`).

The proper extension `ψ : V ⟶ U`, and hence the embedded copy `υ` of `O`, are unchanged; only
the ambient compactification is replaced by its transport along the blow-up
(`AlgebraicGeometry.Compactification.admissibleBlowup`), in which `V` is embedded by the
unique lift of `i` along the blow-up. Scheme-theoretic density of the copy of `O` is preserved
by `isSchemeTheoreticallyDominant_υ_comp_admissibleBlowup_i`. -/
def admissibleBlowup : CompactifiedProperExtension u O where
  V := σ.V
  ψ := σ.ψ
  compactification := σ.compactification.admissibleBlowup B
  isSchemeTheoreticallyDominant_υ_comp_i :=
    σ.isSchemeTheoreticallyDominant_υ_comp_admissibleBlowup_i B

@[simp]
lemma admissibleBlowup_V : (σ.admissibleBlowup B).V = σ.V := rfl

@[simp]
lemma admissibleBlowup_ψ : (σ.admissibleBlowup B).ψ = σ.ψ := rfl

@[simp]
lemma admissibleBlowup_compactification :
    (σ.admissibleBlowup B).compactification = σ.compactification.admissibleBlowup B := rfl

@[simp]
lemma admissibleBlowup_υ : (σ.admissibleBlowup B).υ = σ.υ := rfl

/-- **The boundary loci transport to their full inverse images**: the boundary locus of the
transported extension relative to an open `O'` is the inverse image under the blow-up of the
boundary locus of the original one. -/
lemma admissibleBlowup_boundaryLocus (O' : U.Opens) :
    (σ.admissibleBlowup B).boundaryLocus O' = B.I.blowupMap ⁻¹' σ.boundaryLocus O' :=
  σ.compactification.admissibleBlowup_image_preimage B _

/-- The boundary of a transported extension is the closure of the inverse image of the
boundary locus of the original one. -/
lemma admissibleBlowup_boundary (O' : U.Opens) :
    (σ.admissibleBlowup B).boundary O' = closure (B.I.blowupMap ⁻¹' σ.boundaryLocus O') :=
  congrArg closure (σ.admissibleBlowup_boundaryLocus B O')

/-- **Preparedness persists along admissible blow-ups**: the transported boundaries are the
closures of the inverse images of the original boundary loci, and a continuous map carries the
closure of an inverse image into the inverse image of the closure, so disjointness is
preserved. (Blueprint: `lemma:nagata-two-open-side-transport-prepared`.) -/
lemma Prepared.admissibleBlowup {σ : CompactifiedProperExtension u O}
    [QuasiCompact (σ.υ ≫ σ.compactification.i).opensRange.ι]
    (B : IsAdmissible σ.compactification.Z σ.compactification.i.opensRange) {O' : U.Opens}
    (hσ : σ.Prepared O') : (σ.admissibleBlowup B).Prepared O' := by
  rw [prepared_iff, σ.admissibleBlowup_boundary B O', σ.admissibleBlowup_boundary B O]
  exact hσ.closure_preimage B.I.blowupMap.continuous

end AdmissibleBlowup

end CompactifiedProperExtension

end AlgebraicGeometry
