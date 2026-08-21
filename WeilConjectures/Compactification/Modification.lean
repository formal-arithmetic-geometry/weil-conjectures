/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import WeilConjectures.Blowup.AdmissibleBlowup
public import WeilConjectures.Mathlib.AlgebraicGeometry.Pullbacks
public import WeilConjectures.Compactification.Defs

/-!

# Elimination of indeterminacy, common modifications and graph extension

This file records the modification steps of the proof of Nagata's compactification
theorem, following the blueprint chapter "Nagata compactification", sections
"Boundary preparation" and "Common modifications and graph extension"
(proof order items 30–33):

- `AlgebraicGeometry.exists_admissibleBlowup_strictTransform_open`: **elimination of
  indeterminacy** (Stacks Project Tag 081S; blueprint
  `lemma:nagata-elimination-indeterminacy`): if `q : Z ⟶ X` is separated, of finite
  type and an isomorphism over a quasi-compact open `U` of the qcqs scheme `X`, then
  after a `U`-admissible blow-up the strict transform of `q` is an open immersion;
- `AlgebraicGeometry.Scheme.Hom.schemeTheoreticImage_after_admissibleBlowup`:
  **transport of scheme-theoretic images through admissible blow-ups** (Stacks
  Project Tag 0F3Y; blueprint `lemma:nagata-scheme-image-strict-transform`): the
  scheme-theoretic image of a lift along a `U`-admissible blow-up is the strict
  transform of the scheme-theoretic image;
- `AlgebraicGeometry.CommonModification` and
  `AlgebraicGeometry.exists_commonModification`: **common modification of two models**
  (Stacks Project Tag 0F3X; blueprint `def:nagata-common-modification`,
  `lemma:nagata-common-modification`): two separated finite-type models of a common
  open `U` admit `U`-admissible blow-ups which glue along a common copy of the
  modified `U`-locus to a separated finite-type model;
- `AlgebraicGeometry.Compactification.nonempty_properExtension`: **graph extension**
  (Stacks Project Tag 0F3Z; blueprint `def:nagata-graph-extension`,
  `lemma:nagata-graph-extension`): a compactification of a quasi-compact open
  `V ⊆ U` extends, after a `V`-admissible blow-up of the compactification, to a
  proper morphism `V^gr ⟶ U` restricting to the identity on `V`;
- `AlgebraicGeometry.exists_admissibleBlowup_strictTransform_isIso_near_closure`:
  **isomorphism near a boundary closure** (Stacks Project Tag 0F3W; blueprint
  `def:nagata-isomorphism-near-closure`, `lemma:nagata-isomorphism-near-closure`): a
  proper morphism which is an isomorphism over a neighbourhood of a closed piece `T`
  of `U` acquires, after a `U`-admissible blow-up, a strict transform which is an
  isomorphism over a neighbourhood of the closure of `T`.

The finite-type helper lemmas of the blueprint are already in Mathlib and are not
restated here: `lemma:nagata-proper-to-separated-target` is Mathlib's
`AlgebraicGeometry.IsProper.of_comp`, and the two halves of
`lemma:nagata-finite-type-to-separated-target` (hence also
`lemma:nagata-open-immersion-qc-over-separated-target`) are Mathlib's
`AlgebraicGeometry.locallyOfFiniteType_of_comp` and
`AlgebraicGeometry.QuasiCompact.of_comp` (the latter only needs the second leg
quasi-separated, which separatedness supplies).

## Dependency structure

`exists_admissibleBlowup_strictTransform_open` (Tag 081S) is the only *primitive*
obligation of this file: `schemeTheoreticImage_after_admissibleBlowup` (0F3Y),
`exists_commonModification` (0F3X), `Compactification.nonempty_properExtension` (0F3Z)
and `exists_admissibleBlowup_strictTransform_isIso_near_closure` (0F3W) are all
consumers of it, and the two-open compactification theorem (proof order items 43–48)
consumes those. The Stacks Project proves Tag 081S by Raynaud–Gruson flattening
(Stacks Tags 0815 and 081R), which the revised blueprint deliberately does not
formalize (see the route revision note in
`blueprint/src/version/detailed/nagata/nagata_new_proof_order.md` and the module
docstring of `WeilConjectures.Blowup.AdmissibleBlowup`); the formalized route to
Tag 081S is an open obligation.

-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

/-- **Elimination of indeterminacy** (Stacks Project Tag 081S): let `X` be a qcqs
scheme, `U ⊆ X` a quasi-compact open and `q : Z ⟶ X` separated, of finite type and an
isomorphism over `U`. Then there is a `U`-admissible blow-up `X' ⟶ X` such that the
strict transform `Z' ⟶ X'` of `q` is an open immersion.

(Blueprint: `def:nagata-elimination-indeterminacy`,
`lemma:nagata-elimination-indeterminacy`; proof order item 30.) -/
theorem exists_admissibleBlowup_strictTransform_open
    {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X] {U : X.Opens}
    (hU : IsCompact (U : Set X)) {Z : Scheme.{u}} (q : Z ⟶ X)
    [IsSeparated q] [LocallyOfFiniteType q] [QuasiCompact q]
    (hq : IsIso (q ∣_ U)) :
    ∃ B : IsAdmissible X U,
      IsOpenImmersion (strictTransformMap q B.I.blowupMap B.preservedOpen) := by
  -- The Stacks proof flattens the (finite type, flat over `U`) structure sheaf datum
  -- of `q` by a `U`-admissible blow-up (Tags 0815 and 081R) and observes that a flat,
  -- finitely presented strict transform which is a monomorphism over `U` is an open
  -- immersion. The revised blueprint drops the flattening chain from the formalized
  -- route, so this is the one primitive obligation of the modification layer, and the
  -- route to it is genuinely open.
  sorry

section ImageTransport

variable {S X Y V : Scheme.{u}} (x : X ⟶ S) (y : Y ⟶ S)

/-- **Scheme-theoretic images and admissible blow-ups** (Stacks Project Tag 0F3Y):
let `h : V ⟶ X ×_S Y` be quasi-compact and quasi-separated whose first projection
factors through a quasi-compact open `U ⊆ X`, and let `B` be a `U`-admissible blow-up
of `X`. For every lift `h' : V ⟶ X' ×_S Y` of `h` along the base-changed blow-up
`X' ×_S Y ⟶ X ×_S Y` (such a lift exists because the blow-up is an isomorphism over
`U`), the scheme-theoretic image of `h'` is the strict transform of the
scheme-theoretic image of `h`, as closed subschemes of `X' ×_S Y`.

The statement is in kernel ideal sheaf form: both closed subschemes of `X' ×_S Y` are
recorded by the kernels of the corresponding closed immersions.

**Hypotheses.** The right-hand side is a strict transform, so the theorem carries the
standing quasi-compactness assumption of
`WeilConjectures.Compactification.StrictTransform`: the inclusion of the open locus
over the preserved open must be a quasi-compact morphism, which is exactly what every
comparison lemma about the strict transform requires. It is discharged from finiteness
data by `AlgebraicGeometry.quasiCompact_strictTransformOpen_ι`, and it is not implied
by the remaining hypotheses — nothing here makes `U`, `B.preservedOpen` or `X`
quasi-compact.

**Proof.** The blow-up is an isomorphism over the complement of its center, hence so is
its base change `X' ×_S Y ⟶ X ×_S Y` over the preimage of that complement
(`AlgebraicGeometry.isIso_partialSectionOpenι_restrict`); so the open locus of
`SIm(h) ×_{X ×_S Y} (X' ×_S Y)` over the preserved open is the restriction of `SIm(h)`
itself (`AlgebraicGeometry.isPullback_strictTransformOpen`). Since `h`'s first
projection lands in `U ≤ B.preservedOpen`, the lift `h'` factors through that open
locus, and the factorization is scheme-theoretically dominant because `h ⟶ SIm(h)` is
and dominance descends along a flat base change. So `h'` and the open locus have the
same scheme-theoretic image in `X' ×_S Y`; the open locus and the strict transform have
the same one by `AlgebraicGeometry.ker_strictTransformMap`.
(Blueprint: `lemma:nagata-scheme-image-strict-transform`,
`lemma:nagata-scheme-image-transport-strict-transform`; proof order item 31.) -/
theorem Scheme.Hom.schemeTheoreticImage_after_admissibleBlowup
    {U : X.Opens} (B : IsAdmissible X U)
    (h : V ⟶ pullback x y) [QuasiCompact h] [QuasiSeparated h]
    (hfac : Set.range (h ≫ pullback.fst x y) ⊆ (U : Set X))
    (h' : V ⟶ pullback (B.I.blowupMap ≫ x) y) [QuasiCompact h']
    (hlift : h' ≫ partialSectionOpenι x y B.I.blowupMap = h)
    [QuasiCompact (strictTransformOpen h.imageι (partialSectionOpenι x y B.I.blowupMap)
      (pullback.fst x y ⁻¹ᵁ B.preservedOpen)).ι] :
    h'.ker =
      (AlgebraicGeometry.strictTransformι h.imageι
          (partialSectionOpenι x y B.I.blowupMap)
          (pullback.fst x y ⁻¹ᵁ B.preservedOpen) ≫
        pullback.snd h.imageι (partialSectionOpenι x y B.I.blowupMap)).ker := by
  set ρ := partialSectionOpenι x y B.I.blowupMap
  set W : (pullback x y).Opens := pullback.fst x y ⁻¹ᵁ B.preservedOpen
  set L := strictTransformOpen h.imageι ρ W with hL
  -- `h` lands over the preserved open, because it lands over `U ≤ B.preservedOpen`.
  have hrange : Set.range h ⊆ (W : Set ↥(pullback x y)) := by
    rintro _ ⟨v, rfl⟩
    have : (h ≫ pullback.fst x y) v ∈ (U : Set X) := hfac ⟨v, rfl⟩
    exact B.le_preservedOpen (by simpa [Scheme.Hom.comp_apply] using this)
  -- The blow-up is an isomorphism over its own preserved open, ...
  have hπiso : IsIso (B.I.blowupMap ∣_ B.preservedOpen) :=
    B.I.isIso_blowupMap_restrict_support_compl
  -- ... hence so is its base change, over the preimage of the preserved open.
  have hρiso : IsIso (ρ ∣_ W) :=
    isIso_partialSectionOpenι_restrict x y B.I.blowupMap B.preservedOpen
  -- So the open locus is the restriction of `SIm(h)` over the preserved open.
  have hPB := isPullback_strictTransformOpen h.imageι ρ W
  -- The lift of `h` to `SIm(h) ×_(X ×_S Y) (X' ×_S Y)`.
  have hcond : h.toImage ≫ h.imageι = h' ≫ ρ := by
    rw [Scheme.Hom.toImage_imageι, hlift]
  set k := pullback.lift h.toImage h' hcond
  have hkfst : k ≫ pullback.fst h.imageι ρ = h.toImage := pullback.lift_fst _ _ _
  have hksnd : k ≫ pullback.snd h.imageι ρ = h' := pullback.lift_snd _ _ _
  -- It lands in the open locus, again because `h` lands over the preserved open.
  have hkrange : Set.range k ⊆ Set.range L.ι := by
    rw [Scheme.Opens.range_ι, hL, strictTransformOpen_eq_preimage]
    rintro _ ⟨v, rfl⟩
    have : (k ≫ pullback.fst h.imageι ρ ≫ h.imageι) v ∈ (W : Set ↥(pullback x y)) := by
      rw [← Category.assoc, hkfst, Scheme.Hom.toImage_imageι]
      exact hrange ⟨v, rfl⟩
    simpa [Scheme.Hom.comp_apply] using this
  set m := IsOpenImmersion.lift L.ι k hkrange
  have hmfac : m ≫ L.ι = k := IsOpenImmersion.lift_fac _ _ _
  -- The projection of the open locus to `SIm(h)` is a base change of the open immersion
  -- `W ⟶ X ×_S Y`, so `V` sits inside the open locus as a flat base change of
  -- `V ⟶ SIm(h)`, and scheme-theoretic dominance descends.
  have hp₁ : IsOpenImmersion (L.ι ≫ pullback.fst h.imageι ρ) :=
    IsOpenImmersion.of_isPullback hPB.flip inferInstance
  have hsq : IsPullback (𝟙 V) m h.toImage (L.ι ≫ pullback.fst h.imageι ρ) :=
    IsPullback.of_horiz_isIso_mono ⟨by rw [Category.id_comp, ← Category.assoc, hmfac, hkfst]⟩
  have hmker : m.ker = ⊥ := by
    rw [h.toImage.ker_of_isPullback (L.ι ≫ pullback.fst h.imageι ρ) hsq,
      Scheme.Hom.ker_eq_bot, Scheme.IdealSheafData.comap_bot]
  have : IsSchemeTheoreticallyDominant m := (isSchemeTheoreticallyDominant_iff m).mpr hmker
  calc h'.ker = (m ≫ (L.ι ≫ pullback.snd h.imageι ρ)).ker := by
        rw [← Category.assoc, hmfac, hksnd]
    _ = (L.ι ≫ pullback.snd h.imageι ρ).ker :=
        Scheme.Hom.ker_comp_of_isSchemeTheoreticallyDominant _ _
    _ = _ := (ker_strictTransformMap h.imageι ρ W).symm

end ImageTransport

section CommonModification

variable {S U X₁ X₂ : Scheme.{u}}

/-- The data of a **common modification** of two separated finite-type models `X₁`,
`X₂` of a common open `U` over `S` (Stacks Project Tag 0F3X): admissible blow-ups
`X'ᵢ ⟶ Xᵢ`, open immersions of both `X'ᵢ` into a glued scheme `W`, agreeing lifted
copies of `U`, such that the two opens cover `W` and `W` is separated and of finite
type over `S`.
(Blueprint: `def:nagata-common-modification`.) -/
structure CommonModification (s₁ : X₁ ⟶ S) (s₂ : X₂ ⟶ S) (j₁ : U ⟶ X₁) (j₂ : U ⟶ X₂)
    [IsOpenImmersion j₁] [IsOpenImmersion j₂] where
  /-- The `U`-admissible blow-up of the first model. -/
  B₁ : IsAdmissible X₁ j₁.opensRange
  /-- The `U`-admissible blow-up of the second model. -/
  B₂ : IsAdmissible X₂ j₂.opensRange
  /-- The glued common modification. -/
  W : Scheme.{u}
  /-- The structure morphism of the common modification. -/
  w : W ⟶ S
  /-- The open immersion of the first modified model into the glued scheme. -/
  k₁ : B₁.I.blowup ⟶ W
  /-- The open immersion of the second modified model into the glued scheme. -/
  k₂ : B₂.I.blowup ⟶ W
  isOpenImmersion_k₁ : IsOpenImmersion k₁
  isOpenImmersion_k₂ : IsOpenImmersion k₂
  k₁_w : k₁ ≫ w = B₁.I.blowupMap ≫ s₁
  k₂_w : k₂ ≫ w = B₂.I.blowupMap ≫ s₂
  /-- The lift of `U` into the first modified model. -/
  u₁ : U ⟶ B₁.I.blowup
  /-- The lift of `U` into the second modified model. -/
  u₂ : U ⟶ B₂.I.blowup
  u₁_blowupMap : u₁ ≫ B₁.I.blowupMap = j₁
  u₂_blowupMap : u₂ ≫ B₂.I.blowupMap = j₂
  /-- The two copies of `U` in the glued scheme agree. -/
  u_glue : u₁ ≫ k₁ = u₂ ≫ k₂
  /-- The two modified models cover the glued scheme. -/
  cover : Set.range k₁ ∪ Set.range k₂ = Set.univ
  isSeparated_w : IsSeparated w
  locallyOfFiniteType_w : LocallyOfFiniteType w
  quasiCompact_w : QuasiCompact w

attribute [instance] CommonModification.isOpenImmersion_k₁
  CommonModification.isOpenImmersion_k₂ CommonModification.isSeparated_w
  CommonModification.locallyOfFiniteType_w CommonModification.quasiCompact_w

/-- **Existence of a common modification** (Stacks Project Tag 0F3X): two separated
finite-type models `X₁`, `X₂` over a qcqs base `S` of a common quasi-compact open `U`
admit a common modification: `U`-admissible blow-ups `X'ᵢ ⟶ Xᵢ` which glue along a
common open copy of the blown-up `U`-locus to a separated finite-type scheme over `S`.

The construction is the one of the blueprint: form the scheme-theoretic image
`X₁₂ ⊆ X₁ ×_S X₂` of `U`, eliminate the indeterminacy of both projections
(`exists_admissibleBlowup_strictTransform_open`), dominate the two center ideals by
their product (`Scheme.IdealSheafData.exists_blowup_mul_iso`) and extend the resulting
common blow-up of `X₁₂` across the open strict transforms.
(Blueprint: `lemma:nagata-common-modification`; proof order item 32.) -/
theorem exists_commonModification [CompactSpace S] [QuasiSeparatedSpace S]
    (sU : U ⟶ S) (s₁ : X₁ ⟶ S) (s₂ : X₂ ⟶ S) (j₁ : U ⟶ X₁) (j₂ : U ⟶ X₂)
    [IsOpenImmersion j₁] [IsOpenImmersion j₂] [QuasiCompact j₁] [QuasiCompact j₂]
    (hj₁ : j₁ ≫ s₁ = sU) (hj₂ : j₂ ≫ s₂ = sU)
    [IsSeparated s₁] [LocallyOfFiniteType s₁] [QuasiCompact s₁]
    [IsSeparated s₂] [LocallyOfFiniteType s₂] [QuasiCompact s₂] :
    Nonempty (CommonModification s₁ s₂ j₁ j₂) := by
  sorry

end CommonModification

section GraphExtension

variable {S U : Scheme.{u}}

/-- The data of a **graph extension** of a compactification `c` of a quasi-compact open
`V ⊆ U` (Stacks Project Tag 0F3Z): a `V`-admissible blow-up `B : Y^gr ⟶ c.Z` of the
compactification, an open subscheme `V^gr ⊆ Y^gr` and a proper morphism
`ψ : V^gr ⟶ U` over `S` extending the inclusion of `V`, such that `V` embeds in `V^gr`
as the whole inverse image of `V` and `ψ` is an isomorphism over `V`.
(Blueprint: `def:nagata-graph-extension`.) -/
structure Compactification.ProperExtension (u : U ⟶ S) (V : U.Opens)
    (c : Compactification (V.ι ≫ u)) where
  /-- The `V`-admissible blow-up of the compactification. -/
  B : IsAdmissible c.Z c.i.opensRange
  /-- The open subscheme `V^gr` of the blown-up compactification carrying the
  extension. -/
  Vgr : B.I.blowup.Opens
  /-- The proper extension `V^gr ⟶ U` of the inclusion of `V`. -/
  ψ : Vgr.toScheme ⟶ U
  /-- The open embedding of `V` into `V^gr`. -/
  v : V.toScheme ⟶ Vgr.toScheme
  isProper_ψ : IsProper ψ
  isOpenImmersion_v : IsOpenImmersion v
  /-- The embedded copy of `V` lifts the open immersion of the compactification. -/
  v_blowupMap : v ≫ Vgr.ι ≫ B.I.blowupMap = c.i
  /-- The extension really extends the inclusion of `V`. -/
  v_ψ : v ≫ ψ = V.ι
  /-- The inverse image of `V` is exactly the embedded copy of `V`. -/
  range_v : ((ψ ⁻¹ᵁ V : Vgr.toScheme.Opens) : Set Vgr.toScheme) = Set.range v
  isIso_ψ_restrict : IsIso (ψ ∣_ V)
  /-- The extension lies over `S`. -/
  ψ_u : ψ ≫ u = Vgr.ι ≫ B.I.blowupMap ≫ c.g

attribute [instance] Compactification.ProperExtension.isProper_ψ
  Compactification.ProperExtension.isOpenImmersion_v

/-- **Graph extension** (Stacks Project Tag 0F3Z): a compactification of a
quasi-compact open `V ⊆ U` extends, after a `V`-admissible blow-up of the
compactification, to a proper morphism `V^gr ⟶ U` restricting to the identity on `V`.
(Blueprint: `lemma:nagata-graph-extension`; proof order item 33.) -/
theorem Compactification.nonempty_properExtension
    [CompactSpace S] [QuasiSeparatedSpace S] (u : U ⟶ S)
    [IsSeparated u] [LocallyOfFiniteType u] [QuasiCompact u]
    (V : U.Opens) (hV : IsCompact (V : Set U)) (c : Compactification (V.ι ≫ u)) :
    Nonempty (Compactification.ProperExtension u V c) := by
  -- The graph construction of the blueprint: `V^gr` is the open strict transform of
  -- the scheme-theoretic image of the graph `V ⟶ c.Z ×_S U`, supplied by the
  -- partial-section lemma (`partialSectionRestrictIso`), the image transport
  -- lemma (`Scheme.Hom.schemeTheoreticImage_after_admissibleBlowup`) and elimination
  -- of indeterminacy (`exists_admissibleBlowup_strictTransform_open`); `ψ` is the
  -- second projection, proper because `c.Z ×_S U ⟶ U` is proper
  -- (`isProper_imageι_fst`).
  sorry

end GraphExtension

section IsomorphismNearClosure

/-- **Isomorphism near the closure of a boundary piece** (Stacks Project Tag 0F3W): let
`X` be qcqs, `U ⊆ X` a quasi-compact open, `q : Z ⟶ X` proper and `T ⊆ U` a subset
closed in `U` such that `q` is an isomorphism over an open neighbourhood `N` of `T`.
Then there is a `U`-admissible blow-up `B` of `X` such that the strict transform of `q`
is an isomorphism over an open neighbourhood of the closure of `T` in the blown-up
scheme.

The construction of the blueprint separates `T` from the complement of the maximal
isomorphism open of `q` (`Scheme.Hom.maximalIsomorphismOpen`) by the boundary
separation blow-up (`exists_admissibleBlowup_disjoint_closures`) and then eliminates
the indeterminacy of `q` (`exists_admissibleBlowup_strictTransform_open`) away from
the separated bad locus; a proper open immersion onto a scheme-theoretically dense
open is an isomorphism.
(Blueprint: `def:nagata-isomorphism-near-closure`,
`lemma:nagata-isomorphism-near-closure`; used for the improved comparison projection
of the two-open compactification theorem.) -/
theorem exists_admissibleBlowup_strictTransform_isIso_near_closure
    {X Z : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X] {U : X.Opens}
    (hU : IsCompact (U : Set X)) (q : Z ⟶ X) [IsProper q]
    {T : Set X} (hTU : T ⊆ (U : Set X)) (hT : IsClosed (U.ι ⁻¹' T))
    {N : X.Opens} (hTN : T ⊆ (N : Set X)) (hN : IsIso (q ∣_ N)) :
    ∃ (B : IsAdmissible X U) (N' : B.I.blowup.Opens),
      closure (B.I.blowupMap ⁻¹' T) ⊆ (N' : Set B.I.blowup) ∧
      IsIso (strictTransformMap q B.I.blowupMap B.preservedOpen ∣_ N') := by
  sorry

end IsomorphismNearClosure

end AlgebraicGeometry
