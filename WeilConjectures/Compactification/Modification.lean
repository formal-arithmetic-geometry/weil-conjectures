/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import WeilConjectures.Blowup.AdmissibleBlowup
public import WeilConjectures.Mathlib.AlgebraicGeometry.OpenImmersion
public import WeilConjectures.Mathlib.AlgebraicGeometry.Pullbacks
public import WeilConjectures.Compactification.Defs
public import WeilConjectures.Compactification.StrictTransform

/-!

# Elimination of indeterminacy, common modifications and graph extension

This file records the modification steps of the proof of Nagata's compactification
theorem, following the blueprint chapter "Nagata compactification", sections
"Boundary preparation" and "Common modifications and graph extension"
(proof order items 30–33):

- `AlgebraicGeometry.exists_admissibleBlowup_isOpenImmersion_strictTransformMap`:
  **elimination of indeterminacy** (Stacks Project Tag 081S; blueprint
  `lemma:nagata-elimination-indeterminacy`): if `q : Z ⟶ X` is separated, of finite
  type and an isomorphism over a quasi-compact open `U` of the qcqs scheme `X`, then
  after a `U`-admissible blow-up the strict transform of `q` is an open immersion;
- `AlgebraicGeometry.Scheme.Hom.ker_lift_admissibleBlowup`:
  **transport of scheme-theoretic images through admissible blow-ups** (Stacks
  Project Tag 0F3Y; blueprint `lemma:nagata-scheme-image-strict-transform`): the
  scheme-theoretic image of a lift along a `U`-admissible blow-up is the strict
  transform of the scheme-theoretic image;
- `AlgebraicGeometry.CommonModification` and
  `AlgebraicGeometry.nonempty_commonModification`: **common modification of two models**
  (Stacks Project Tag 0F3X; blueprint `def:nagata-common-modification`,
  `lemma:nagata-common-modification`): two separated finite-type models of a common
  open `U` admit `U`-admissible blow-ups which glue along a common copy of the
  modified `U`-locus to a separated finite-type model;
- `AlgebraicGeometry.Compactification.nonempty_properExtension`: **graph extension**
  (Stacks Project Tag 0F3Z; blueprint `def:nagata-graph-extension`,
  `lemma:nagata-graph-extension`): a compactification of a quasi-compact open
  `V ⊆ U` extends, after a `V`-admissible blow-up of the compactification, to a
  proper morphism `V^gr ⟶ U` restricting to the identity on `V`;
- `AlgebraicGeometry.exists_admissibleBlowup_isIso_strictTransformMap_near_closure`:
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

`exists_admissibleBlowup_isOpenImmersion_strictTransformMap` (Tag 081S) is the only
*primitive* obligation of this file: `Scheme.Hom.ker_lift_admissibleBlowup` (0F3Y),
`nonempty_commonModification` (0F3X), `Compactification.nonempty_properExtension` (0F3Z)
and `exists_admissibleBlowup_isIso_strictTransformMap_near_closure` (0F3W) are all
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
theorem exists_admissibleBlowup_isOpenImmersion_strictTransformMap
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

variable {S X Y V : Scheme.{u}} {x : X ⟶ S} {y : Y ⟶ S}

/-- **Scheme-theoretic images and admissible blow-ups** (Stacks Project Tag 0F3Y):
let `h : V ⟶ X ×_S Y` be quasi-compact whose first projection factors through a
quasi-compact open `U ⊆ X`, and let `B` be a `U`-admissible blow-up of `X`. For every
lift `h' : V ⟶ X' ×_S Y` of `h` along the base-changed blow-up `X' ×_S Y ⟶ X ×_S Y`
(such a lift exists because the blow-up is an isomorphism over `U`), the
scheme-theoretic image of `h'` is the strict transform of the scheme-theoretic image
of `h`, as closed subschemes of `X' ×_S Y`.

The statement is in kernel ideal sheaf form: both closed subschemes of `X' ×_S Y` are
recorded by the kernels of the corresponding closed immersions. The Stacks Project and
the blueprint also assume `h` quasi-separated; Mathlib's kernel ideal sheaf theory only
needs quasi-compactness, so that hypothesis is dropped here.

**Hypotheses.** The right-hand side is a strict transform, so the theorem carries the
standing quasi-compactness assumption of
`WeilConjectures.Compactification.StrictTransform`: the inclusion of the open locus
over the preserved open must be a quasi-compact morphism, which is exactly what every
comparison lemma about the strict transform requires. It is not implied by the
remaining hypotheses — nothing here makes `U`, `B.preservedOpen` or `X` quasi-compact —
and is discharged from finiteness data by
`AlgebraicGeometry.quasiCompact_strictTransformOpen_ι_of_isCompact`. (The
specialization `AlgebraicGeometry.quasiCompact_strictTransformOpen_ι` does *not* apply:
it is stated for a blow-up map of an ideal sheaf, not for the base-changed blow-up
occurring here.)
(Blueprint: `lemma:nagata-scheme-image-strict-transform`,
`lemma:nagata-scheme-image-transport-strict-transform`; proof order item 31.) -/
theorem Scheme.Hom.ker_lift_admissibleBlowup
    {U : X.Opens} (B : IsAdmissible X U)
    (h : V ⟶ pullback x y) [QuasiCompact h]
    (hfac : Set.range (h ≫ pullback.fst x y) ⊆ (U : Set X))
    (h' : V ⟶ pullback (B.I.blowupMap ≫ x) y)
    (hlift : h' ≫ partialSectionOpenι x y B.I.blowupMap = h)
    [QuasiCompact (strictTransformOpen h.imageι (partialSectionOpenι x y B.I.blowupMap)
      (pullback.fst x y ⁻¹ᵁ B.preservedOpen)).ι] :
    h'.ker =
      (strictTransformMap h.imageι (partialSectionOpenι x y B.I.blowupMap)
        (pullback.fst x y ⁻¹ᵁ B.preservedOpen)).ker := by
  set ρ := partialSectionOpenι x y B.I.blowupMap
  set W : (pullback x y).Opens := pullback.fst x y ⁻¹ᵁ B.preservedOpen
  set L := strictTransformOpen h.imageι ρ W
  -- `h` lands over the preserved open, because it lands over `U ≤ B.preservedOpen`.
  have hrange : Set.range h ⊆ (W : Set ↥(pullback x y)) := by
    rintro _ ⟨v, rfl⟩
    exact B.le_preservedOpen (by simpa [Scheme.Hom.comp_apply] using hfac ⟨v, rfl⟩)
  -- The blow-up is an isomorphism over its own preserved open, ...
  have : IsIso (B.I.blowupMap ∣_ B.preservedOpen) :=
    B.I.isIso_blowupMap_restrict_support_compl
  -- ... hence so is its base change, over the preimage of the preserved open.
  have : IsIso (ρ ∣_ W) :=
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
  have hkrange : Set.range (k ≫ pullback.fst h.imageι ρ ≫ h.imageι) ⊆
      (W : Set ↥(pullback x y)) := by
    rw [← Category.assoc, hkfst, Scheme.Hom.toImage_imageι]
    exact hrange
  set m := strictTransformOpenLift h.imageι ρ W k hkrange
  have hmfac : m ≫ L.ι = k := strictTransformOpenLift_ι h.imageι ρ W k hkrange
  -- The projection of the open locus to `SIm(h)` is a base change of the open immersion
  -- `W ⟶ X ×_S Y`, so `V` sits inside the open locus as a flat base change of
  -- `V ⟶ SIm(h)`, and scheme-theoretic dominance descends.
  have : IsOpenImmersion (L.ι ≫ pullback.fst h.imageι ρ) :=
    IsOpenImmersion.of_isPullback hPB.flip inferInstance
  have hsq : IsPullback (𝟙 V) m h.toImage (L.ι ≫ pullback.fst h.imageι ρ) :=
    IsPullback.of_horiz_isIso_mono
      ⟨by rw [Category.id_comp, ← Category.assoc, hmfac, hkfst]⟩
  have : IsSchemeTheoreticallyDominant m := .of_isPullback hsq
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
  /-- The first modified model is an open subscheme of the glued scheme. -/
  isOpenImmersion_k₁ : IsOpenImmersion k₁
  /-- The second modified model is an open subscheme of the glued scheme. -/
  isOpenImmersion_k₂ : IsOpenImmersion k₂
  /-- The first open immersion lies over `S`. -/
  k₁_w : k₁ ≫ w = B₁.I.blowupMap ≫ s₁
  /-- The second open immersion lies over `S`. -/
  k₂_w : k₂ ≫ w = B₂.I.blowupMap ≫ s₂
  /-- The lift of `U` into the first modified model. -/
  u₁ : U ⟶ B₁.I.blowup
  /-- The lift of `U` into the second modified model. -/
  u₂ : U ⟶ B₂.I.blowup
  /-- The first lift of `U` lies over the given open immersion `j₁`. -/
  u₁_blowupMap : u₁ ≫ B₁.I.blowupMap = j₁
  /-- The second lift of `U` lies over the given open immersion `j₂`. -/
  u₂_blowupMap : u₂ ≫ B₂.I.blowupMap = j₂
  /-- The two copies of `U` in the glued scheme agree. -/
  u_glue : u₁ ≫ k₁ = u₂ ≫ k₂
  /-- The two modified models cover the glued scheme. -/
  cover : Set.range k₁ ∪ Set.range k₂ = Set.univ
  /-- The glued scheme is separated over `S`. -/
  isSeparated_w : IsSeparated w
  /-- The glued scheme is locally of finite type over `S`. -/
  locallyOfFiniteType_w : LocallyOfFiniteType w
  /-- The glued scheme is quasi-compact over `S`. -/
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
(`exists_admissibleBlowup_isOpenImmersion_strictTransformMap`), dominate the two center
ideals by their product (`Scheme.IdealSheafData.exists_blowup_mul_iso`) and extend the
resulting common blow-up of `X₁₂` across the open strict transforms.
(Blueprint: `lemma:nagata-common-modification`; proof order item 32.) -/
theorem nonempty_commonModification [CompactSpace S] [QuasiSeparatedSpace S]
    (s₁ : X₁ ⟶ S) (s₂ : X₂ ⟶ S) (j₁ : U ⟶ X₁) (j₂ : U ⟶ X₂)
    [IsOpenImmersion j₁] [IsOpenImmersion j₂] [QuasiCompact j₁] [QuasiCompact j₂]
    (hj : j₁ ≫ s₁ = j₂ ≫ s₂)
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
  /-- The extension is proper. -/
  isProper_ψ : IsProper ψ
  /-- The copy of `V` is an open subscheme of `V^gr`. -/
  isOpenImmersion_v : IsOpenImmersion v
  /-- The embedded copy of `V` lifts the open immersion of the compactification. -/
  v_blowupMap : v ≫ Vgr.ι ≫ B.I.blowupMap = c.i
  /-- The extension really extends the inclusion of `V`. -/
  v_ψ : v ≫ ψ = V.ι
  /-- The inverse image of `V` is exactly the embedded copy of `V`. -/
  range_v : ((ψ ⁻¹ᵁ V : Vgr.toScheme.Opens) : Set Vgr.toScheme) = Set.range v
  /-- The extension is an isomorphism over `V`. -/
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
  -- lemma (`Scheme.Hom.ker_lift_admissibleBlowup`) and elimination of indeterminacy
  -- (`exists_admissibleBlowup_isOpenImmersion_strictTransformMap`); `ψ` is the second
  -- projection, proper because `c.Z ×_S U ⟶ U` is proper
  -- (`isProper_imageι_comp_fst`).
  -- Step 0: finiteness of the ambient schemes and quasi-compactness of the inclusions.
  have : CompactSpace U := QuasiCompact.compactSpace_of_compactSpace u
  have : QuasiSeparatedSpace U := quasiSeparatedSpace_of_quasiSeparated u
  have : CompactSpace c.Z := QuasiCompact.compactSpace_of_compactSpace c.g
  have : QuasiSeparatedSpace c.Z := quasiSeparatedSpace_of_quasiSeparated c.g
  have : CompactSpace V.toScheme := isCompact_iff_compactSpace.mp hV
  have : QuasiCompact c.i := c.quasiCompact_openImmersion inferInstance
  -- Step 1: the graph `γ = (c.i, V.ι) : V ⟶ c.Z ×_S U` of the compactification, a
  -- partial section of the first projection over the open immersion `c.i`.
  obtain ⟨γ, hγfst, hγsnd⟩ : ∃ γ : V.toScheme ⟶ pullback c.g u,
      γ ≫ pullback.fst c.g u = c.i ∧ γ ≫ pullback.snd c.g u = V.ι :=
    ⟨pullback.lift c.i V.ι c.comm.symm, pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
  have hqcγ : QuasiCompact γ := quasiCompact_of_partialSection c.g u c.i γ hγfst
  -- the two projections of the scheme-theoretic image of the graph
  let p : γ.image ⟶ c.Z := γ.imageι ≫ pullback.fst c.g u
  let ψ₀ : γ.image ⟶ U := γ.imageι ≫ pullback.snd c.g u
  have hψ₀def : ψ₀ = γ.imageι ≫ pullback.snd c.g u := rfl
  have : IsSeparated (pullback.fst c.g u) := MorphismProperty.pullback_fst _ _ ‹_›
  have : LocallyOfFiniteType (pullback.fst c.g u) := MorphismProperty.pullback_fst _ _ ‹_›
  have : QuasiCompact (pullback.fst c.g u) := MorphismProperty.pullback_fst _ _ ‹_›
  have : IsSeparated p := inferInstanceAs (IsSeparated (γ.imageι ≫ pullback.fst c.g u))
  have : LocallyOfFiniteType p :=
    inferInstanceAs (LocallyOfFiniteType (γ.imageι ≫ pullback.fst c.g u))
  have : QuasiCompact p := inferInstanceAs (QuasiCompact (γ.imageι ≫ pullback.fst c.g u))
  -- Step 2: `p` is an isomorphism over the compact open `V₀ = c.i(V)`
  -- (`isIso_restrict_imageι_comp_fst`), so its indeterminacy can be eliminated.
  have hV₀ : IsCompact ((c.i.opensRange : c.Z.Opens) : Set c.Z) :=
    isCompact_range c.i.continuous
  have hpV₀ : IsIso (p ∣_ c.i.opensRange) := isIso_restrict_imageι_comp_fst c.g u c.i γ hγfst
  obtain ⟨B, hB⟩ := exists_admissibleBlowup_isOpenImmersion_strictTransformMap hV₀ p hpV₀
  let π : B.I.blowup ⟶ c.Z := B.I.blowupMap
  let W : c.Z.Opens := B.preservedOpen
  haveI hOIst : IsOpenImmersion (strictTransformMap p π W) := hB
  -- `V^gr` is the open strict transform, and `ψ` the projection to `U` through the
  -- scheme-theoretic image of the graph.
  let Vgr : B.I.blowup.Opens := (strictTransformMap p π W).opensRange
  let e : strictTransform p π W ≅ Vgr.toScheme := (strictTransformMap p π W).isoOpensRange
  have he : e.hom ≫ Vgr.ι = strictTransformMap p π W :=
    (strictTransformMap p π W).isoOpensRange_hom_ι
  have hVgrι : Vgr.ι = e.inv ≫ strictTransformMap p π W := by
    rw [← he, Iso.inv_hom_id_assoc]
  let ψ : Vgr.toScheme ⟶ U := e.inv ≫ strictTransformToSource p π W ≫ ψ₀
  have hψdef : ψ = e.inv ≫ strictTransformToSource p π W ≫ ψ₀ := rfl
  -- Step 3: the canonical lift `ℓ` of `c.i` along the blow-up, an open immersion with
  -- range the full preimage of `c.i(V)`.
  haveI hπV₀ : IsIso (π ∣_ c.i.opensRange) := B.isIso_blowupMap_restrict
  obtain ⟨ℓ, hℓπ⟩ : ∃ ℓ : V.toScheme ⟶ B.I.blowup, ℓ ≫ π = c.i :=
    ⟨(c.i.isoOpensRange.hom ≫ inv (π ∣_ c.i.opensRange)) ≫ (π ⁻¹ᵁ c.i.opensRange).ι, by
      simp only [Category.assoc]
      rw [← morphismRestrict_ι, IsIso.inv_hom_id_assoc, Scheme.Hom.isoOpensRange_hom_ι]⟩
  have hOIℓ : IsOpenImmersion ℓ :=
    isOpenImmersion_of_comp_of_isIso_restrict ℓ π c.i hℓπ hπV₀
  have hrangeℓ : Set.range ℓ = ⇑π ⁻¹' Set.range c.i :=
    range_eq_preimage_of_comp_of_isIso_restrict ℓ π c.i hℓπ hπV₀
  -- the canonical morphism to the image projects back to `c.i` and `V.ι`
  have htoImp : γ.toImage ≫ p = c.i := by
    have h := Scheme.Hom.toImage_imageι_assoc γ (pullback.fst c.g u)
    rw [hγfst] at h
    exact h
  have hψ₀V : γ.toImage ≫ ψ₀ = V.ι := by
    have h := Scheme.Hom.toImage_imageι_assoc γ (pullback.snd c.g u)
    rw [hγsnd] at h
    exact h
  -- Step 4: the embedding `v` of `V` into `V^gr`, through the open strict transform.
  obtain ⟨v, hvι, hvst⟩ : ∃ v : V.toScheme ⟶ Vgr.toScheme,
      v ≫ Vgr.ι = ℓ ∧ v ≫ e.inv ≫ strictTransformToSource p π W = γ.toImage := by
    have hcompk : γ.toImage ≫ p = ℓ ≫ π := by
      rw [htoImp, hℓπ]
    have hkfst : pullback.lift γ.toImage ℓ hcompk ≫ pullback.fst p π = γ.toImage :=
      pullback.lift_fst _ _ _
    have hksnd : pullback.lift γ.toImage ℓ hcompk ≫ pullback.snd p π = ℓ :=
      pullback.lift_snd _ _ _
    have hkrange : Set.range (pullback.lift γ.toImage ℓ hcompk ≫ pullback.fst p π ≫ p) ⊆
        (W : Set c.Z) := by
      rw [← Category.assoc, hkfst, htoImp]
      rintro - ⟨t, rfl⟩
      exact B.le_preservedOpen ⟨t, rfl⟩
    refine ⟨(strictTransformOpenLift p π W (pullback.lift γ.toImage ℓ hcompk) hkrange ≫
        strictTransformFactor p π W) ≫ e.hom, ?_, ?_⟩
    · rw [Category.assoc, he, Category.assoc, strictTransformFactor_strictTransformMap,
        strictTransformOpenLift_ι_assoc, hksnd]
    · rw [Category.assoc, Iso.hom_inv_id_assoc]
      simp only [strictTransformToSource]
      rw [Category.assoc, strictTransformFactor_ι_assoc, strictTransformOpenLift_ι_assoc,
        hkfst]
  -- Step 5: the extension `ψ` is proper: it is a closed immersion into the base change
  -- of the (proper) blow-up followed by the proper projection `SIm(γ) ⟶ U`.
  have hψ₀proper : IsProper ψ₀ := by
    have h1 : IsProper (pullback.snd c.g u) := MorphismProperty.pullback_snd _ _ c.isProper
    exact inferInstanceAs (IsProper (γ.imageι ≫ pullback.snd c.g u))
  have hψproper : IsProper ψ := by
    have h2 : IsProper (pullback.fst p π) :=
      MorphismProperty.pullback_fst _ _ B.isProper_blowupMap
    rw [hψdef]
    simp only [strictTransformToSource]
    infer_instance
  -- Step 6: `v` is an open immersion, since `ℓ` is one.
  have hOIv : IsOpenImmersion v := by
    have : IsOpenImmersion (v ≫ Vgr.ι) := by
      rw [hvι]
      exact hOIℓ
    exact IsOpenImmersion.of_comp v Vgr.ι
  -- Step 7: the compatibilities of `v` and `ψ`.
  have hvblow : v ≫ Vgr.ι ≫ π = c.i := by
    rw [← Category.assoc, hvι, hℓπ]
  have hvψ : v ≫ ψ = V.ι := by
    have h1 : v ≫ ψ = (v ≫ e.inv ≫ strictTransformToSource p π W) ≫ ψ₀ := by
      rw [hψdef]
      simp only [Category.assoc]
    rw [h1, hvst, hψ₀V]
  have hpsq : ψ₀ ≫ u = p ≫ c.g := by
    have h : (γ.imageι ≫ pullback.snd c.g u) ≫ u =
        (γ.imageι ≫ pullback.fst c.g u) ≫ c.g := by
      simp only [Category.assoc, ← pullback.condition]
    exact h
  have hψu : ψ ≫ u = Vgr.ι ≫ π ≫ c.g := by
    calc ψ ≫ u = e.inv ≫ strictTransformToSource p π W ≫ ψ₀ ≫ u := by
          rw [hψdef]
          simp only [Category.assoc]
      _ = e.inv ≫ strictTransformToSource p π W ≫ p ≫ c.g := by rw [hpsq]
      _ = e.inv ≫ (strictTransformToSource p π W ≫ p) ≫ c.g := by
          simp only [Category.assoc]
      _ = e.inv ≫ (strictTransformMap p π W ≫ π) ≫ c.g := by
          rw [strictTransform_condition]
      _ = (e.inv ≫ strictTransformMap p π W) ≫ π ≫ c.g := by
          simp only [Category.assoc]
      _ = Vgr.ι ≫ π ≫ c.g := by rw [← hVgrι]
  -- Step 8: the inverse image of `V` under `ψ` is exactly the embedded copy of `V`.
  have hrangev : ((ψ ⁻¹ᵁ V : Vgr.toScheme.Opens) : Set Vgr.toScheme) = Set.range v := by
    apply subset_antisymm
    · -- a point of `V^gr` over `V` lies on the embedded copy of `V`: its image in
      -- `SIm(γ)` is a limit point of the graph lying over `V`, hence on the graph
      -- (`closure_range_inter_preimage_range_snd_subset`), and the lift `ℓ` then
      -- recovers it as the image of a point of `V`.
      intro t ht
      have htV : ψ t ∈ Set.range V.ι := by
        rw [Scheme.Opens.range_ι]
        exact ht
      have hψt : ψ t = ψ₀ (strictTransformToSource p π W (e.inv t)) := by
        rw [hψdef]
        simp only [Scheme.Hom.comp_apply]
      have hcl : γ.imageι (strictTransformToSource p π W (e.inv t)) ∈
          closure (Set.range γ) := by
        rw [← Scheme.Hom.support_ker γ, ← Scheme.IdealSheafData.range_subschemeι]
        exact ⟨_, rfl⟩
      have hsndz : pullback.snd c.g u
          (γ.imageι (strictTransformToSource p π W (e.inv t))) ∈ Set.range V.ι := by
        rw [← Scheme.Hom.comp_apply, ← hψ₀def, ← hψt]
        exact htV
      obtain ⟨v₀, hv₀⟩ := closure_range_inter_preimage_range_snd_subset c.g u γ V.ι hγsnd
        ⟨hcl, hsndz⟩
      have htoim : γ.imageι (γ.toImage v₀) = γ v₀ := by
        rw [← Scheme.Hom.comp_apply, Scheme.Hom.toImage_imageι]
      have hz₀ : strictTransformToSource p π W (e.inv t) = γ.toImage v₀ :=
        γ.imageι.isClosedEmbedding.injective (by rw [htoim, hv₀])
      have hπVgr : π (Vgr.ι t) = c.i v₀ := by
        calc π (Vgr.ι t) = (Vgr.ι ≫ π) t := (Scheme.Hom.comp_apply _ _ _).symm
          _ = ((e.inv ≫ strictTransformMap p π W) ≫ π) t := by rw [hVgrι]
          _ = (e.inv ≫ strictTransformToSource p π W ≫ p) t := by
              rw [Category.assoc, ← strictTransform_condition]
          _ = p (strictTransformToSource p π W (e.inv t)) := by
              simp only [Scheme.Hom.comp_apply]
          _ = p (γ.toImage v₀) := by rw [hz₀]
          _ = (γ.toImage ≫ p) v₀ := (Scheme.Hom.comp_apply _ _ _).symm
          _ = c.i v₀ := by rw [htoImp]
      have hbmem : Vgr.ι t ∈ Set.range ℓ := by
        rw [hrangeℓ]
        exact ⟨v₀, hπVgr.symm⟩
      obtain ⟨v₁, hv₁⟩ := hbmem
      have hv₁₀ : v₁ = v₀ := by
        apply c.i.isOpenEmbedding.injective
        calc c.i v₁ = (ℓ ≫ π) v₁ := by rw [hℓπ]
          _ = π (ℓ v₁) := Scheme.Hom.comp_apply _ _ _
          _ = π (Vgr.ι t) := by rw [hv₁]
          _ = c.i v₀ := hπVgr
      refine ⟨v₀, Vgr.ι.isOpenEmbedding.injective ?_⟩
      calc Vgr.ι (v v₀) = (v ≫ Vgr.ι) v₀ := (Scheme.Hom.comp_apply _ _ _).symm
        _ = ℓ v₀ := by rw [hvι]
        _ = ℓ v₁ := by rw [hv₁₀]
        _ = Vgr.ι t := hv₁
    · -- conversely the embedded copy of `V` lies over `V`, since `v ≫ ψ = V.ι`
      rintro - ⟨v₀, rfl⟩
      have hmem : ψ (v v₀) ∈ (V : Set U) := by
        rw [← Scheme.Hom.comp_apply, hvψ, ← Scheme.Opens.range_ι]
        exact ⟨v₀, rfl⟩
      exact hmem
  -- Step 9: `ψ` restricts to an isomorphism over `V`.
  have hisoψ : IsIso (ψ ∣_ V) := isIso_morphismRestrict_of_range_eq ψ V v hvψ hrangev
  exact ⟨{ B := B, Vgr := Vgr, ψ := ψ, v := v, isProper_ψ := hψproper,
           isOpenImmersion_v := hOIv, v_blowupMap := hvblow, v_ψ := hvψ,
           range_v := hrangev, isIso_ψ_restrict := hisoψ, ψ_u := hψu }⟩

end GraphExtension

section IsomorphismNearClosure

/-- **Isomorphism near the closure of a boundary piece** (Stacks Project Tag 0F3W): let
`X` be qcqs, `U ⊆ X` a quasi-compact open, `q : Z ⟶ X` proper and `T ⊆ U` a subset
closed in `U` such that `q` is an isomorphism over an open neighbourhood `N` of `T`.
Then there is a `U`-admissible blow-up `B` of `X` such that the strict transform of `q`
is an isomorphism over an open neighbourhood of the closure of `T` in the blown-up
scheme.

The construction of the blueprint separates `T` from the complement of the maximal
open over which `q` is an isomorphism, using the boundary-separation blow-up of the
boundary-preparation layer, and then eliminates the indeterminacy of `q`
(`exists_admissibleBlowup_isOpenImmersion_strictTransformMap`) away from the separated
bad locus; a proper open immersion onto a scheme-theoretically dense open is an
isomorphism.
(Blueprint: `def:nagata-isomorphism-near-closure`,
`lemma:nagata-isomorphism-near-closure`; used for the improved comparison projection
of the two-open compactification theorem.) -/
theorem exists_admissibleBlowup_isIso_strictTransformMap_near_closure
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
