/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.NagataRelativeGluingValidStage
import WeilConjectures.Order.DirectedFiniteUpperBound
import WeilConjectures.AlgebraicGeometry.NagataMorphismEqEventually
import WeilConjectures.AlgebraicGeometry.NagataQCOpenEqEventually
import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Pullbacks

/-!
# Relative gluing axioms at the selected stage

Source: Weil conjectures blueprint, sec-nagata-compactification,
sk-prop-nagata-sketch-approximation, node order 361
(blueprint: lemma-nagata-relative-gluing-axioms-eventually).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- The explicit piecewise gluing axioms for the transported relative datum: diagonal
coverage, reversed-orientation coverage, domain matching in both directions, inverse
identities, agreement on intersections and with reversed orientations, diagonal identity,
and the triple cocycle on the canonical common fibre-product domain.
Source: blueprint nodes orders 360--361
(blueprint: lemma-nagata-relative-gluing-axioms-eventually).
This predicate only spells out the conclusion; it supplies no gluing equations as data. -/
def NagataRelativeGluingTransport.HasGluingAxioms
    {S : Scheme.{u}} {J : Type u} {K : J → J → Type u}
    (T : NagataRelativeGluingTransport S J K) : Prop :=
  let a := T.leftInclusion
  let b := T.rightInclusion
  let g := fun j k l ↦ T.forward j k l ≫ b j k l
  let h := fun j k l ↦ T.backward j k l ≫ a j k l
  let w := fun j k ↦ ⨆ l, T.leftOpen j k l
  let v := fun j k ↦ ⨆ l, T.rightOpen j k l
  (∀ j, w j j = ⊤) ∧
  (∀ j k, w j k = v k j) ∧
  (∀ j k z l, (g j k l).left ⁻¹ᵁ w k z = (a j k l).left ⁻¹ᵁ w j z) ∧
  (∀ j k z l, (h j k l).left ⁻¹ᵁ w j z = (b j k l).left ⁻¹ᵁ w k z) ∧
  (∀ j k l, T.forward j k l ≫ T.backward j k l = 𝟙 (T.left j k l) ∧
    T.backward j k l ≫ T.forward j k l = 𝟙 (T.right j k l)) ∧
  (∀ j k l m, pullback.fst (a j k l) (a j k m) ≫ g j k l =
    pullback.snd (a j k l) (a j k m) ≫ g j k m) ∧
  (∀ j k l m, pullback.fst (b j k l) (b j k m) ≫ h j k l =
    pullback.snd (b j k l) (b j k m) ≫ h j k m) ∧
  (∀ j k l m, pullback.fst (a j k l) (b k j m) ≫ g j k l =
    pullback.snd (a j k l) (b k j m) ≫ h k j m) ∧
  (∀ j l, g j j l = a j j l) ∧
  (∀ j k z l m n,
    pullback.fst (pullback.fst (g j k l) (a k z m) ≫ a j k l) (a j z n) ≫
      pullback.snd (g j k l) (a k z m) ≫ g k z m =
    pullback.snd (pullback.fst (g j k l) (a k z m) ≫ a j k l) (a j z n) ≫ g j z n)

private theorem map_pullback_relation
    {C : Type*} [Category C] {E : Type*} [Category E]
    (F : C ⥤ E) {U V W Z : C} (a : U ⟶ W) (b : V ⟶ W)
    (g : U ⟶ Z) (h : V ⟶ Z)
    [HasPullback a b] [HasPullback (F.map a) (F.map b)]
    [PreservesLimit (cospan a b) F]
    (he : F.map (pullback.fst a b ≫ g) = F.map (pullback.snd a b ≫ h)) :
    pullback.fst (F.map a) (F.map b) ≫ F.map g =
      pullback.snd (F.map a) (F.map b) ≫ F.map h := by
  apply (cancel_epi (PreservesPullback.iso F a b).hom).mp
  simpa only [Category.assoc, PreservesPullback.iso_hom_fst_assoc,
    PreservesPullback.iso_hom_snd_assoc, ← F.map_comp] using he

private theorem pullback_map_preimage {S S' : Scheme.{u}} (q : S' ⟶ S)
    {U V : Over S} (a : U ⟶ V) (W : V.left.Opens) :
    ((Over.pullback q).map a).left ⁻¹ᵁ (pullback.fst V.hom q ⁻¹ᵁ W) =
      pullback.fst U.hom q ⁻¹ᵁ (a.left ⁻¹ᵁ W) := by
  simp only [← Scheme.Hom.comp_preimage, Over.pullback_map_left, pullback.lift_fst]

private theorem backward_preimage
    {L R U V : Scheme.{u}} (a : L ⟶ U) (b : R ⟶ V) (f : L ⟶ R) (g : R ⟶ L)
    (hg : g ≫ f = 𝟙 R) (W : U.Opens) (Z : V.Opens)
    (hf : (f ≫ b) ⁻¹ᵁ Z = a ⁻¹ᵁ W) :
    (g ≫ a) ⁻¹ᵁ W = b ⁻¹ᵁ Z := by
  have h := congrArg (fun E ↦ g ⁻¹ᵁ E) hf
  simpa only [← Scheme.Hom.comp_preimage, ← Category.assoc, hg, Category.id_comp]
    using h.symm

private theorem map_cocycle_relation
    {C : Type*} [Category C] {E : Type*} [Category E]
    [HasPullbacks C] [HasPullbacks E]
    (F : C ⥤ E) [PreservesLimitsOfShape WalkingCospan F]
    {L M N U V W : C} (a : L ⟶ U) (g : L ⟶ V) (b : M ⟶ V)
    (h : M ⟶ W) (d : N ⟶ U) (k : N ⟶ W)
    (he : F.map (pullback.fst (pullback.fst g b ≫ a) d ≫ pullback.snd g b ≫ h) =
      F.map (pullback.snd (pullback.fst g b ≫ a) d ≫ k))
    (g' : F.obj L ⟶ F.obj V) (hg' : F.map g = g') :
    pullback.fst (pullback.fst g' (F.map b) ≫ F.map a) (F.map d) ≫
        pullback.snd g' (F.map b) ≫ F.map h =
      pullback.snd (pullback.fst g' (F.map b) ≫ F.map a) (F.map d) ≫
        F.map k := by
  subst g'
  let e := (PreservesPullback.iso F g b).inv
  let s := pullback.lift
    (pullback.fst (pullback.fst (F.map g) (F.map b) ≫ F.map a) (F.map d) ≫ e)
    (pullback.snd (pullback.fst (F.map g) (F.map b) ≫ F.map a) (F.map d))
    (show _ ≫ F.map (pullback.fst g b ≫ a) = _ ≫ F.map d by
      simp only [F.map_comp, Category.assoc, e,
        PreservesPullback.iso_inv_fst_assoc]
      exact pullback.condition)
  have hh := map_pullback_relation F (pullback.fst g b ≫ a) d
    (pullback.snd g b ≫ h) k he
  have hh' := congrArg (fun v ↦ s ≫ v) hh
  simpa only [s, e, F.map_comp, Category.assoc, pullback.lift_fst_assoc,
    pullback.lift_snd_assoc, PreservesPullback.iso_inv_snd_assoc] using hh'

/-- The finite relation equalities recorded by a valid stage imply the ten explicit
piecewise gluing axioms after canonical transport. The proof expands the finite lists
of open and map relations and identifies each relation with the corresponding clause
of `HasGluingAxioms`; the backward domain clause uses the inverse identity.
Source: blueprint node `lemma-nagata-relative-gluing-axioms-eventually`, proof steps 3--4.
(blueprint: lemma-nagata-relative-gluing-axioms-eventually).
-/
private theorem nagataRelativeGluingAxioms_of_relations
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (D : Iᵒᵖ ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ {i j : Iᵒᵖ} (t : i ⟶ j), IsAffineHom (D.map t)]
    (i₀ : I) [CompactSpace (D.obj (op i₀))] [QuasiSeparatedSpace (D.obj (op i₀))]
    {X : Scheme.{u}} (f : X ⟶ c.pt)
    [CompactSpace c.pt] [QuasiSeparatedSpace c.pt]
    [LocallyOfFinitePresentation f] [QuasiCompact f] [QuasiSeparated f]
    (R : NagataRelativeGluingDatum D c hc i₀ f)
    (P : NagataRelativeRawInclusions D c hc i₀ f R)
    (A : NagataRelativeGluingValidStageData D c hc i₀ f R P)
    (hopen : ∀ e ∈ nagataRelativeOpenRelations D c hc i₀ f R P,
      pullback.fst e.source.hom
          (D.map (homOfLE (nagataRelativeRawStage_le_validStage
            D c hc i₀ f R P A)).op) ⁻¹ᵁ e.first =
        pullback.fst e.source.hom
          (D.map (homOfLE (nagataRelativeRawStage_le_validStage
            D c hc i₀ f R P A)).op) ⁻¹ᵁ e.second)
    (hmap : ∀ e ∈ nagataRelativeMapRelations D c hc i₀ f R P,
      (Over.pullback (D.map (homOfLE
        (nagataRelativeRawStage_le_validStage D c hc i₀ f R P A)).op)).map e.phi =
        (Over.pullback (D.map (homOfLE
          (nagataRelativeRawStage_le_validStage D c hc i₀ f R P A)).op)).map e.psi) :
    (nagataRelativeGluingValidDatum D c hc i₀ f R P A).HasGluingAxioms := by
  classical
  simp only [nagataRelativeMapRelations, List.mem_append, List.mem_flatMap,
    List.mem_map, List.mem_cons, List.not_mem_nil, or_false,
    Finset.mem_toList, Finset.mem_univ, true_and] at hmap
  simp only [nagataRelativeOpenRelations, List.mem_append, List.mem_flatMap,
    List.mem_map, Finset.mem_toList, Finset.mem_univ, true_and] at hopen
  let ht := nagataRelativeRawStage_le_validStage D c hc i₀ f R P A
  let q := D.map (homOfLE ht).op
  let F := Over.pullback q
  let T := nagataRelativeGluingValidDatum D c hc i₀ f R P A
  have hinv : ∀ j k l, T.forward j k l ≫ T.backward j k l = 𝟙 _ ∧
      T.backward j k l ≫ T.forward j k l = 𝟙 _ := by
    intro j k l
    dsimp only [T, nagataRelativeGluingValidDatum, nagataRelativeGluingAtStage]
    constructor
    · have h := hmap _ (Or.inl (Or.inl ⟨j, k, l, Or.inl (Or.inl (Or.inl rfl))⟩))
      change F.map (_ ≫ _) = F.map (𝟙 _) at h
      rw [F.map_comp, F.map_id] at h
      exact h
    · have h := hmap _ (Or.inl (Or.inl ⟨j, k, l, Or.inl (Or.inl (Or.inr rfl))⟩))
      change F.map (_ ≫ _) = F.map (𝟙 _) at h
      rw [F.map_comp, F.map_id] at h
      exact h
  have hforward : ∀ j k z l,
      (T.forward j k l ≫ T.rightInclusion j k l).left ⁻¹ᵁ
          (⨆ m, T.leftOpen k z m) =
        (T.leftInclusion j k l).left ⁻¹ᵁ (⨆ m, T.leftOpen j z m) := by
    intro j k z l
    dsimp only [T, nagataRelativeGluingValidDatum, nagataRelativeGluingAtStage]
    have h := hopen _ (Or.inr ⟨j, k, z, l, rfl⟩)
    dsimp only at h
    simp only [← Scheme.Hom.preimage_iSup]
    rw [← Functor.map_comp]
    change (F.map (nagataRelativeForwardToChart D c hc i₀ f R P j k l)).left ⁻¹ᵁ
        (pullback.fst (nagataRelativeRawChart D c hc i₀ f R k).hom q ⁻¹ᵁ
          (⨆ m, R.raw.rawLeftOpen k z m)) =
      (F.map (P.left j k l)).left ⁻¹ᵁ
        (pullback.fst (nagataRelativeRawChart D c hc i₀ f R j).hom q ⁻¹ᵁ
          (⨆ m, R.raw.rawLeftOpen j z m))
    simpa only [F, pullback_map_preimage] using h
  change T.HasGluingAxioms
  refine ⟨?_, ?_, hforward, ?_, hinv, ?_, ?_, ?_, ?_, ?_⟩ <;>
    dsimp only [T, nagataRelativeGluingValidDatum, nagataRelativeGluingAtStage]
  · intro j
    have h := hopen _ (Or.inl (Or.inl ⟨j, rfl⟩))
    simpa only [Scheme.Hom.preimage_iSup, Scheme.Hom.preimage_top] using h
  · intro j k
    have h := hopen _ (Or.inl (Or.inr ⟨j, k, rfl⟩))
    simpa only [Scheme.Hom.preimage_iSup] using h
  · intro j k z l
    have hi := congrArg (fun m ↦ m.left) (hinv j k l).2
    have hf := hforward j k z l
    simp only [Over.comp_left, Over.id_left] at hi hf
    exact backward_preimage _ _ _ _ hi _ _ hf
  · intro j k l m
    have h := hmap _ (Or.inl (Or.inl ⟨j, k, l, Or.inl (Or.inr ⟨m, Or.inl rfl⟩)⟩))
    simpa only [F, nagataRelativeForwardToChart, Functor.map_comp] using
      map_pullback_relation F (P.left j k l) (P.left j k m)
        (nagataRelativeForwardToChart D c hc i₀ f R P j k l)
        (nagataRelativeForwardToChart D c hc i₀ f R P j k m) h
  · intro j k l m
    have h := hmap _ (Or.inl (Or.inl ⟨j, k, l, Or.inl (Or.inr ⟨m, Or.inr rfl⟩)⟩))
    simpa only [F, nagataRelativeBackwardToChart, Functor.map_comp] using
      map_pullback_relation F (P.right j k l) (P.right j k m)
        (nagataRelativeBackwardToChart D c hc i₀ f R P j k l)
        (nagataRelativeBackwardToChart D c hc i₀ f R P j k m) h
  · intro j k l m
    have h := hmap _ (Or.inl (Or.inl ⟨j, k, l, Or.inr ⟨m, rfl⟩⟩))
    simpa only [F, nagataRelativeForwardToChart, nagataRelativeBackwardToChart,
      Functor.map_comp] using
      map_pullback_relation F (P.left j k l) (P.right k j m)
        (nagataRelativeForwardToChart D c hc i₀ f R P j k l)
        (nagataRelativeBackwardToChart D c hc i₀ f R P k j m) h
  · intro j l
    have h := hmap _ (Or.inl (Or.inr ⟨j, l, rfl⟩))
    simpa only [nagataRelativeForwardToChart, Functor.map_comp] using h.symm
  · intro j k z l m n
    have h := hmap _ (Or.inr ⟨j, k, z, l, m, n, rfl⟩)
    have hh := map_cocycle_relation F (P.left j k l)
        (nagataRelativeForwardToChart D c hc i₀ f R P j k l) (P.left k z m)
        (nagataRelativeForwardToChart D c hc i₀ f R P k z m) (P.left j z n)
        (nagataRelativeForwardToChart D c hc i₀ f R P j z n) h
        (F.map (R.raw.forwardRaw j k l).map ≫ F.map (P.right j k l))
        (F.map_comp _ _)
    simpa only [nagataRelativeForwardToChart, Functor.map_comp] using hh

/-- The named datum at lambda_rel satisfies all relative gluing axioms.
Source: blueprint node order 361
(blueprint: lemma-nagata-relative-gluing-axioms-eventually).

Proof:
1. Fix the raw datum, canonical inclusions, and equality choices of
   `def-nagata-relative-gluing-valid-stage`. By
   `lemma-nagata-relative-gluing-datum-descends`, its charts and both directions of
   its overlap maps pull back to the finite affine presentation of
   `def-nagata-relative-finite-affine-presentation`. That presentation satisfies
   the gluing equations. Canonical common domains are identified by their chart
   and base projections, using the fibre-product universal property. The retained
   compactness, finite-presentation and limit-equality inputs apply to these equations.
2. Apply `lemma-nagata-directed-finite-upper-bound` to the finite set containing
   the raw stage and every selected open- and map-equality stage. Hence every
   witness stage is below the very same selected lambda_rel.
3. Apply `lemma-nagata-qc-open-eq-eventually` to each listed open equation at
   lambda_rel. This gives diagonal coverage, reversed-orientation coverage, and
   forward domain matching. Functorial inverse images identify these opens with
   those of `nagataRelativeGluingValidDatum`.
4. Apply `lemma-nagata-morphism-eq-eventually` to each listed parallel-map
   equation at lambda_rel. Functorial pullback and its canonical identifications
   give both inverse identities, both piecewise agreement equations, orientation
   agreement, the diagonal identity and every triple cocycle. For backward domain
   matching, cover each right piece by its intersections with the reversed left
   pieces, using reversed-orientation coverage. On each intersection orientation
   agreement identifies the backward map with the reversed forward map, whose
   domain matching was proved in step 3. Equality of opens is local on this cover.
   No glued scheme or finite-stage gluing hypothesis is used. -/
theorem nagataRelativeGluingAxiomsEventually
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (D : Iᵒᵖ ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ {i j : Iᵒᵖ} (t : i ⟶ j), IsAffineHom (D.map t)]
    (i₀ : I) [CompactSpace (D.obj (op i₀))] [QuasiSeparatedSpace (D.obj (op i₀))]
    {X : Scheme.{u}} (f : X ⟶ c.pt)
    [CompactSpace c.pt] [QuasiSeparatedSpace c.pt]
    [LocallyOfFinitePresentation f] [QuasiCompact f] [QuasiSeparated f]
    (R : NagataRelativeGluingDatum D c hc i₀ f)
    (P : NagataRelativeRawInclusions D c hc i₀ f R)
    (A : NagataRelativeGluingValidStageData D c hc i₀ f R P) :
    (nagataRelativeGluingValidDatum D c hc i₀ f R P A).HasGluingAxioms := by
  classical
  let t := nagataRelativeGluingValidStage D c hc i₀ f R P A
  let ht := nagataRelativeRawStage_le_validStage D c hc i₀ f R P A
  let q := D.map (homOfLE ht).op
  let F := Over.pullback q
  have open_eq (n : Fin (nagataRelativeOpenRelations D c hc i₀ f R P).length) :
      let e := (nagataRelativeOpenRelations D c hc i₀ f R P).get n
      pullback.fst e.source.hom q ⁻¹ᵁ e.first =
        pullback.fst e.source.hom q ⁻¹ᵁ e.second := by
    let e := (nagataRelativeOpenRelations D c hc i₀ f R P).get n
    let a := A.opens n
    let := a.compactSource
    let := a.qsSource
    apply nagataQCOpenEqEventually D c hc R.raw.stage e.source.hom e.first e.second
      a.compactFirst a.compactSecond a.limit_eq R.base.boundPair R.base.boundPair_le
      R.base.boundOrder t ht
    apply le_directedFiniteUpperBound i₀ R.base.boundPair R.base.boundPair_le
      R.base.boundOrder
    simp only [nagataRelativeGluingEqualityStages, Finset.mem_insert, Finset.mem_union]
    exact Or.inr (Or.inl (Finset.mem_image.mpr ⟨n, Finset.mem_univ _, rfl⟩))
  have map_eq (n : Fin (nagataRelativeMapRelations D c hc i₀ f R P).length) :
      let e := (nagataRelativeMapRelations D c hc i₀ f R P).get n
      (F.map e.phi).left = (F.map e.psi).left := by
    let e := (nagataRelativeMapRelations D c hc i₀ f R P).get n
    let a := A.maps n
    let := a.compactBase
    let := a.qsBase
    let := a.compactSource
    let := a.qsSource
    let := a.lfpSource
    let := a.qcSource
    let := a.qsSourceMap
    let := a.lfpTarget
    let := a.qcTarget
    let := a.qsTargetMap
    have h := nagataMorphismEqEventually a.choice t ht
    apply h
    apply le_directedFiniteUpperBound i₀ R.base.boundPair R.base.boundPair_le
      R.base.boundOrder
    simp only [nagataRelativeGluingEqualityStages, Finset.mem_insert, Finset.mem_union]
    exact Or.inr (Or.inr (Finset.mem_image.mpr ⟨n, Finset.mem_univ _, rfl⟩))
  have opens (e : NagataRelativeOpenRelation (D.obj (op R.raw.stage)))
      (he : e ∈ nagataRelativeOpenRelations D c hc i₀ f R P) :
      pullback.fst e.source.hom q ⁻¹ᵁ e.first =
        pullback.fst e.source.hom q ⁻¹ᵁ e.second := by
    obtain ⟨n, hn⟩ := List.mem_iff_get.mp he
    subst e
    exact open_eq n
  have maps (e : NagataRelativeMapRelation (D.obj (op R.raw.stage)))
      (he : e ∈ nagataRelativeMapRelations D c hc i₀ f R P) :
      F.map e.phi = F.map e.psi := by
    obtain ⟨n, hn⟩ := List.mem_iff_get.mp he
    subst e
    ext
    exact map_eq n
  apply nagataRelativeGluingAxioms_of_relations D c hc i₀ f R P A
  · exact opens
  · exact maps

end AlgebraicGeometry
