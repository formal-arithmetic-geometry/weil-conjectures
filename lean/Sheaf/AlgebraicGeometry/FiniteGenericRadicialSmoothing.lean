/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group ND
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyInjective
public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
import Sheaf.AlgebraicGeometry.GenericGeometricallyReducedPreparation
import WeilConjectures.AlgebraicGeometry.Morphisms.SlicingFlat
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Sheaf.Topology.IrreducibleOpenComplementDimension
import WeilConjectures.AlgebraicGeometry.EtaleSetInverseImageRestriction
import WeilConjectures.ConstructibleSheaf.GenericConstancy

/-! # Generic smoothing after a finite radicial base change

Source: blueprint sec-smooth-purity/sk-prop-sf-cbc,
lem-fin-generic-radicial-smoothing (blueprint: lem-fin-generic-radicial-smoothing).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

-- Flatness makes every nonempty open meet the generic fibre. Lift a smooth fibre point.
private theorem dense_smoothLocus_of_generic_fibre {Y T : Scheme.{u}}
    (g : Y ⟶ T) [Flat g] [LocallyOfFinitePresentation g]
    (η : T) (hη : IsGenericPoint η Set.univ)
    [GeometricallyReduced (g.fiberToSpecResidueField η)] :
    Dense (g.smoothLocus : Set Y) := by
  refine dense_iff_inter_open.mpr ?_
  intro O hO hOne
  have hηO : η ∈ g '' O := (hη.mem_open_set_iff (g.isOpenMap O hO)).mpr
    (by simpa using hOne.image g)
  obtain ⟨x, hxO, hxη⟩ := hηO
  obtain ⟨w, hw⟩ := (g.range_fiberι η).symm.subset hxη
  let W : (g.fiber η).Opens := ⟨g.fiberι η ⁻¹' O, hO.preimage (g.fiberι η).continuous⟩
  obtain ⟨z, hzO, hzs⟩ :=
    (GeometricallyReduced.dense_smoothLocus (g.fiberToSpecResidueField η)).inter_open_nonempty
      W W.isOpen ⟨w, by change g.fiberι η w ∈ O; rwa [hw]⟩
  exact ⟨g.fiberι η z, hzO, g.fiberι_mem_smoothLocus hzs⟩

-- Compare an arbitrary subspace of the complement with each containing component.
private theorem dimension_lt_of_dense_open
    {A B D : Type u} [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace D]
    [TopologicalSpace.NoetherianSpace A] (i : B → A) (hi : IsHomeomorph i)
    (V : TopologicalSpace.Opens B) (hV : Dense (V : Set B))
    (d : ℕ) (hd : topologicalKrullDim A ≤ (d : WithBot ℕ∞))
    (C : Set A) (hC : C ∈ irreducibleComponents A)
    (a : D → B) (ha : Topology.IsInducing a)
    (hCa : ∀ z, i (a z) ∈ C) (hVa : ∀ z, a z ∉ V) :
    topologicalKrullDim D < topologicalKrullDim C := by
  let W : TopologicalSpace.Opens A := ⟨i '' (V : Set B), hi.isOpenMap _ V.isOpen⟩
  have hW : Dense (W : Set A) := by
    intro x
    obtain ⟨y, rfl⟩ := hi.surjective x
    exact (hi.isInducing.dense_iff.mp hV) y
  obtain ⟨O, hOo, hOne, hOC⟩ :=
    TopologicalSpace.NoetherianSpace.exists_isOpen_nonempty_subset_irreducibleComponent C hC
  obtain ⟨x, hxO, hxW⟩ := hW.inter_open_nonempty O hOo hOne
  let U : TopologicalSpace.Opens C := ⟨Subtype.val ⁻¹' (W : Set A),
    W.isOpen.preimage continuous_subtype_val⟩
  have hU : U ≠ ⊥ := U.ne_bot_iff_nonempty.mpr ⟨⟨x, hOC hxO⟩, hxW⟩
  have : IrreducibleSpace C := isIrreducible_iff_irreducibleSpace.mp hC.1
  have hCdim := (topologicalKrullDim_subspace_le A C).trans hd
  have hne : topologicalKrullDim C ≠ ⊥ := by
    intro heq
    have hzero : (0 : WithBot ℕ∞) ≤ topologicalKrullDim C :=
      Order.LTSeries.length_le_krullDim (.singleton _
        ⟨Set.univ, IrreducibleSpace.isIrreducible_univ C, isClosed_univ⟩)
    simp [heq] at hzero
  obtain ⟨e, he⟩ := WithBot.ne_bot_iff_exists.mp hne
  have hefin : e ≠ ⊤ := by
    have he' : e ≤ (d : ℕ∞) := by exact_mod_cast (he ▸ hCdim)
    exact ne_top_of_le_ne_top (ENat.natCast_ne_top d) he'
  obtain ⟨n, rfl⟩ := ENat.ne_top_iff_exists.mp hefin
  have hdim : topologicalKrullDim C = (n : WithBot ℕ∞) := he.symm
  let b : D → ↥((U : Set C)ᶜ) := fun z ↦ ⟨⟨i (a z), hCa z⟩, by
    rintro ⟨y, hy, heq⟩
    exact hVa z (hi.injective heq ▸ hy)⟩
  have hb : Topology.IsInducing b := by
    apply Topology.IsInducing.of_comp (g :=
      (Subtype.val : C → A) ∘ (Subtype.val : ↥((U : Set C)ᶜ) → C))
    · exact (hi.continuous.comp ha.continuous).subtype_mk _ |>.subtype_mk _
    · exact continuous_subtype_val.comp continuous_subtype_val
    · exact hi.isInducing.comp ha
  rcases irreducible_open_complement_dimension C n hdim.le U hU with h | ⟨m, hmn, hm⟩
  · have : IsEmpty (TopologicalSpace.IrreducibleCloseds D) := ⟨fun c ↦ by
      obtain ⟨z, _⟩ := c.isIrreducible.nonempty
      exact h.false (b z)⟩
    rw [topologicalKrullDim, Order.krullDim_eq_bot, hdim]
    exact WithBot.bot_lt_coe _
  · exact (hb.topologicalKrullDim_le.trans hm).trans_lt (by rw [hdim]; exact_mod_cast hmn)

private theorem sets_constant_over_iff {Y : Scheme.{u}} (U : Y.Etale)
    (F : Sheaf Y.smallEtaleTopology (Type (u + 1))) :
    (F.over U).IsConstant (Y.smallEtaleTopology.over U) ↔
      ((Scheme.etaleSetPullback U.hom).obj F).IsConstant U.left.smallEtaleTopology := by
  obtain ⟨ρ, _⟩ := etaleSetInverseImageRestriction U.hom
  let e : (Scheme.Etale.overSheafEquiv U (Type (u + 1))).functor.obj (F.over U) ≅
      (Scheme.etaleSetPullback U.hom).obj F :=
    (fullyFaithfulSheafToPresheaf _ _).preimageIso
      (X := (Scheme.Etale.overSheafEquiv U (Type (u + 1))).functor.obj (F.over U))
      (Y := (Etale.localizationRestriction (Type (u + 1)) U.hom U.prop).obj F)
      (Functor.isoWhiskerRight
        (NatIso.op (Scheme.Etale.etaleToOverCompForgetIso U).symm) F.obj) ≪≫ (ρ.app F).symm
  rw [← Sheaf.isConstant_sheafCongr_functor_iff
    (J := Y.smallEtaleTopology.over U) (K := U.left.smallEtaleTopology)
    (Scheme.Etale.overEquiv U) CategoryTheory.Over.mkIdTerminal (F.over U)]
  constructor
  · intro h
    have : Sheaf.IsConstant U.left.smallEtaleTopology
        ((Scheme.Etale.overSheafEquiv U (Type (u + 1))).functor.obj (F.over U)) := h
    exact Sheaf.isConstant_congr _ e
  · intro h
    have := h
    exact Sheaf.isConstant_congr _ e.symm

private theorem sets_constant_pullback {Y Z : Scheme.{u}} (a : Z ⟶ Y)
    (F : Sheaf Y.smallEtaleTopology (Type (u + 1)))
    [F.IsConstant Y.smallEtaleTopology] :
    ((Scheme.etaleSetPullback a).obj F).IsConstant Z.smallEtaleTopology := by
  have h := Sheaf.isConstant_sheafPullback a.Etale (K := Z.smallEtaleTopology)
    terminalIsTerminal (terminalIsTerminal.isTerminalObj a.Etale) F
  exact Sheaf.isConstant_congr _
    ((Functor.sheafPullbackConstruction.sheafPullbackIso a.Etale (Type (u + 1))
      Y.smallEtaleTopology Z.smallEtaleTopology).app F)

private theorem sets_locallyConstant_iso {Y : Scheme.{u}}
    {F G : Sheaf Y.smallEtaleTopology (Type (u + 1))} (e : F ≅ G)
    (hF : Scheme.IsLocallyConstantEtaleSheafOfSets F) :
    Scheme.IsLocallyConstantEtaleSheafOfSets G := by
  obtain ⟨𝒰, h𝒰⟩ := hF
  refine ⟨𝒰, fun i ↦ ?_⟩
  have := h𝒰 i
  exact Sheaf.isConstant_congr _ ((Y.smallEtaleTopology.overPullback _ _).mapIso e)

private theorem sets_locallyConstant_pullback {Y Z : Scheme.{u}} (a : Z ⟶ Y)
    (F : Sheaf Y.smallEtaleTopology (Type (u + 1)))
    (hF : Scheme.IsLocallyConstantEtaleSheafOfSets F) :
    Scheme.IsLocallyConstantEtaleSheafOfSets ((Scheme.etaleSetPullback a).obj F) := by
  classical
  obtain ⟨𝒰, h𝒰⟩ := hF
  obtain ⟨c, _⟩ := etaleSetInverseImageCompositionUnits.2.2
  have : Scheme.etalePrecoverage.IsStableUnderBaseChange :=
    inferInstanceAs (Scheme.precoverage @Etale).IsStableUnderBaseChange
  refine ⟨𝒰.pullback₂ a, fun j ↦ ?_⟩
  apply (sets_constant_over_iff _ _).mpr
  have h₁ : ((Scheme.etaleSetPullback (𝒰.f j)).obj F).IsConstant
      (𝒰.X j).smallEtaleTopology :=
    (sets_constant_over_iff (𝒰.etalePrecoverageToEtale j) F).mp (h𝒰 j)
  have h₂ := sets_constant_pullback (pullback.fst (𝒰.f j) a)
    ((Scheme.etaleSetPullback (𝒰.f j)).obj F)
  have : ((Scheme.etaleSetPullback (pullback.fst (𝒰.f j) a)).obj
      ((Scheme.etaleSetPullback (𝒰.f j)).obj F)).IsConstant
      (Scheme.Cover.etalePrecoverageToEtale (𝒰.pullback₂ a) j).left.smallEtaleTopology := h₂
  let e : (Scheme.etaleSetPullback (pullback.fst (𝒰.f j) a)).obj
      ((Scheme.etaleSetPullback (𝒰.f j)).obj F) ≅
      (Scheme.etaleSetPullback (pullback.snd (𝒰.f j) a)).obj
        ((Scheme.etaleSetPullback a).obj F) :=
    (c Y (𝒰.X j) _ (𝒰.f j) (pullback.fst (𝒰.f j) a)).app F ≪≫
      eqToIso (congrArg (fun m ↦ (Scheme.etaleSetPullback m).obj F) pullback.condition) ≪≫
      ((c Y Z _ a (pullback.snd (𝒰.f j) a)).app F).symm
  exact Sheaf.isConstant_congr _ e

private theorem sets_locallyConstant_of_cover {Y : Scheme.{u}}
    (𝒰 : Scheme.Cover.{u} Scheme.etalePrecoverage Y)
    (F : Sheaf Y.smallEtaleTopology (Type (u + 1)))
    (h : ∀ i, Scheme.IsLocallyConstantEtaleSheafOfSets
      ((Scheme.etaleSetPullback (𝒰.f i)).obj F)) :
    Scheme.IsLocallyConstantEtaleSheafOfSets F := by
  classical
  choose 𝒱 h𝒱 using h
  obtain ⟨c, _⟩ := etaleSetInverseImageCompositionUnits.2.2
  have : Scheme.etalePrecoverage.IsStableUnderComposition :=
    inferInstanceAs (Scheme.precoverage @Etale).IsStableUnderComposition
  refine ⟨𝒰.bind 𝒱, fun ⟨i, j⟩ ↦ ?_⟩
  apply (sets_constant_over_iff _ _).mpr
  have h₁ := (sets_constant_over_iff ((𝒱 i).etalePrecoverageToEtale j) _).mp (h𝒱 i j)
  have : ((Scheme.etaleSetPullback (𝒰.f i) ⋙
      Scheme.etaleSetPullback ((𝒱 i).f j)).obj F).IsConstant
      (Scheme.Cover.etalePrecoverageToEtale (𝒰.bind 𝒱) ⟨i, j⟩).left.smallEtaleTopology := h₁
  exact Sheaf.isConstant_congr _
    ((c Y (𝒰.X i) ((𝒱 i).X j) (𝒰.f i) ((𝒱 i).f j)).app F)

-- Over a reduced source, the surjective immersion obtained by pulling back a stratum
-- is an isomorphism; this supplies an actual factorization through the stratum.
private theorem sets_locallyConstant_range_subset
    {Y Z R : Scheme.{u}} [IsReduced Z] (a : Z ⟶ Y) (b : R ⟶ Y) [IsImmersion b]
    (hr : Set.range a ⊆ Set.range b)
    (F : Sheaf Y.smallEtaleTopology (Type (u + 1)))
    (hF : Scheme.IsLocallyConstantEtaleSheafOfSets ((Scheme.etaleSetPullback b).obj F)) :
    Scheme.IsLocallyConstantEtaleSheafOfSets ((Scheme.etaleSetPullback a).obj F) := by
  have : Surjective (pullback.fst a b) := Scheme.surjective_pullback_fst_of_range_subset a b hr
  have : IsClosedImmersion (pullback.fst a b) :=
    IsClosedImmersion.of_isImmersion_of_surjective _
  have : IsIso (pullback.fst a b) := isIso_of_isClosedImmersion_of_surjective _
  let c : Z ⟶ R := inv (pullback.fst a b) ≫ pullback.snd a b
  have hc : c ≫ b = a := by simp [c, ← pullback.condition]
  have h := sets_locallyConstant_pullback c ((Scheme.etaleSetPullback b).obj F) hF
  obtain ⟨comp, _⟩ := etaleSetInverseImageCompositionUnits.2.2
  apply sets_locallyConstant_iso ((comp Y R Z b c).app F ≪≫
    eqToIso (congrArg (fun m ↦ (Scheme.etaleSetPullback m).obj F) hc)) h

-- The interiors of a finite stratification are dense, including on an empty scheme.
private theorem sets_generic_constancy {Y Z : Scheme.{u}} [IsReduced Z]
    (a : Z ⟶ Y) (F : Sheaf Y.smallEtaleTopology (Type (u + 1)))
    (hF : Scheme.IsConstructibleEtaleSheafOfSets F) :
    ∃ W : Z.Opens, Dense (W : Set Z) ∧
      Scheme.IsLocallyConstantEtaleSheafOfSets ((Scheme.etaleSetPullback (W.ι ≫ a)).obj F) := by
  classical
  obtain ⟨S, hS⟩ := hF
  let T := S.pullback a
  let W := T.interiorUnion
  let G := (Scheme.etaleSetPullback (W.ι ≫ a)).obj F
  refine ⟨W, T.dense_interiorUnion, ?_⟩
  let 𝒰 : Scheme.Cover.{u} Scheme.etalePrecoverage W.toScheme :=
    T.interiorUnionCover.changeProp (Q := @Etale) fun _ ↦ inferInstance
  apply sets_locallyConstant_of_cover 𝒰 G
  intro j
  have hr : Set.range ((T.interiorOpens j.down).ι ≫ a) ⊆ Set.range (S.immersion j.down) := by
    rintro _ ⟨z, rfl⟩
    rw [S.range_immersion]
    have hz : z.1 ∈ T.stratum j.down := interior_subset z.2
    exact hz
  have hl := sets_locallyConstant_range_subset ((T.interiorOpens j.down).ι ≫ a)
    (S.immersion j.down) hr F (hS j.down).1
  obtain ⟨comp, _⟩ := etaleSetInverseImageCompositionUnits.2.2
  have heq : 𝒰.f j ≫ (W.ι ≫ a) = (T.interiorOpens j.down).ι ≫ a := by
    rw [← Category.assoc]
    congr 1
    exact Scheme.homOfLE_ι Z (le_iSup T.interiorOpens j.down)
  exact sets_locallyConstant_iso
    (eqToIso (congrArg (fun m ↦ (Scheme.etaleSetPullback m).obj F) heq.symm) ≪≫
      ((comp Y W.toScheme _ (W.ι ≫ a) (𝒰.f j)).app F).symm) hl

/-- After shrinking an integral finite type base over a field, a finite radicial
surjection makes the reduced pullback admit a dense smooth open. An optional
constructible finite sheaf becomes locally constant there. The parameter `none`
expresses the assertion without a sheaf, and `some F` its sheaf refinement.
The complement in the generic fibre is written using the subspace of points over
its generic point; `Scheme.Hom.fiberHomeo` identifies this with the scheme fibre.
Its components are compared with every containing component of the unreduced pullback.

Source: blueprint sec-smooth-purity/sk-prop-sf-cbc,
lem-fin-generic-radicial-smoothing (blueprint: lem-fin-generic-radicial-smoothing).

Proof:
1. Apply lem-pur-generic-geometrically-reduced-preparation (Stacks 0550).
The resulting finite universal homeomorphism is surjective and universally injective.
2. The geometrically reduced generic fibre has dense smooth locus. Flat local finite
presentation makes the morphism open, so every nonempty open meets that generic fibre.
Lift its smooth points using `Scheme.Hom.fiberι_mem_smoothLocus` to obtain density of
`g.smoothLocus` on the total reduced pullback.
3. For the optional sheaf, pull back its finite stratification and take the union of
the interiors. This is dense by `Stratification.dense_interiorUnion`. Each interior
is reduced, so the surjective immersion obtained by pulling back its original stratum
is an isomorphism. This factors the interior through the original stratum, where the
sheaf is locally constant. Inverse-image composition and restriction comparisons
transport the constant trivializations and compose their étale covers. Intersect this
dense open with the smooth locus. Without a sheaf keep the smooth locus.
4. The unreduced pullback is Noetherian and finite dimensional, by finite type over
the original field. Reduction gives a homeomorphism. Every component contains a
nonempty ambient open, so the dense open meets that component in a nonempty open.
Apply `irreducible_open_complement_dimension` to that open in the component.
5. The set Z in the assertion embeds into this component's closed complement, so its
dimension is bounded by the complement's dimension and is strictly smaller than that
of the component. The empty-complement branch forces Z to be empty and has dimension
bottom. This argument works for any such subspace Z, so the component and genericity
hypotheses on Z are unnecessary for the comparison itself. -/
theorem exists_finite_generic_radicial_smoothing
    (k : Type u) [Field k] (S : Scheme.{u}) [IsIntegral S]
    [S.Over (Spec (.of k))]
    [LocallyOfFiniteType (S ↘ Spec (.of k))] [QuasiCompact (S ↘ Spec (.of k))]
    (X : Scheme.{u}) (f : X ⟶ S) [LocallyOfFiniteType f] [QuasiCompact f]
    [Nonempty X]
    (F : Option (Sheaf X.smallEtaleTopology (Type (u + 1))))
    (hF : ∀ E ∈ F, Scheme.IsConstructibleEtaleSheafOfSets E) :
    ∃ U : S.Opens, (U : Set S).Nonempty ∧
      ∃ (T : Scheme.{u}) (q : T ⟶ U.toScheme),
        IsFinite q ∧ UniversallyInjective q ∧ Surjective q ∧
        ∃ V : (pullback f (q ≫ U.ι)).nilradical.subscheme.Opens,
          Dense (V : Set (pullback f (q ≫ U.ι)).nilradical.subscheme) ∧
          Smooth (V.ι ≫ (pullback f (q ≫ U.ι)).nilradical.subschemeι ≫
            pullback.snd f (q ≫ U.ι)) ∧
          (∀ E ∈ F, Scheme.IsLocallyConstantEtaleSheafOfSets
            ((Scheme.etaleSetPullback
              (V.ι ≫ (pullback f (q ≫ U.ι)).nilradical.subschemeι ≫
                pullback.fst f (q ≫ U.ι))).obj E)) ∧
          ∀ η : T, IsGenericPoint η Set.univ →
            ∀ Z : Set {y : (pullback f (q ≫ U.ι)).nilradical.subscheme |
              ((pullback f (q ≫ U.ι)).nilradical.subschemeι ≫
                pullback.snd f (q ≫ U.ι)) y = η ∧ y ∉ V},
              Z ∈ irreducibleComponents _ →
              ∀ (C : Set ↥(pullback f (q ≫ U.ι))),
                C ∈ irreducibleComponents ↥(pullback f (q ≫ U.ι)) →
                (∀ z ∈ Z, (pullback f (q ≫ U.ι)).nilradical.subschemeι z.1 ∈ C) →
                topologicalKrullDim Z < topologicalKrullDim C := by
  classical
  obtain ⟨U, hU, T, hTi, hTa, q, hqf, hqh, hgflat, hglfp, hgqc, hgqs, hggeom⟩ :=
    exists_generic_geometricallyReduced_preparation f
  have : IsIntegral T := hTi
  have : IsAffine T := hTa
  have : IsFinite q := hqf
  have : UniversallyInjective q := ⟨fun _ _ _ _ _ h ↦ (hqh _ _ _ h).injective⟩
  have : Surjective q := ⟨(hqh _ _ _ IsPullback.of_id_snd).surjective⟩
  let P := pullback f (q ≫ U.ι)
  let Y := P.nilradical.subscheme
  let r : Y ⟶ P := P.nilradical.subschemeι
  let g : Y ⟶ T := r ≫ pullback.snd f (q ≫ U.ι)
  let a : Y ⟶ X := r ≫ pullback.fst f (q ≫ U.ι)
  have : Flat g := hgflat
  have : LocallyOfFinitePresentation g := hglfp
  have : QuasiCompact g := hgqc
  have : QuasiSeparated g := hgqs
  have : GeometricallyReduced (g.fiberToSpecResidueField (genericPoint T)) :=
    hggeom _ (genericPoint_spec T)
  have hdense := dense_smoothLocus_of_generic_fibre g (genericPoint T) (genericPoint_spec T)
  have hVl : ∃ V : Y.Opens, Dense (V : Set Y) ∧ Smooth (V.ι ≫ g) ∧
      ∀ E ∈ F, Scheme.IsLocallyConstantEtaleSheafOfSets
        ((Scheme.etaleSetPullback (V.ι ≫ a)).obj E) := by
    have hsmooth (V : Y.Opens) (hV : V ≤ g.smoothLocus) : Smooth (V.ι ≫ g) := by
      rw [← Scheme.Hom.smoothLocus_eq_top_iff, ← Scheme.Hom.preimage_smoothLocus_eq]
      exact top_le_iff.mp (fun x _ ↦ hV x.2)
    cases F with
    | none =>
      refine ⟨g.smoothLocus, hdense, hsmooth _ le_rfl, ?_⟩
      simp
    | some E =>
      obtain ⟨W, hWd, hWl⟩ := sets_generic_constancy a E (hF E (by simp))
      let V := g.smoothLocus ⊓ W
      refine ⟨V, hdense.inter_of_isOpen_left hWd g.smoothLocus.isOpen,
        hsmooth _ inf_le_left, ?_⟩
      intro E' hE'
      have heq : E = E' := by simpa using hE'
      subst E'
      have hl := sets_locallyConstant_pullback (Y.homOfLE (show V ≤ W from inf_le_right))
        ((Scheme.etaleSetPullback (W.ι ≫ a)).obj E) hWl
      obtain ⟨comp, _⟩ := etaleSetInverseImageCompositionUnits.2.2
      apply sets_locallyConstant_iso
        ((comp X W.toScheme V.toScheme (W.ι ≫ a) (Y.homOfLE inf_le_right)).app E ≪≫
          eqToIso (congrArg (fun m ↦ (Scheme.etaleSetPullback m).obj E) ?_)) hl
      rw [← Category.assoc, Scheme.homOfLE_ι]
  obtain ⟨V, hVd, hVs, hVf⟩ := hVl
  refine ⟨U, hU, T, q, hqf, inferInstance, inferInstance, V, hVd, hVs, hVf, ?_⟩
  intro η _ Z _ C hC hZC
  have : IsLocallyNoetherian S :=
    LocallyOfFiniteType.isLocallyNoetherian (S ↘ Spec (.of k))
  have : IsLocallyNoetherian T := LocallyOfFiniteType.isLocallyNoetherian (q ≫ U.ι)
  have : IsLocallyNoetherian P :=
    LocallyOfFiniteType.isLocallyNoetherian (pullback.snd f (q ≫ U.ι))
  have : CompactSpace P := inferInstance
  have : IsNoetherian P := ⟨⟩
  let p : P ⟶ Spec (.of k) := pullback.snd f (q ≫ U.ι) ≫ q ≫ U.ι ≫
    (S ↘ Spec (.of k))
  obtain ⟨d, hd⟩ := exists_topologicalKrullDim_le p
  have hrs : Surjective r := by
    constructor
    rw [← Set.range_eq_univ]
    change Set.range P.nilradical.subschemeι = Set.univ
    rw [Scheme.IdealSheafData.range_subschemeι, Scheme.support_nilradical]
    rfl
  have hr : IsHomeomorph r :=
    isHomeomorph_iff_isEmbedding_surjective.mpr ⟨r.isEmbedding, r.surjective⟩
  exact dimension_lt_of_dense_open r hr V hVd d hd C hC
    (fun z : Z ↦ z.1.1) (Topology.IsInducing.subtypeVal.comp Topology.IsInducing.subtypeVal)
    (fun z ↦ hZC z.1 z.2) (fun z ↦ z.1.2.2)

end AlgebraicGeometry
