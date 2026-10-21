/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF groups Q04 and E2
-/
module

public import Sheaf.Paper.WeilCompletedTensorReflector
public import Sheaf.Paper.PbcAutomorphismTransport
public import Sheaf.Paper.PbcCompletedPullbackActual
import all Sheaf.AlgebraicGeometry.ProEtaleOperations
import Sheaf.Paper.SfConstructibleCanonicalCompleteness
import Sheaf.Paper.CompletedKoszulQuotientComparison
import Mathlib.CategoryTheory.Adjunction.FullyFaithful
import Mathlib.CategoryTheory.Adjunction.Restrict

/-! # Automorphisms commute with intrinsic completed-coefficient completion

Source: blueprint main-20261015, def-wf-tensor-product, tensor Frobenius sentence;
Stacks Tags 099N, 099M, 0A0E and 03D7.
(blueprint: lem-sf-automorphism-completion-unit-comparison).
The ordinary derived functors and their adjunction are the published tensor-formula
pullback and module direct image. Completion uses the actual completed coefficient
ring, the specified Koszul fiber, and its specified (u,0) unit.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

set_option backward.isDefEq.respectTransparency false in
private theorem completeWitness
    (X : Scheme.{u}) {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)
    (r : ℕ) (a : Fin r → A) (ha : Ideal.span (Set.range a) = d.ideal)
    (M : PbcCompletedDerived X d) (hM : WfIsComplete X d r a ha M) :
    PbcIsIntrinsicallyComplete X d M := by
  let B := intrinsicPresentationModulesBack X d
  let R := pbcDerivedRestrict (pbcCompletedComparison X d).inv
  let L := pbcDerivedExtend (pbcCompletedComparison X d).inv
  let c := (sheafCompose (ProEt.topology X)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).mapIso
      (pbcCompletedComparison X d).symm
  have : B.IsEquivalence :=
    inferInstanceAs (proEtaleScalarEquivalence X c).functor.IsEquivalence
  have : R.IsEquivalence := by dsimp [R, pbcDerivedRestrict]; infer_instance
  let adj : L ⊣ R := pbcDerivedScalarAdjunction (pbcCompletedComparison X d).inv
  let C := wfCompletionRepresentative X d M
  let real := DerivedCategory.Q.objObjPreimageIso M
  let P := (intrinsicPresentationComplex X d).obj C
  let U := completedKoszulUnitComplex X (intrinsicPresentationDatum d) r a P
  let E := (NatIso.mapHomologicalComplex (intrinsicPresentationRoundTrip X d)
    (.up ℤ)).app C
  have hunit : intrinsicCompletionComplexUnit X d r a C =
      E.hom ≫ (B.mapHomologicalComplex (.up ℤ)).map U := by
    ext i
    rfl
  have hq : IsIso (DerivedCategory.Q.map (intrinsicCompletionComplexUnit X d r a C)) := by
    have : IsIso (intrinsicCompletionUnit X d r a ha M C real) := hM
    change IsIso (real.inv ≫ _) at this
    exact IsIso.of_isIso_comp_left real.inv _
  have hbu : IsIso (DerivedCategory.Q.map ((B.mapHomologicalComplex (.up ℤ)).map U)) := by
    rw [hunit, Functor.map_comp] at hq
    have := hq
    exact IsIso.of_isIso_comp_left (DerivedCategory.Q.map E.hom) _
  have hru : IsIso (R.map (DerivedCategory.Q.map U)) := by
    have hn := B.mapDerivedCategoryFactors_hom_naturality U
    have : IsIso (R.map (DerivedCategory.Q.map U) ≫
        B.mapDerivedCategoryFactors.hom.app _) := by
      change IsIso (B.mapDerivedCategory.map (DerivedCategory.Q.map U) ≫ _)
      rw [hn]
      infer_instance
    exact IsIso.of_isIso_comp_right _ (B.mapDerivedCategoryFactors.hom.app _)
  have hu : IsIso (DerivedCategory.Q.map U) := isIso_of_reflects_iso _ R
  let realP : DerivedCategory.Q.obj P ≅ L.obj M :=
    R.preimageIso (B.mapDerivedCategoryFactors.app P ≪≫
      (DerivedCategory.Q.mapIso E).symm ≪≫ real ≪≫ asIso (adj.unit.app M))
  refine ⟨r, a, ha, P, realP, ?_⟩
  change IsIso (realP.inv ≫ DerivedCategory.Q.map U)
  infer_instance

private theorem completeIso
    (X : Scheme.{u}) {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)
    {M N : PbcCompletedDerived X d} (e : M ≅ N)
    (hM : PbcIsIntrinsicallyComplete X d M) : PbcIsIntrinsicallyComplete X d N := by
  obtain ⟨r, a, ha, C, real, hC⟩ := hM
  refine ⟨r, a, ha, C,
    real ≪≫ (pbcDerivedExtend (pbcCompletedComparison X d).inv).mapIso e, ?_⟩
  change IsIso (real.inv ≫ _) at hC
  have := hC
  change IsIso (((pbcDerivedExtend (pbcCompletedComparison X d).inv).map e.inv ≫
    real.inv) ≫ _)
  rw [Category.assoc]
  infer_instance

private theorem completeUnit_iff
    (X : Scheme.{u}) {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)
    (M : PbcCompletedDerived X d) :
    PbcIsIntrinsicallyComplete X d M ↔ IsIso ((pbcActualCompletionUnit d X).app M) := by
  let P := PbcIsIntrinsicallyComplete X d
  let adj := Adjunction.ofIsRightAdjoint (ObjectProperty.ι P)
  change P M ↔ IsIso (adj.unit.app M)
  rw [adj.isIso_unit_app_iff_mem_essImage]
  constructor
  · intro h
    exact ⟨⟨M, h⟩, ⟨Iso.refl _⟩⟩
  · rintro ⟨N, ⟨e⟩⟩
    exact completeIso X d e N.property

private theorem wfComplete_iff
    (X : Scheme.{u}) {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)
    (r : ℕ) (a : Fin r → A) (ha : Ideal.span (Set.range a) = d.ideal)
    (M : PbcCompletedDerived X d) :
    WfIsComplete X d r a ha M ↔ PbcIsIntrinsicallyComplete X d M :=
  ⟨completeWitness X d r a ha M,
    fun h ↦ sfConstructibleCanonicalReflectorComplete X d M h r a ha⟩

set_option backward.isDefEq.respectTransparency false in
private theorem intrinsicReflection
    (X : Scheme.{u}) {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)
    (r : ℕ) (a : Fin r → A) (ha : Ideal.span (Set.range a) = d.ideal)
    (M : PbcCompletedDerived X d)
    (C : CochainComplex (pbcModules X (pbcAdicCompletion X d)) ℤ)
    (real : DerivedCategory.Q.obj C ≅ M) :
    PbcIsIntrinsicallyComplete X d (intrinsicCompletion X d r a ha M C real) ∧
    ∀ N, PbcIsIntrinsicallyComplete X d N →
      Function.Bijective (fun f : intrinsicCompletion X d r a ha M C real ⟶ N ↦
        intrinsicCompletionUnit X d r a ha M C real ≫ f) := by
  obtain ⟨c, hc⟩ := completedKoszulQuotientComparison X d r a ha M C real
  obtain ⟨c₀, hc₀⟩ := completedKoszulQuotientComparison X d r a ha M
    (wfCompletionRepresentative X d M) (DerivedCategory.Q.objObjPreimageIso M)
  let k : intrinsicCompletion X d r a ha M C real ≅ wfCompletionObj X d r a ha M :=
    c ≪≫ c₀.symm
  have hk : intrinsicCompletionUnit X d r a ha M C real ≫ k.hom =
      wfCompletionUnit X d r a ha M := by
    apply (cancel_mono c₀.hom).mp
    dsimp only [k, Iso.trans_hom, Iso.symm_hom]
    rw [Category.assoc, Category.assoc, c₀.inv_hom_id, Category.comp_id]
    exact hc.trans hc₀.symm
  have hcomplete := (wfComplete_iff X d r a ha _).mp
    ((wfCompletionReflector X d r a ha).1 M)
  refine ⟨completeIso X d k.symm hcomplete, ?_⟩
  intro N hN
  have hb := (wfCompletionReflector X d r a ha).2 M N
    ((wfComplete_iff X d r a ha _).mpr hN)
  constructor
  · intro f g hfg
    have h : k.inv ≫ f = k.inv ≫ g := hb.1 (by
      simpa only [← hk, Category.assoc, Iso.hom_inv_id_assoc] using hfg)
    exact (cancel_epi k.inv).mp h
  · intro f
    obtain ⟨g, hg⟩ := hb.2 f
    refine ⟨k.hom ≫ g, ?_⟩
    change intrinsicCompletionUnit X d r a ha M C real ≫ (k.hom ≫ g) = f
    rw [← Category.assoc, hk]
    exact hg

private theorem adjointReflection
    {C D : Type*} [Category* C] [Category* D] {H : C ⥤ D} {G : D ⥤ C}
    (adj : H ⊣ G) (P : C → Prop) (Q : D → Prop)
    (hG : ∀ N, Q N → P (G.obj N)) {M L : C} (η : M ⟶ L)
    (hη : ∀ K, P K → Function.Bijective (fun f : L ⟶ K ↦ η ≫ f)) :
    ∀ N, Q N → Function.Bijective (fun f : H.obj L ⟶ N ↦ H.map η ≫ f) := by
  intro N hN
  have hb := hη (G.obj N) (hG N hN)
  constructor
  · intro f g hfg
    apply (adj.homEquiv _ _).injective
    apply hb.1
    simpa only [← adj.homEquiv_naturality_left] using
      congrArg (adj.homEquiv _ _) hfg
  · intro f
    obtain ⟨g, hg⟩ := hb.2 (adj.homEquiv _ _ f)
    refine ⟨(adj.homEquiv _ _).symm g, ?_⟩
    apply (adj.homEquiv _ _).injective
    rw [adj.homEquiv_naturality_left, Equiv.apply_symm_apply]
    exact hg

private theorem reflectionIso
    {D : Type*} [Category* D] (P : D → Prop) {M L N : D}
    (η : M ⟶ L) (μ : M ⟶ N) (hL : P L) (hN : P N)
    (hη : ∀ K, P K → Function.Bijective (fun f : L ⟶ K ↦ η ≫ f))
    (hμ : ∀ K, P K → Function.Bijective (fun f : N ⟶ K ↦ μ ≫ f)) :
    ∃! e : L ≅ N, η ≫ e.hom = μ := by
  obtain ⟨f, hf⟩ := (hη N hN).2 μ
  obtain ⟨g, hg⟩ := (hμ L hL).2 η
  dsimp only at hf hg
  have hfg : f ≫ g = 𝟙 L := (hη L hL).1 (by
    dsimp only
    rw [← Category.assoc, hf, hg, Category.comp_id])
  have hgf : g ≫ f = 𝟙 N := (hμ N hN).1 (by
    dsimp only
    rw [← Category.assoc, hg, hf, Category.comp_id])
  refine ⟨⟨f, g, hfg, hgf⟩, hf, ?_⟩
  intro e he
  apply Iso.ext
  exact (hη N hN).1 (he.trans hf.symm)

set_option backward.isDefEq.respectTransparency false in
/-- Ordinary pullback by an automorphism and its actual right adjoint preserve the
complete full subcategory; their specified adjoint equivalence restricts to it.
On every pair of complex representatives there is exactly one completion comparison
isomorphism carrying the pulled-back intrinsic unit to the intrinsic unit.

Source: blueprint main-20261015, def-wf-tensor-product, tensor Frobenius sentence;
Stacks Tags 099N, 099M, 0A0E and 03D7.
(blueprint: lem-sf-automorphism-completion-unit-comparison).

Proof: (1) exact module transport is an equivalence, hence its termwise derived
functor is an equivalence. The specified ordinary-derived comparison transports the
actual derived adjunction to this functor. Its unit and counit are invertible.
(2) An invertible actual Koszul unit gives a published intrinsic-completeness witness:
apply the inverse coefficient restriction equivalence to reflect invertibility of
the published unit, and use the scalar adjunction to realize the transported complex.
Conversely, canonical completeness supplies the actual Koszul unit for every tuple.
(3) The actual direct-image/completion isomorphism preserves the reflection unit.
Since direct image is an equivalence, it therefore preserves and reflects intrinsic
completeness. Its composite with pullback is isomorphic to the identity by the
actual adjunction unit, so pullback preserves completeness as well. Restrict that
adjunction along the full inclusions. Its Hom transpose is the ambient one, and
its unit and counit remain invertible by full faithfulness.
(4) Compare any representative's Koszul completion, and the canonical representative's,
to the same strict quotient completion, using their specified unit equations.
Their composite is a unit-preserving isomorphism. Transport the canonical
reflector's complete-output and Hom-bijection assertions through this isomorphism.
(5) For a complete target N, direct image GN is complete. The adjunction Hom
bijection therefore transports the reflection property of eta_M to H(eta_M).
Both H(LM) and L(HM) are complete, so their reflection properties supply inverse
maps; injectivity of precomposition with their units proves the inverse identities
and uniqueness of the resulting unit-preserving isomorphism. All arguments apply
to every generating tuple and representative, including r = 0. -/
theorem automorphism_completion_unit_comparison
    (X : Scheme.{u}) {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)
    (r : ℕ) (a : Fin r → A) (ha : Ideal.span (Set.range a) = d.ideal) (e : Aut X) :
    (∀ M : PbcCompletedDerived X d,
      IsIso (((pbcActualDerivedAdjunction e.hom d).ofNatIsoLeft
        (pbcIsoOrdinaryDerivedComparison e.hom d)).unit.app M)) ∧
    (∀ M : PbcCompletedDerived X d,
      IsIso (((pbcActualDerivedAdjunction e.hom d).ofNatIsoLeft
        (pbcIsoOrdinaryDerivedComparison e.hom d)).counit.app M)) ∧
    (∃ (hH : ∀ M : WfCompleteCategory X d r a ha,
          WfIsComplete X d r a ha ((pbcIsoAmbientPullback e.hom d).obj M.obj))
        (hG : ∀ M : WfCompleteCategory X d r a ha,
          WfIsComplete X d r a ha ((pbcActualDerivedPush e.hom d).obj M.obj)),
      ∃ adj :
          ObjectProperty.lift (WfIsComplete X d r a ha)
            (ObjectProperty.ι (WfIsComplete X d r a ha) ⋙ pbcIsoAmbientPullback e.hom d) hH ⊣
          ObjectProperty.lift (WfIsComplete X d r a ha)
            (ObjectProperty.ι (WfIsComplete X d r a ha) ⋙ pbcActualDerivedPush e.hom d) hG,
        (∀ (M N : WfCompleteCategory X d r a ha)
          (f : (ObjectProperty.lift (WfIsComplete X d r a ha)
            (ObjectProperty.ι (WfIsComplete X d r a ha) ⋙
              pbcIsoAmbientPullback e.hom d) hH).obj M ⟶ N),
          (adj.homEquiv M N f).hom =
            ((pbcActualDerivedAdjunction e.hom d).ofNatIsoLeft
              (pbcIsoOrdinaryDerivedComparison e.hom d)).homEquiv M.obj N.obj f.hom) ∧
        (∀ M : WfCompleteCategory X d r a ha, IsIso (adj.unit.app M)) ∧
        (∀ M : WfCompleteCategory X d r a ha, IsIso (adj.counit.app M))) ∧
    ∀ (M : PbcCompletedDerived X d)
      (C : CochainComplex (pbcModules X (pbcAdicCompletion X d)) ℤ)
      (real : DerivedCategory.Q.obj C ≅ M)
      (D : CochainComplex (pbcModules X (pbcAdicCompletion X d)) ℤ)
      (realH : DerivedCategory.Q.obj D ≅ (pbcIsoAmbientPullback e.hom d).obj M),
      ∃! c : (pbcIsoAmbientPullback e.hom d).obj
          (intrinsicCompletion X d r a ha M C real) ≅
        intrinsicCompletion X d r a ha ((pbcIsoAmbientPullback e.hom d).obj M) D realH,
        (pbcIsoAmbientPullback e.hom d).map (intrinsicCompletionUnit X d r a ha M C real) ≫
            c.hom =
          intrinsicCompletionUnit X d r a ha ((pbcIsoAmbientPullback e.hom d).obj M) D realH := by
  have : (pbcIsoAmbientPullback e.hom d).IsEquivalence := by
    change (pbcIsoModulePullback e.hom d).mapDerivedCategory.IsEquivalence
    infer_instance
  let H := pbcIsoAmbientPullback e.hom d
  let G := pbcActualDerivedPush e.hom d
  let adj := (pbcActualDerivedAdjunction e.hom d).ofNatIsoLeft
    (pbcIsoOrdinaryDerivedComparison e.hom d)
  have : G.IsEquivalence := adj.isEquivalence_right_of_isEquivalence_left
  have hGiff (M : PbcCompletedDerived X d) :
      PbcIsIntrinsicallyComplete X d (G.obj M) ↔ PbcIsIntrinsicallyComplete X d M := by
    rw [completeUnit_iff, completeUnit_iff]
    obtain ⟨c, hc⟩ := (pbcActualDirectCompletionIso_exists e.hom d).exists
    have h := hc M
    constructor
    · intro hi
      have := hi
      have hh : IsIso (G.map ((pbcActualCompletionUnit d X).app M)) := by
        rw [← h]
        infer_instance
      exact isIso_of_reflects_iso _ G
    · intro hi
      have := hi
      have hh : IsIso ((pbcActualCompletionUnit d X).app (G.obj M) ≫ c.hom.app M) := by
        rw [h]
        infer_instance
      exact IsIso.of_isIso_comp_right _ (c.hom.app M)
  have hH (M : WfCompleteCategory X d r a ha) :
      WfIsComplete X d r a ha (H.obj M.obj) := by
    apply (wfComplete_iff X d r a ha _).mpr
    apply (hGiff _).mp
    exact completeIso X d (asIso (adj.unit.app M.obj))
      ((wfComplete_iff X d r a ha _).mp M.property)
  have hG (M : WfCompleteCategory X d r a ha) :
      WfIsComplete X d r a ha (G.obj M.obj) := by
    exact (wfComplete_iff X d r a ha _).mpr
      ((hGiff _).mpr ((wfComplete_iff X d r a ha _).mp M.property))
  refine ⟨fun M ↦ by infer_instance, fun M ↦ by infer_instance, ?_, ?_⟩
  · refine ⟨hH, hG, ?_⟩
    let P : ObjectProperty (PbcCompletedDerived X d) := WfIsComplete X d r a ha
    let inc := ObjectProperty.ι P
    let H' := ObjectProperty.lift P (inc ⋙ H) hH
    let G' := ObjectProperty.lift P (inc ⋙ G) hG
    let adj' : H' ⊣ G' := adj.restrictFullyFaithful
      P.fullyFaithfulι P.fullyFaithfulι (Iso.refl _) (Iso.refl _)
    refine ⟨adj', ?_, ?_, ?_⟩
    · intro M N f
      rw [Adjunction.restrictFullyFaithful_homEquiv_apply]
      change adj.unit.app M.obj ≫ G.map (𝟙 _) ≫ G.map f.hom ≫ 𝟙 _ =
        adj.unit.app M.obj ≫ G.map f.hom
      simp only [G.map_id, Category.comp_id]
      exact congrArg (fun k ↦ adj.unit.app M.obj ≫ k) (Category.id_comp (G.map f.hom))
    · intro M
      infer_instance
    · intro M
      infer_instance
  · intro M C real D realH
    obtain ⟨hLC, huC⟩ := intrinsicReflection X d r a ha M C real
    obtain ⟨hLD, huD⟩ := intrinsicReflection X d r a ha (H.obj M) D realH
    have hHLC : PbcIsIntrinsicallyComplete X d
        (H.obj (intrinsicCompletion X d r a ha M C real)) := by
      apply (hGiff _).mp
      exact completeIso X d (asIso (adj.unit.app _)) hLC
    exact reflectionIso (PbcIsIntrinsicallyComplete X d)
      (H.map (intrinsicCompletionUnit X d r a ha M C real))
      (intrinsicCompletionUnit X d r a ha (H.obj M) D realH) hHLC hLD
      (adjointReflection adj (PbcIsIntrinsicallyComplete X d)
        (PbcIsIntrinsicallyComplete X d) (fun N h ↦ (hGiff N).mpr h) _ huC) huD

end AlgebraicGeometry.Scheme
