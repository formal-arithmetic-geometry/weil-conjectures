/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.IsRegularScheme
public import Sheaf.AlgebraicGeometry.StrictNormalCrossingsBoundary
public import WeilConjectures.RingTheory.IsRegularSystemOfParameters
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.RingTheory.Localization.AtPrime.Basic

import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Affine
import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Basic
import WeilConjectures.AlgebraicGeometry.Morphisms.RegularImmersionStalk
import WeilConjectures.RingTheory.RegularLocalQuotientKernelParameters
import WeilConjectures.RingTheory.RegularLocalGeneratorsRegularSequence

/-!
# Labelled affine SNC charts with integral deepest stratum

Source: ILO, Travaux de Gabber, VIII Remark 4.2.2(i), printed pp. 118--119;
Stacks Project, Tag 00NR, and the affine component refinement in the DAG proof
(blueprint: lem-sfb-snc-labelled-affine-stratum-charts).

The charts map to Y by open immersions avoiding the components outside I. The
reduced intersection is pulled back from Y, which is the same closed subscheme
on such a chart as the reduced stratum inside the open Y_I. This avoids importing
the downstream henselian charts merely to name that open.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

private theorem parameter_extension
    {R S : Type u} [CommRing R] [CommRing S]
    [IsRegularLocalRing R] [IsRegularLocalRing S]
    (f : R →+* S) (hf : Function.Surjective f) (xs : List R)
    (hker : Ideal.ofList xs = RingHom.ker f)
    (hdim : ringKrullDim R = ringKrullDim S + (xs.length : ℕ)) :
    ∃ ys : List R, IsLocalRing.IsRegularSystemOfParameters (xs ++ ys) := by
  classical
  obtain ⟨s, hcard, hspan⟩ := Submodule.FG.exists_span_finset_card_eq_spanFinrank
    (IsNoetherian.noetherian (IsLocalRing.maximalIdeal S))
  obtain ⟨ys, hys⟩ := hf.list_map s.toList
  have hmap : (Ideal.ofList (xs ++ ys)).map f = IsLocalRing.maximalIdeal S := by
    rw [Ideal.ofList_append, Ideal.map_sup, hker, (Ideal.map_eq_bot_iff_le_ker f).mpr le_rfl,
      bot_sup_eq,
      Ideal.map_ofList, hys]
    change Submodule.span S {r | r ∈ s.toList} = _
    simpa using hspan
  have hspan' : Ideal.ofList (xs ++ ys) = IsLocalRing.maximalIdeal R := by
    have h := congrArg (Ideal.comap f) hmap
    rw [Ideal.comap_map_of_surjective f hf, ← RingHom.ker_eq_comap_bot] at h
    rw [sup_eq_left.mpr (by
      rw [← hker]
      exact Ideal.span_mono (by intro x hx; exact List.mem_append_left _ hx))] at h
    rw [← IsLocalRing.map_maximalIdeal_of_surjective f hf,
      Ideal.comap_map_of_surjective f hf,
      ← RingHom.ker_eq_comap_bot,
      sup_eq_left.mpr (IsLocalRing.le_maximalIdeal (RingHom.ker_ne_top f))] at h
    exact h
  refine ⟨ys, hspan', ?_⟩
  have hlen : ys.length = (IsLocalRing.maximalIdeal S).spanFinrank := by
    have hh := congrArg List.length hys
    simpa only [List.length_map, Finset.length_toList, hcard] using hh
  rw [List.length_append, Nat.cast_add, hlen,
    IsRegularLocalRing.spanFinrank_maximalIdeal, add_comm]
  exact hdim.symm

private theorem principal_regular_kernel
    {R S : Type u} [CommRing R] [CommRing S]
    [IsRegularLocalRing R] [IsRegularLocalRing S]
    (f : R →+* S) (hf : Function.Surjective f)
    (hdim : ringKrullDim R = ringKrullDim S + 1) :
    ∃ xs : List R, xs.length = 1 ∧ RingTheory.Sequence.IsRegular R xs ∧
      Ideal.ofList xs = RingHom.ker f := by
  let d := (IsLocalRing.maximalIdeal R).spanFinrank
  have hd : ringKrullDim R = (d : WithBot ℕ∞) :=
    IsRegularLocalRing.spanFinrank_maximalIdeal.symm
  have : IsRegularLocalRing (R ⧸ RingHom.ker f) :=
    IsRegularLocalRing.of_ringEquiv (f.quotientKerEquivOfSurjective hf).symm
  obtain ⟨p, c, hc, hp, hker⟩ := RingTheory.exists_parameters_regularLocalQuotient
    R d hd (RingHom.ker f) (RingHom.ker_ne_top f)
  obtain ⟨hreg, hquot, -⟩ :=
    IsRegularLocalRing.isRegular_and_quotients_of_generators R d hd p hp
  have heq := (hquot c hc).2
  rw [← hker, ringKrullDim_eq_of_ringEquiv (f.quotientKerEquivOfSurjective hf)] at heq
  have hc1 : c = 1 := by
    rw [hd, heq] at hdim
    have heq' : d = d - c + 1 := by exact_mod_cast hdim
    omega
  have hw : RingTheory.Sequence.IsWeaklyRegular R (p.take c) :=
    ((RingTheory.Sequence.isWeaklyRegular_append_iff R (p.take c) (p.drop c)).mp
      (by simpa using hreg.toIsWeaklyRegular)).1
  have hr : RingTheory.Sequence.IsRegular R (p.take c) :=
    (IsLocalRing.isRegular_iff_isWeaklyRegular_of_subset_maximalIdeal (fun x hx ↦
      hp.1 ▸ Ideal.subset_span (List.mem_of_mem_take hx))).mpr hw
  refine ⟨p.take c, ?_, hr, hker.symm⟩
  have hlen : p.length = d := by exact_mod_cast hp.2.trans hd
  rw [List.length_take, hlen, min_eq_left hc, hc1]

private theorem regular_of_open {X Z : Scheme.{u}} (f : X ⟶ Z)
    [IsOpenImmersion f] [IsRegular Z] : IsRegular X := by
  constructor
  intro x
  exact IsRegularLocalRing.of_ringEquiv (asIso (f.stalkMap x)).commRingCatIsoToRingEquiv

private theorem locally_principal_of_regular_codimension_one
    {X Z : Scheme.{u}} [IsLocallyNoetherian X] [IsRegular X] [IsRegular Z]
    (i : Z ⟶ X) [IsClosedImmersion i]
    (hdim : ∀ z, ringKrullDim (X.presheaf.stalk (i z)) =
      ringKrullDim (Z.presheaf.stalk z) + 1) : i.ker.IsLocallyPrincipal := by
  have : IsRegularImmersion 1 i := IsRegularImmersion.of_stalk 1 (by decide) i (by
    intro z
    obtain ⟨xs, hlen, hreg, hker⟩ :=
      principal_regular_kernel (i.stalkMap z).hom (i.stalkMap_surjective z) (hdim z)
    exact ⟨xs, hlen, hreg.toIsWeaklyRegular, hker⟩)
  intro x
  obtain ⟨U, hx, xs, hlen, -, hspan⟩ :=
    IsRegularImmersion.exists_isWeaklyRegular_generators (c := 1) (i := i) x
  rw [List.eq_cons_of_length_one hlen] at hspan
  refine ⟨U, hx, ?_⟩
  rw [← hspan, Ideal.ofList_singleton]
  infer_instance

private theorem common_principal_neighbourhood
    {X : Scheme.{u}} {a : ℕ} (C : Fin a → X.IdealSheafData)
    (hC : ∀ i, (C i).IsLocallyPrincipal) (x : X) (O : X.Opens) (hx : x ∈ O) :
    ∃ U : X.affineOpens, x ∈ U.1 ∧ U.1 ≤ O ∧
      ∀ i, ∃ t : Γ(X, U.1), (C i).ideal U = Ideal.span {t} := by
  classical
  choose V hxV hV using fun i ↦ hC i x
  let W : X.Opens := O ⊓ ⨅ i, (V i).1
  have hxW : x ∈ W := ⟨hx, by
    change x ∈ ((⨅ i, (V i).1 : X.Opens) : Set X)
    rw [TopologicalSpace.Opens.coe_iInf]
    exact Set.mem_iInter.mpr (fun i ↦ hxV i)⟩
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, hUW⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hxW W.isOpen
  refine ⟨⟨U, hU⟩, hxU, fun z hz ↦ (hUW hz).1, ?_⟩
  intro i
  obtain ⟨t, ht⟩ := hV i
  have hUV : U ≤ (V i).1 := fun z hz ↦
    ((iInf_le (fun i ↦ (V i).1) i) ((hUW hz).2))
  refine ⟨X.presheaf.map (homOfLE hUV).op t, ?_⟩
  rw [← (C i).map_ideal hUV, ht, Ideal.submodule_span_eq,
    Ideal.map_span, Set.image_singleton]
  rfl

private theorem integral_neighbourhood_pair
    {X : Scheme.{u}} [IsNoetherian X] [IsRegular X]
    (J : X.IdealSheafData) [IsRegular J.subscheme]
    (x : X) (hx : x ∈ J.support) :
    ∃ O : X.Opens, x ∈ O ∧ IsIntegral O.toScheme ∧
      ∀ U : X.affineOpens, U.1 ≤ O → x ∈ U.1 →
        IsIntegral (Spec (.of (Γ(X, U.1) ⧸ J.ideal U))) := by
  classical
  have hx' : x ∈ Set.range J.subschemeι := by rwa [J.range_subschemeι]
  obtain ⟨z, rfl⟩ := hx'
  obtain ⟨n, V, hVcl, -, hVcov, hV⟩ := IsRegular.exists_isClopen_isIntegral X
  have hzV : J.subschemeι z ∈ ⨆ i, V i := by rw [hVcov]; trivial
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hzV
  have : IsLocallyNoetherian J.subscheme :=
    LocallyOfFiniteType.isLocallyNoetherian J.subschemeι
  have : IsNoetherian J.subscheme := {}
  obtain ⟨m, W, hWcl, -, hWcov, hW⟩ := IsRegular.exists_isClopen_isIntegral J.subscheme
  have hzW : z ∈ ⨆ j, W j := by rw [hWcov]; trivial
  obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.mp hzW
  let F : Set X := J.subschemeι '' ((W j : Set J.subscheme)ᶜ)
  have hF : IsClosed F := J.subschemeι.isClosedEmbedding.isClosedMap _
    (hWcl j).isOpen.isClosed_compl
  let O : X.Opens := V i ⊓ ⟨Fᶜ, hF.isOpen_compl⟩
  have hxO : J.subschemeι z ∈ O := by
    refine ⟨hi, ?_⟩
    rintro ⟨z', hz', he⟩
    exact hz' (J.subschemeι.isClosedEmbedding.injective he ▸ hj)
  have : IsIntegral (V i).toScheme := (hV i).1
  have : Nonempty O.toScheme := ⟨⟨_, hxO⟩⟩
  have hint : IsIntegral O.toScheme := isIntegral_of_isOpenImmersion (X.homOfLE inf_le_left)
  refine ⟨O, hxO, hint, ?_⟩
  intro U hU hxU
  let f := J.subschemeCover.f U
  have hrange : Set.range f ⊆ Set.range (W j).ι := by
    rintro w ⟨q, rfl⟩
    rw [Scheme.Opens.range_ι]
    have hq : J.subschemeι (f q) ∈ U.1 := by
      change f q ∈ J.subschemeι ⁻¹ᵁ U.1
      rw [← J.opensRange_subschemeCover_map U]
      exact Set.mem_range_self q
    by_contra hw
    exact (hU hq).2 ⟨f q, hw, rfl⟩
  let g := IsOpenImmersion.lift (W j).ι f hrange
  have : IsOpenImmersion g := inferInstance
  have hnonempty : Nonempty (Spec (.of (Γ(X, U.1) ⧸ J.ideal U))) := by
    have hz : z ∈ f.opensRange := by
      rw [J.opensRange_subschemeCover_map U]
      exact hxU
    obtain ⟨q, -⟩ := hz
    exact ⟨q⟩
  have : IsIntegral (W j).toScheme := (hW j).1
  exact isIntegral_of_isOpenImmersion g

private theorem labelled_parameters
    {X : Scheme.{u}} [IsRegular X] {a : ℕ} (C : Fin a → X.IdealSheafData)
    (hC : ∀ K : Finset (Fin a), ∀ z : (⨆ i ∈ K, C i).subscheme,
      IsRegularScheme (⨆ i ∈ K, C i).subscheme ∧
      ringKrullDim (X.presheaf.stalk ((⨆ i ∈ K, C i).subschemeι z)) =
        ringKrullDim ((⨆ i ∈ K, C i).subscheme.presheaf.stalk z) + (K.card : ℕ))
    (U : X.affineOpens) {b : ℕ} (e : Fin b → Fin a) (he : Function.Injective e)
    (t : Fin b → Γ(X, U.1)) (ht : ∀ i, (C (e i)).ideal U = Ideal.span {t i})
    (x : X) (hx : x ∈ U.1) :
    ∃ s : List (X.presheaf.stalk x), IsLocalRing.IsRegularSystemOfParameters s ∧
      List.Sublist
        (((List.ofFn t).filter (fun z ↦ @decide
          (X.presheaf.germ U.1 x hx z ∈ IsLocalRing.maximalIdeal _)
          (Classical.propDecidable _))).map
          (X.presheaf.germ U.1 x hx)) s := by
  classical
  let L : List (Fin b) := (List.ofFn id).filter (fun i ↦ @decide
    (X.presheaf.germ U.1 x hx (t i) ∈ IsLocalRing.maximalIdeal _) (Classical.propDecidable _))
  let K : Finset (Fin a) := (L.map e).toFinset
  let J : X.IdealSheafData := ⨆ i ∈ K, C i
  have hL : L.Nodup := by
    apply List.Nodup.filter
    exact List.nodup_ofFn.mpr Function.injective_id
  have hcard : K.card = L.length := by
    rw [List.toFinset_card_of_nodup (hL.map he), List.length_map]
  have hgen : J.ideal U = Ideal.ofList (L.map t) := by
    apply le_antisymm
    · change (⨆ i ∈ K, C i).ideal U ≤ _
      rw [show (⨆ i ∈ K, C i) = ⨆ i : K, C i.val from
        (iSup_subtype (f := fun i : K ↦ C i.val)).symm]
      simp only [Scheme.IdealSheafData.ideal_iSup, iSup_apply, iSup_le_iff]
      intro i
      obtain ⟨l, hl, hil⟩ := List.mem_map.mp (List.mem_toFinset.mp i.2)
      rw [← hil]
      rw [ht l]
      exact Ideal.span_mono (by rintro z rfl; exact List.mem_map.mpr ⟨l, hl, rfl⟩)
    · apply Ideal.span_le.mpr
      intro z hz
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hz
      have hmem : e i ∈ K := List.mem_toFinset.mpr (List.mem_map.mpr ⟨i, hi, rfl⟩)
      have hle : C (e i) ≤ J := le_iSup_of_le (e i) (le_iSup_of_le hmem le_rfl)
      exact hle U (ht i ▸ Ideal.mem_span_singleton_self (t i))
  have hJm : (J.ideal U).map (X.presheaf.germ U.1 x hx).hom ≤
      IsLocalRing.maximalIdeal _ := by
    rw [hgen, Ideal.map_ofList]
    apply Ideal.span_le.mpr
    intro z hz
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hz
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hv
    exact of_decide_eq_true (List.mem_filter.mp hi).2
  have hxJ : x ∈ J.support := by
    rw [Scheme.IdealSheafData.mem_support_iff_of_mem hx]
    rw [X.mem_zeroLocus_iff]
    intro z hz
    rw [X.mem_basicOpen z x hx]
    exact (IsLocalRing.mem_maximalIdeal _).mp
      (hJm (Ideal.mem_map_of_mem _ hz))
  have hLdef : L = (List.ofFn id).filter (fun i ↦ @decide
      (X.presheaf.germ U.1 x hx (t i) ∈ IsLocalRing.maximalIdeal _)
      (Classical.propDecidable _)) := rfl
  clear_value L
  have hxrange : x ∈ Set.range J.subschemeι := by rwa [J.range_subschemeι]
  obtain ⟨z, rfl⟩ := hxrange
  have : IsRegular J.subscheme := (hC K z).1.2
  let f := (J.subschemeι.stalkMap z).hom
  have hker : Ideal.ofList ((L.map t).map (X.presheaf.germ U.1 _ hx)) =
      RingHom.ker f := by
    rw [J.subschemeι.ker_stalkMap U z hx, J.ker_subschemeι, hgen, Ideal.map_ofList]
  have hdim : ringKrullDim (X.presheaf.stalk (J.subschemeι z)) =
      ringKrullDim (J.subscheme.presheaf.stalk z) +
        (((L.map t).map (X.presheaf.germ U.1 _ hx)).length : ℕ) := by
    simpa only [List.length_map, hcard] using (hC K z).2
  obtain ⟨ys, hys⟩ := parameter_extension f (J.subschemeι.stalkMap_surjective z) _ hker hdim
  refine ⟨_, hys, ?_⟩
  have heq : (List.ofFn t).filter (fun v ↦ @decide
      (X.presheaf.germ U.1 _ hx v ∈ IsLocalRing.maximalIdeal _) (Classical.propDecidable _)) =
      L.map t := by
    rw [hLdef]
    conv_lhs => rw [show List.ofFn t = (List.ofFn id).map t by simp]
    rw [List.filter_map]
    rfl
  rw [heq]
  exact List.sublist_append_left _ _

private theorem parameters_map_equiv {R S : Type u} [CommRing R] [CommRing S]
    [IsLocalRing R] [IsNoetherianRing R] [IsLocalRing S] [IsNoetherianRing S]
    (e : R ≃+* S) {xs : List R} (h : IsLocalRing.IsRegularSystemOfParameters xs) :
    IsLocalRing.IsRegularSystemOfParameters (xs.map e) := by
  constructor
  · change Ideal.ofList (xs.map e.toRingHom) = _
    have hh : Ideal.ofList xs = IsLocalRing.maximalIdeal R := h.1
    rw [← Ideal.map_ofList, hh]
    exact IsLocalRing.map_ringEquiv_maximalIdeal e
  · rw [List.length_map, h.2, ringKrullDim_eq_of_ringEquiv e]

private theorem affine_equation {X : Scheme.{u}} (C : X.IdealSheafData)
    (U : X.affineOpens) (t : Γ(X, U.1)) (ht : C.ideal U = Ideal.span {t}) :
    C.comap U.2.fromSpec = Scheme.IdealSheafData.ofIdealTop
      (Ideal.span {(Scheme.ΓSpecIso Γ(X, U.1)).inv t}) := by
  apply Scheme.IdealSheafData.ext_of_isAffine
  have h := C.ideal_top_comap_specMap_fromSpec U (𝟙 _)
  simpa only [Spec.map_id, Category.id_comp, CommRingCat.hom_id, Ideal.map_id,
    ht, Ideal.map_span, Set.image_singleton, RingHom.id_apply,
    Scheme.IdealSheafData.ideal_top_ofIdealTop] using h

/-- One affine chart in the asserted family. Its equations retain the given labels,
ordered by the standard equivalence of I with a finite ordinal. The residual
isomorphism is over Spec B, so it identifies the reduced stratum scheme-theoretically.
Source: ILO VIII Remark 4.2.2(i); Stacks 00NR; DAG proof Steps 2--5
(blueprint: lem-sfb-snc-labelled-affine-stratum-charts). -/
structure SNCAffineStratumChart {Y : Scheme.{u}} {a : ℕ}
    (C : Fin a → Y.IdealSheafData) (I : Finset (Fin a)) where
  B : CommRingCat.{u}
  v : Spec B ⟶ Y
  openImmersion : IsOpenImmersion v
  inside : ∀ x : Spec B, ∀ i : Fin a, i ∉ I → v x ∉ (C i).support
  regular : IsRegularRing B
  noetherian : IsNoetherianRing B
  domain : IsDomain B
  separated : IsSeparated (terminal.from (Spec B))
  t : Fin (Fintype.card I) → B
  equations : ∀ i : Fin (Fintype.card I),
    (C ((Fintype.equivFin I).symm i).val).comap v =
      Scheme.IdealSheafData.ofIdealTop
        (Ideal.span {(Scheme.ΓSpecIso B).inv (t i)})
  parameters : ∀ q : PrimeSpectrum B,
    ∃ (_hnoeth : IsNoetherianRing (Localization.AtPrime q.asIdeal))
      (s : List (Localization.AtPrime q.asIdeal)),
      IsLocalRing.IsRegularSystemOfParameters s ∧
      List.Sublist
        (((List.ofFn t).filter
          (fun z ↦ @decide (z ∈ q.asIdeal) (Classical.propDecidable _))).map
          (algebraMap B (Localization.AtPrime q.asIdeal))) s
  residualIso : Spec (.of (B ⧸ Ideal.span (Set.range t))) ≅
    pullback (⨆ i ∈ I, C i).radical.subschemeι v
  residualIso_base : residualIso.hom ≫ pullback.snd _ _ =
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span (Set.range t))))
  residual_integral : IsIntegral (Spec (.of (B ⧸ Ideal.span (Set.range t))))
  residual_regular : IsRegularScheme (Spec (.of (B ⧸ Ideal.span (Set.range t))))
  residual_connected : ConnectedSpace (Spec (.of (B ⧸ Ideal.span (Set.range t))))
  empty_ideal : I = ∅ → Ideal.span (Set.range t) = ⊥
  empty_residual : I = ∅ →
    IsIso (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span (Set.range t)))))

set_option backward.isDefEq.respectTransparency false in
private theorem exists_chart_at
    (Y : Scheme.{u}) [IsNoetherian Y] [IsRegular Y]
    (a : ℕ) (C : Fin a → Y.IdealSheafData)
    (hCreg : ∀ i, IsRegularScheme (C i).subscheme)
    (hC : ∀ K : Finset (Fin a), ∀ z : (⨆ i ∈ K, C i).subscheme,
      IsRegularScheme (⨆ i ∈ K, C i).subscheme ∧
      ringKrullDim (Y.presheaf.stalk ((⨆ i ∈ K, C i).subschemeι z)) =
        ringKrullDim ((⨆ i ∈ K, C i).subscheme.presheaf.stalk z) + (K.card : ℕ))
    (I : Finset (Fin a)) (x : Y) (hx : x ∈ (⨆ i ∈ I, C i).support)
    (hout : ∀ i, i ∉ I → x ∉ (C i).support) :
    ∃ (Q : SNCAffineStratumChart C I) (q : Spec Q.B), Q.v q = x := by
  classical
  let J : Y.IdealSheafData := ⨆ i ∈ I, C i
  have hxJ : x ∈ J.support := hx
  have hxrange : x ∈ Set.range J.subschemeι := by rwa [J.range_subschemeι]
  obtain ⟨z, hz⟩ := hxrange
  have : IsRegular J.subscheme := (hC I z).1.2
  have : IsReduced J.subscheme := isReduced_of_isReduced_stalk _
  have hrad : J.radical = J := by
    have hv := J.subschemeι.ker_eq_vanishingIdeal
    rw [J.ker_subschemeι] at hv
    have he : (⟨closure (Set.range J.subschemeι), isClosed_closure⟩ :
        TopologicalSpace.Closeds Y) = J.support := by
      apply TopologicalSpace.Closeds.ext
      change closure (Set.range J.subschemeι) = (J.support : Set Y)
      rw [J.range_subschemeι, J.support.isClosed.closure_eq]
    rw [he, Scheme.IdealSheafData.vanishingIdeal_support] at hv
    exact hv.symm
  obtain ⟨O, hxO, hO, hOJ⟩ := integral_neighbourhood_pair J x hxJ
  have hp : ∀ i, (C i).IsLocallyPrincipal := by
    intro i
    have : IsRegular (C i).subscheme := (hCreg i).2
    have hdim : ∀ z, ringKrullDim (Y.presheaf.stalk ((C i).subschemeι z)) =
        ringKrullDim ((C i).subscheme.presheaf.stalk z) + 1 := by
      have hd := hC {i}
      rw [Finset.iSup_singleton] at hd
      simp only [Finset.card_singleton, Nat.cast_one] at hd
      exact fun w ↦ (hd w).2
    simpa using locally_principal_of_regular_codimension_one (C i).subschemeι hdim
  let Vout : Y.Opens := (⨆ i : {j : Fin a // j ∉ I}, (C i.val).support).compl
  have hxout : x ∈ Vout := by
    change x ∉ (⨆ i : {j : Fin a // j ∉ I}, (C i.val).support)
    have hc : IsClosed (⋃ i : {j : Fin a // j ∉ I}, ((C i.val).support : Set Y)) :=
      isClosed_iUnion_of_finite (fun i ↦ (C i.val).support.isClosed)
    have he : (⨆ i : {j : Fin a // j ∉ I}, (C i.val).support) =
        (⟨_, hc⟩ : TopologicalSpace.Closeds Y) := by
      apply le_antisymm
      · exact iSup_le fun i y hy ↦ Set.mem_iUnion.mpr ⟨i, hy⟩
      · intro y hy
        obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hy
        exact le_iSup (fun i : {j : Fin a // j ∉ I} ↦ (C i.val).support) i hi
    rw [he]
    exact fun hx ↦ by
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
      exact hout i.val i.property hi
  obtain ⟨U, hxU, hU, ht⟩ := common_principal_neighbourhood C hp x (O ⊓ Vout) ⟨hxO, hxout⟩
  choose t₀ ht₀ using ht
  let e : Fin (Fintype.card I) ≃ I := (Fintype.equivFin I).symm
  let t : Fin (Fintype.card I) → Γ(Y, U.1) := fun i ↦ t₀ (e i).val
  have hsum : Ideal.span (Set.range t) = J.ideal U := by
    change _ = (⨆ i ∈ I, C i).ideal U
    rw [show (⨆ i ∈ I, C i) = ⨆ i : I, C i.val from (iSup_subtype (f := fun i : I ↦ C i.val)).symm]
    rw [Scheme.IdealSheafData.ideal_iSup, iSup_apply, Ideal.span_range_eq_iSup]
    rw [← e.iSup_comp (g := fun i : I ↦ (C i.val).ideal U)]
    simp only [ht₀]
    rfl
  have hregB : IsRegularRing Γ(Y, U.1) := by
    have : IsNoetherianRing Γ(Y, U.1) := IsLocallyNoetherian.component_noetherian U
    rw [isRegularRing_iff]
    exact U.2.isRegularLocalRing_localization (fun _ _ ↦ inferInstance)
  have : IsRegularRing Γ(Y, U.1) := hregB
  have : IsIntegral O.toScheme := hO
  have hUO : U.1 ≤ O := fun y hy ↦ (hU hy).1
  have : Nonempty U.1.toScheme := ⟨⟨x, hxU⟩⟩
  have : IsIntegral U.1.toScheme := isIntegral_of_isOpenImmersion (Y.homOfLE hUO)
  have hdom : IsDomain Γ(Y, U.1) :=
    U.1.topIso.commRingCatIsoToRingEquiv.symm.toMulEquiv.isDomain _
  let R := Γ(Y, U.1) ⧸ J.ideal U
  let f := J.subschemeCover.f U
  have hR : IsIntegral (Spec (.of R)) := hOJ U hUO hxU
  have : IsIntegral (Spec (.of R)) := hR
  have hregR : IsRegularScheme (Spec (.of R)) :=
    ⟨inferInstance, regular_of_open f⟩
  let E : Spec (.of (Γ(Y, U.1) ⧸ Ideal.span (Set.range t))) ≅ Spec (.of R) :=
    Scheme.Spec.mapIso (Ideal.quotEquivOfEq hsum).symm.toCommRingCatIso.op
  have hE : E.hom ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (J.ideal U))) =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span (Set.range t)))) := by
    change Spec.map _ ≫ Spec.map _ = _
    rw [← Spec.map_comp]
    congr 1
  let P := J.isPullback_subschemeCover_map U
  let residual := E ≪≫ P.isoPullback
  have hresbase : residual.hom ≫ pullback.snd J.subschemeι U.2.fromSpec =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span (Set.range t)))) := by
    simpa only [residual, Iso.trans_hom, Category.assoc, P.isoPullback_hom_snd] using hE
  obtain ⟨residual', hresbase'⟩ :
      ∃ r : Spec (.of (Γ(Y, U.1) ⧸ Ideal.span (Set.range t))) ≅
          pullback J.radical.subschemeι U.2.fromSpec,
        r.hom ≫ pullback.snd J.radical.subschemeι U.2.fromSpec =
          Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span (Set.range t)))) := by
    rw [hrad]
    exact ⟨residual, hresbase⟩
  have hparam : ∀ q : PrimeSpectrum Γ(Y, U.1),
      ∃ s : List (Localization.AtPrime q.asIdeal),
        IsLocalRing.IsRegularSystemOfParameters s ∧
        List.Sublist (((List.ofFn t).filter
          (fun z ↦ @decide (z ∈ q.asIdeal) (Classical.propDecidable _))).map
          (algebraMap Γ(Y, U.1) (Localization.AtPrime q.asIdeal))) s := by
    intro q
    have hq : U.2.fromSpec q ∈ U.1 := (U.2.isoSpec.inv q).2
    obtain ⟨s, hs, hsub⟩ := labelled_parameters C hC U (fun i ↦ (e i).val)
      (Subtype.val_injective.comp e.injective) t (fun i ↦ ht₀ _) _ hq
    let : Algebra Γ(Y, U.1) (Y.presheaf.stalk (U.2.fromSpec q)) :=
      Y.presheaf.algebra_section_stalk ⟨_, hq⟩
    have : IsLocalization.AtPrime (Y.presheaf.stalk (U.2.fromSpec q)) q.asIdeal :=
      U.2.isLocalization_stalk' q hq
    let eqv := (IsLocalization.algEquiv q.asIdeal.primeCompl
      (Y.presheaf.stalk (U.2.fromSpec q)) (Localization.AtPrime q.asIdeal)).toRingEquiv
    have hm (v : Γ(Y, U.1)) :
        Y.presheaf.germ U.1 _ hq v ∈ IsLocalRing.maximalIdeal _ ↔ v ∈ q.asIdeal := by
      rw [IsLocalRing.mem_maximalIdeal]
      change ¬IsUnit (algebraMap Γ(Y, U.1) (Y.presheaf.stalk _) v) ↔ _
      rw [IsLocalization.AtPrime.isUnit_to_map_iff _ q.asIdeal]
      exact not_not
    refine ⟨s.map eqv, parameters_map_equiv eqv hs, ?_⟩
    have hsub' := hsub.map eqv
    rw [List.map_map] at hsub'
    have heq : (fun v ↦ eqv (Y.presheaf.germ U.1 _ hq v)) =
        algebraMap Γ(Y, U.1) (Localization.AtPrime q.asIdeal) := by
      funext v
      exact (IsLocalization.algEquiv q.asIdeal.primeCompl
        (Y.presheaf.stalk (U.2.fromSpec q)) (Localization.AtPrime q.asIdeal)).commutes v
    simp only [Function.comp_def, heq] at hsub'
    simpa only [hm] using hsub'
  have h_empty : I = ∅ → Ideal.span (Set.range t) = ⊥ := by
    intro hi
    subst I
    simp only [hsum, J, Finset.notMem_empty, iSup_false, iSup_bot,
      Scheme.IdealSheafData.ideal_bot, Pi.bot_apply]
  have hiR : IsIntegral (Spec (.of (Γ(Y, U.1) ⧸ Ideal.span (Set.range t)))) :=
    IsIntegral.of_isIso E.inv
  have : IsRegular (Spec (.of R)) := hregR.2
  have hrR : IsRegularScheme (Spec (.of (Γ(Y, U.1) ⧸ Ideal.span (Set.range t)))) := by
    exact ⟨LocallyOfFiniteType.isLocallyNoetherian E.hom, regular_of_open E.hom⟩
  let Q : SNCAffineStratumChart C I := {
    B := Γ(Y, U.1)
    v := U.2.fromSpec
    openImmersion := inferInstance
    inside := fun q i hi ↦ by
      have hq : U.2.fromSpec q ∈ U.1 := (U.2.isoSpec.inv q).2
      have hv := (hU hq).2
      change U.2.fromSpec q ∉ (⨆ j : {j : Fin a // j ∉ I}, (C j.val).support) at hv
      exact fun hc ↦ hv (le_iSup (fun j : {j : Fin a // j ∉ I} ↦ (C j.val).support)
        ⟨i, hi⟩ hc)
    regular := hregB
    noetherian := inferInstance
    domain := hdom
    separated := inferInstance
    t := t
    equations := fun i ↦ affine_equation (C (e i).val) U _ (ht₀ _)
    parameters := fun q ↦ by obtain ⟨s, hs⟩ := hparam q; exact ⟨inferInstance, s, hs⟩
    residualIso := residual'
    residualIso_base := hresbase'
    residual_integral := hiR
    residual_regular := hrR
    residual_connected := by have := hiR; infer_instance
    empty_ideal := h_empty
    empty_residual := fun hi ↦ by
      have hbij : Function.Bijective (Ideal.Quotient.mk (Ideal.span (Set.range t))) := by
        constructor
        · exact (RingHom.injective_iff_ker_eq_bot _).mpr (by rw [Ideal.mk_ker, h_empty hi])
        · exact Ideal.Quotient.mk_surjective
      have : IsIso (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span (Set.range t)))) :=
        (ConcreteCategory.isIso_iff_bijective _).mpr hbij
      infer_instance }
  obtain ⟨q, hq⟩ : x ∈ Set.range U.2.fromSpec := by rwa [U.2.range_fromSpec]
  exact ⟨Q, q, hq⟩

/-- A finite family of labelled affine open charts covers the reduced deepest stratum;
every chart and its nonempty deepest stratum are integral and regular. The chosen
family is empty when the stratum is empty. The family C is the supplied labelled
component presentation of the boundary, with exactly the clauses of its definition.

Source: ILO VIII Remark 4.2.2(i), printed pp. 118--119; Stacks 00NR
(blueprint: lem-sfb-snc-labelled-affine-stratum-charts).

Proof:
1. Finite type and regularity make Y Noetherian. Every scheme-theoretic component
   intersection is regular by hC. It is reduced, so its ideal equals its radical,
   using the kernel/vanishing-ideal description of a reduced closed immersion.
2. For each singleton intersection, the regular-quotient kernel theorem and the
   parameter quotient dimension formula give a regular generator at every stalk.
   IsRegularImmersion.of_stalk spreads these generators to affine neighbourhoods.
   Intersect finitely many such neighbourhoods and restrict their principal ideals
   to a common affine neighbourhood. The equations keep their given labels.
3. At any point let K be the vanishing labels. Their germs generate the kernel of
   the map onto the regular intersection stalk. Lift a minimal generating list of
   the quotient maximal ideal and append it to the given equations. Surjectivity
   and the kernel equality show that this list generates the ambient maximal ideal.
   Its length is the ambient dimension by hC and regularity of the quotient, so it
   is a regular system of parameters. Transport it to the prime localization.
4. Apply the regular normal decomposition to Y and its intersection. Retain the
   integral components through the chosen point. Remove the closed image of the
   other intersection components and restrict to the ambient component. Choose the
   common affine neighbourhood inside this open and outside unselected divisors.
   Both the chart and its residual intersection are nonempty opens in integral schemes.
5. The affine subscheme-cover pullback identifies the residual intersection with
   Spec of the quotient by the sum of the labelled principal ideals. This gives the
   residual isomorphism over the chart, integrality, regularity and connectedness.
   Affineness gives separatedness. When I is empty the ideal is zero and the quotient
   morphism is an isomorphism.
6. Every subset of a Noetherian space is compact. Select finitely many pointwise
   charts to cover the stratum. For the empty stratum select the empty family.
-/
theorem exists_sncAffineStratumCharts
    (k : Type u) [Field k] (Y : Scheme.{u}) (y : Y ⟶ Spec (.of k))
    [LocallyOfFiniteType y] [QuasiCompact y] [IsSeparated y]
    (hY : IsRegularScheme Y) (D : Y.IdealSheafData)
    (hD : IsStrictNormalCrossingsBoundary D)
    (a : ℕ) (C : Fin a → Y.IdealSheafData)
    (hC : Function.Injective (fun i ↦ (C i).support) ∧
      (∀ i, IsIntegral (C i).subscheme ∧ IsRegularScheme (C i).subscheme) ∧
      D.support = ⨆ i, (C i).support ∧
      ∀ s : Finset (Fin a), ∀ z : (⨆ i ∈ s, C i).subscheme,
        IsRegularScheme (⨆ i ∈ s, C i).subscheme ∧
        ringKrullDim (Y.presheaf.stalk ((⨆ i ∈ s, C i).subschemeι z)) =
          ringKrullDim ((⨆ i ∈ s, C i).subscheme.presheaf.stalk z) + (s.card : ℕ))
    (I : Finset (Fin a)) :
    ∃ (n : ℕ) (Q : Fin n → SNCAffineStratumChart C I),
      (∀ x : Y, x ∈ (⨆ i ∈ I, C i).support →
        (∀ i : Fin a, i ∉ I → x ∉ (C i).support) →
        ∃ (j : Fin n) (z : Spec (Q j).B), (Q j).v z = x) ∧
      ((¬ ∃ x : Y, x ∈ (⨆ i ∈ I, C i).support ∧
        ∀ i : Fin a, i ∉ I → x ∉ (C i).support) → n = 0) := by
  classical
  have _hBoundary := hD
  have : IsLocallyNoetherian Y := hY.1
  have : IsRegular Y := hY.2
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace y
  have : IsNoetherian Y := {}
  let S : Set Y := {x | x ∈ (⨆ i ∈ I, C i).support ∧
    ∀ i : Fin a, i ∉ I → x ∉ (C i).support}
  by_cases hS : S.Nonempty
  · have hlocal : ∀ x : S, ∃ (Q : SNCAffineStratumChart C I) (q : Spec Q.B),
        Q.v q = x.val := by
      intro x
      exact exists_chart_at Y a C (fun i ↦ (hC.2.1 i).2) hC.2.2.2 I x.val x.2.1 x.2.2
    choose Q q hq using hlocal
    have hopen : ∀ x : S, IsOpen (Set.range (Q x).v) := by
      intro x
      have := (Q x).openImmersion
      exact (Q x).v.isOpenEmbedding.isOpen_range
    have hcover : S ⊆ ⋃ x : S, Set.range (Q x).v := by
      intro x hx
      exact Set.mem_iUnion.mpr ⟨⟨x, hx⟩, q ⟨x, hx⟩, hq ⟨x, hx⟩⟩
    obtain ⟨T, hT⟩ := (TopologicalSpace.NoetherianSpace.isCompact S).elim_finite_subcover
      (fun x : S ↦ Set.range (Q x).v) hopen hcover
    let e : Fin (Fintype.card T) ≃ T := (Fintype.equivFin T).symm
    refine ⟨Fintype.card T, fun i ↦ Q (e i).val, ?_, ?_⟩
    · intro x hx hout
      obtain ⟨w, hw⟩ := Set.mem_iUnion.mp (hT ⟨hx, hout⟩)
      obtain ⟨hwT, z, hz⟩ := Set.mem_iUnion.mp hw
      refine ⟨e.symm ⟨w, hwT⟩, ?_⟩
      change ∃ z : Spec (Q (e (e.symm ⟨w, hwT⟩)).val).B,
        (Q (e (e.symm ⟨w, hwT⟩)).val).v z = x
      rw [e.apply_symm_apply]
      exact ⟨z, hz⟩
    · intro hempty
      exact False.elim (hempty hS)
  · refine ⟨0, Fin.elim0, ?_, fun _ ↦ rfl⟩
    intro x hx hout
    exact False.elim (hS ⟨x, hx, hout⟩)

end AlgebraicGeometry
