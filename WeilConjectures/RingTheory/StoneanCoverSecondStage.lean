/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.RingTheory.ProEtale.WContractible
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import WeilConjectures.RingTheory.IndPrincipalZariski
import WeilConjectures.RingTheory.ThmPeIndetaleRefinementPart1Supplement2
import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra

/-!
# Realizing a Stonean cover of the components

Source: the blueprint of the Weil conjectures, chapter `sec-proetale-coefficients`,
unit `sk-thm-pe-wc-cover` (blueprint: det-pe-wc-cover-second-stage); Stacks Project,
Tag 097D and the surrounding w-local component lemmas.

The canonical ring is the graph restriction `WContractification.PullbackProfinite`.
Its spectrum is the fiber product with the prescribed map of component spaces.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace PrimeSpectrum ConnectedComponents

namespace Algebra

/-- The canonical restriction map for inclusion of closed component subsets.

Source: Stacks Project, Tag 097C; blueprint `det-pe-wc-cover-second-stage`.
It is induced by the inclusion of the clopen-neighbourhood indexing categories.
(blueprint: det-pe-wc-cover-second-stage) -/
noncomputable def stoneanRestrictionMap {C : Type u} [CommRing C]
    {Z Z' : Set (ConnectedComponents (PrimeSpectrum C))} (h : Z ⊆ Z') :
    WContractification.Restriction Z' →ₐ[C] WContractification.Restriction Z :=
  (colimit.pre (WContractification.Restriction.diag Z)
    (OrderHom.toFunctor
      ({ toFun := fun W => ⟨W.val, fun _ hx => W.property (h hx)⟩
         monotone' := fun _ _ hW => hW } :
        {W : Clopens (PrimeSpectrum C) // ConnectedComponents.mk ⁻¹' Z' ⊆ W} →o
          {W : Clopens (PrimeSpectrum C) // ConnectedComponents.mk ⁻¹' Z ⊆ W})).op).hom

/-- The product of the component restrictions over the parts of a finite clopen partition.

Source: Stacks Project, Tag 097D and the blueprint's finite-partition construction
(blueprint: det-pe-wc-cover-second-stage).
A discrete quotient of compact `S` is finite; its fibres are exactly the nonempty
clopen parts. This includes the empty quotient when `S` is empty. -/
noncomputable def stoneanPartitionStage (C S : Type u) [CommRing C]
    [TopologicalSpace S] (f : C(S, ConnectedComponents (PrimeSpectrum C)))
    (Q : DiscreteQuotient S) : CommAlgCat C :=
  .of C (∀ a : Q, WContractification.Restriction (f '' (Q.proj ⁻¹' {a})))

/-- The finite-stage map for a refinement, using restriction on every finer part.

Source: Stacks Project, Tag 097D (blueprint: det-pe-wc-cover-second-stage). -/
noncomputable def stoneanPartitionMap {C S : Type u} [CommRing C]
    [TopologicalSpace S] (f : C(S, ConnectedComponents (PrimeSpectrum C)))
    {Q Q' : DiscreteQuotient S} (h : Q' ≤ Q) :
    stoneanPartitionStage C S f Q ⟶ stoneanPartitionStage C S f Q' :=
  CommAlgCat.ofHom (AlgHom.pi fun a =>
    (stoneanRestrictionMap (Set.image_mono (DiscreteQuotient.fiber_subset_ofLE h a))).comp
      (Pi.evalAlgHom C _ (DiscreteQuotient.ofLE h a)))

/-- The directed diagram of finite clopen-partition stages.

Source: Stacks Project, Tag 097D (blueprint: det-pe-wc-cover-second-stage).
The opposite of the refinement order makes finer partitions later stages. -/
noncomputable def stoneanPartitionDiagram (C S : Type u) [CommRing C]
    [TopologicalSpace S] (f : C(S, ConnectedComponents (PrimeSpectrum C))) :
    (DiscreteQuotient S)ᵒᵖ ⥤ CommAlgCat C where
  obj Q := stoneanPartitionStage C S f Q.unop
  map g := stoneanPartitionMap f g.unop.le
  map_id Q := by
    apply CommAlgCat.hom_ext
    apply AlgHom.ext
    intro r
    funext a
    obtain ⟨s, rfl⟩ := Q.unop.proj_surjective a
    change stoneanRestrictionMap _ (r (Q.unop.proj s)) = r (Q.unop.proj s)
    obtain ⟨c, hc⟩ := WContractification.Restriction.algebraMap_surjective
      (f '' (Q.unop.proj ⁻¹' {Q.unop.proj s})) (r (Q.unop.proj s))
    rw [← hc]
    exact (stoneanRestrictionMap _).commutes c
  map_comp {Q Q' Q''} g g' := by
    apply CommAlgCat.hom_ext
    apply AlgHom.ext
    intro r
    funext a
    obtain ⟨s, rfl⟩ := Q''.unop.proj_surjective a
    change stoneanRestrictionMap _ (r (Q.unop.proj s)) =
      stoneanRestrictionMap _ (stoneanRestrictionMap _ (r (Q.unop.proj s)))
    obtain ⟨c, hc⟩ := WContractification.Restriction.algebraMap_surjective
      (f '' (Q.unop.proj ⁻¹' {Q.unop.proj s})) (r (Q.unop.proj s))
    rw [← hc]
    simp only [AlgHom.commutes]

/-- The spectrum map to the fiber product `Spec C ×ₚ₀ S`.

Source: Stacks Project, Tag 097D (blueprint: det-pe-wc-cover-second-stage).
This is obtained from the canonical `fiberHomeo`, with the two factors exchanged. -/
noncomputable def stoneanCoverPointMap (C S : Type u) [CommRing C]
    [TopologicalSpace S] [CompactSpace S] [T2Space S]
    [TotallyDisconnectedSpace S]
    (f : C(S, ConnectedComponents (PrimeSpectrum C)))
    (q : PrimeSpectrum (WContractification.PullbackProfinite C S f)) :
    {z : PrimeSpectrum C × S // ConnectedComponents.mk z.1 = f z.2} := by
  let y := WContractification.PullbackProfinite.fiberHomeo C S f q
  exact ⟨(y.1.2, y.1.1), y.2.symm⟩

-- A zero in the restriction colimit already vanishes on one clopen neighbourhood.
private theorem restriction_zero_iff {R : Type u} [CommRing R]
    (Z : Set (ConnectedComponents (PrimeSpectrum R))) (r : R) :
    algebraMap R (WContractification.Restriction Z) r = 0 ↔
      ∃ W : Clopens (PrimeSpectrum R), ConnectedComponents.mk ⁻¹' Z ⊆ W ∧
        algebraMap R (WContractification.RestrictClopen W) r = 0 := by
  constructor
  · intro hr
    let top : {W : Clopens (PrimeSpectrum R) // ConnectedComponents.mk ⁻¹' Z ⊆ W} :=
      ⟨⊤, le_top⟩
    have heq :
        (colimit.ι (WContractification.Restriction.diag Z) (Opposite.op top)).hom
            (algebraMap R (WContractification.RestrictClopen top.val) r) =
          (colimit.ι (WContractification.Restriction.diag Z) (Opposite.op top)).hom 0 := by
      exact (((colimit.ι (WContractification.Restriction.diag Z)
        (Opposite.op top)).hom.commutes r).trans hr).trans (map_zero _).symm
    obtain ⟨k, g, g', hgg⟩ :=
      (Types.FilteredColimit.isColimit_eq_iff
        (WContractification.Restriction.diag Z ⋙ forget (CommAlgCat R))
        (isColimitOfPreserves (forget (CommAlgCat R))
          (colimit.isColimit (WContractification.Restriction.diag Z)))).mp heq
    refine ⟨k.unop.val, k.unop.property, ?_⟩
    change ((WContractification.Restriction.diag Z).map g).hom
      (algebraMap R _ r) = ((WContractification.Restriction.diag Z).map g').hom 0 at hgg
    exact (((WContractification.Restriction.diag Z).map g).hom.commutes r).symm.trans
      (hgg.trans (map_zero _))
  · rintro ⟨W, hW, hr⟩
    let ι := (colimit.ι (WContractification.Restriction.diag Z)
      (Opposite.op ⟨W, hW⟩)).hom
    exact (ι.commutes r).symm.trans ((congrArg ι hr).trans (map_zero ι))

private theorem idempotent_mul_eq_zero {R A : Type u} [CommRing R] [CommRing A]
    [Algebra R A] {e r : R} (he : IsIdempotentElem e) [IsLocalization.Away e A]
    (h : algebraMap R A r = 0) : e * r = 0 := by
  obtain ⟨⟨_, n, rfl⟩, hn⟩ := (IsLocalization.map_eq_zero_iff (Submonoid.powers e) A r).mp h
  have hh := congrArg (e * ·) hn
  simpa only [← mul_assoc, ← pow_succ', he.pow_succ_eq, mul_zero] using hh

private noncomputable def partitionFunctionMap {C S : Type u} [CommRing C]
    [TopologicalSpace S] (f : C(S, ConnectedComponents (PrimeSpectrum C)))
    (Q : DiscreteQuotient S) :
    LocallyConstant Q C →ₐ[C] stoneanPartitionStage C S f Q where
  toFun r a := algebraMap C _ (r a)
  map_one' := by apply funext; intro a; exact map_one _
  map_zero' := by apply funext; intro a; exact map_zero _
  map_add' r r' := by apply funext; intro a; exact map_add _ _ _
  map_mul' r r' := by apply funext; intro a; exact map_mul _ _ _
  commutes' r := by apply funext; intro a; rfl

private noncomputable def partitionFunctionCocone {C S : Type u} [CommRing C]
    [TopologicalSpace S] [CompactSpace S]
    (f : C(S, ConnectedComponents (PrimeSpectrum C))) :
    Cocone (LocallyConstant.discreteQuotientDiag C S) where
  pt := colimit (stoneanPartitionDiagram C S f)
  ι :=
    { app Q := CommAlgCat.ofHom (partitionFunctionMap f Q.unop) ≫
        colimit.ι (stoneanPartitionDiagram C S f) Q
      naturality {Q Q'} g := by
        have hh : (LocallyConstant.discreteQuotientDiag C S).map g ≫
              CommAlgCat.ofHom (partitionFunctionMap f Q'.unop) =
            CommAlgCat.ofHom (partitionFunctionMap f Q.unop) ≫
              (stoneanPartitionDiagram C S f).map g := by
          apply CommAlgCat.hom_ext
          apply AlgHom.ext
          intro r
          funext a
          exact ((stoneanRestrictionMap _).commutes _).symm
        simp only [← Category.assoc, hh]
        rw [Category.assoc, colimit.w]
        simp }

private noncomputable def partitionFunction {C S : Type u} [CommRing C]
    [TopologicalSpace S] [CompactSpace S]
    (f : C(S, ConnectedComponents (PrimeSpectrum C))) :
    LocallyConstant S C →ₐ[C] (colimit (stoneanPartitionDiagram C S f) : CommAlgCat C) :=
  ((LocallyConstant.isColimitDiscreteQuotientCocone C S).desc
    (partitionFunctionCocone f)).hom

private theorem partitionFunction_apply {C S : Type u} [CommRing C]
    [TopologicalSpace S] [CompactSpace S]
    (f : C(S, ConnectedComponents (PrimeSpectrum C)))
    (Q : DiscreteQuotient S) (r : LocallyConstant Q C) :
    partitionFunction f (LocallyConstant.comapₐ C ⟨Q.proj, Q.proj_continuous⟩ r) =
      (colimit.ι (stoneanPartitionDiagram C S f) (Opposite.op Q)).hom
        (fun a ↦ algebraMap C _ (r a)) :=
  DFunLike.congr_fun (congrArg CommAlgCat.Hom.hom
    ((LocallyConstant.isColimitDiscreteQuotientCocone C S).fac
      (partitionFunctionCocone f) (Opposite.op Q))) r

private theorem partitionFunction_surjective {C S : Type u} [CommRing C]
    [TopologicalSpace S] [CompactSpace S]
    (f : C(S, ConnectedComponents (PrimeSpectrum C))) :
    Function.Surjective (partitionFunction f) := by
  classical
  intro b
  obtain ⟨Q, r, rfl⟩ := Concrete.isColimit_exists_rep
    (stoneanPartitionDiagram C S f)
    (colimit.isColimit (stoneanPartitionDiagram C S f)) b
  choose r' hr' using fun a ↦ WContractification.Restriction.algebraMap_surjective
    (f '' (Q.unop.proj ⁻¹' {a})) (r a)
  refine ⟨LocallyConstant.comapₐ C ⟨Q.unop.proj, Q.unop.proj_continuous⟩
    ⟨r', IsLocallyConstant.of_discrete r'⟩, ?_⟩
  rw [partitionFunction_apply]
  congr 1
  exact funext hr'

private theorem restriction_killed {R : Type u} [CommRing R]
    (Z : Set (ConnectedComponents (PrimeSpectrum R))) {e r : R}
    (he : IsIdempotentElem e)
    (hZ : ConnectedComponents.mk ⁻¹' Z ⊆ (basicOpen e : Set (PrimeSpectrum R)))
    (hr : e * r = 0) : algebraMap R (WContractification.Restriction Z) r = 0 := by
  let W := isIdempotentElemEquivClopens ⟨e, he⟩
  apply (restriction_zero_iff Z r).mpr
  refine ⟨W, hZ, ?_⟩
  have heW : (isIdempotentElemEquivClopens.symm W).val = e := by
    exact congrArg Subtype.val (isIdempotentElemEquivClopens.symm_apply_apply ⟨e, he⟩)
  have hh : (isIdempotentElemEquivClopens.symm W).val * r = 0 := heW ▸ hr
  exact (IsLocalization.map_eq_zero_iff
    (Submonoid.powers (isIdempotentElemEquivClopens.symm W).val) _ r).mpr
    ⟨⟨_, Submonoid.mem_powers _⟩, hh⟩

-- Both constructions are quotients of locally constant functions. A kernel element
-- is killed by an idempotent equal to one on a neighbourhood of the graph. Refining
-- a partition to make that idempotent constant compares the two kernel conditions.
private theorem partitionFunction_zero_iff {C S : Type u} [CommRing C]
    [TopologicalSpace S] [CompactSpace S] [T2Space S] [TotallyDisconnectedSpace S]
    (f : C(S, ConnectedComponents (PrimeSpectrum C))) (r : LocallyConstant S C) :
    partitionFunction f r = 0 ↔
      algebraMap (LocallyConstant S C) (WContractification.PullbackProfinite C S f) r = 0 := by
  classical
  constructor
  · intro hr
    let Q := r.discreteQuotient
    have heq : (colimit.ι (stoneanPartitionDiagram C S f) (Opposite.op Q)).hom
        (fun a ↦ algebraMap C _ (r.lift a)) =
      (colimit.ι (stoneanPartitionDiagram C S f) (Opposite.op Q)).hom 0 := by
      rw [← partitionFunction_apply, map_zero]
      exact hr
    obtain ⟨Q', g, g', hgg⟩ :=
      (Types.FilteredColimit.isColimit_eq_iff
        (stoneanPartitionDiagram C S f ⋙ forget (CommAlgCat C))
        (isColimitOfPreserves (forget (CommAlgCat C))
          (colimit.isColimit (stoneanPartitionDiagram C S f)))).mp heq
    let v : Q'.unop → C := fun a ↦ r.lift (DiscreteQuotient.ofLE g.unop.le a)
    have hv : ∀ a : Q'.unop,
        algebraMap C (WContractification.Restriction (f '' (Q'.unop.proj ⁻¹' {a})))
          (v a) = 0 := by
      intro a
      have hgg0 := hgg.trans (map_zero ((stoneanPartitionDiagram C S f).map g').hom)
      have hh := congrFun hgg0 a
      let ρ : WContractification.Restriction
          (f '' (Q.proj ⁻¹' {DiscreteQuotient.ofLE g.unop.le a})) →ₐ[C]
          WContractification.Restriction (f '' (Q'.unop.proj ⁻¹' {a})) :=
        stoneanRestrictionMap
          (Set.image_mono (DiscreteQuotient.fiber_subset_ofLE g.unop.le a))
      change ρ (algebraMap C _ (v a)) = 0 at hh
      exact (ρ.commutes (v a)).symm.trans hh
    choose W hW hz using fun a ↦
      (restriction_zero_iff (f '' (Q'.unop.proj ⁻¹' {a})) (v a)).mp (hv a)
    let e : Q'.unop → C := fun a ↦ (isIdempotentElemEquivClopens.symm (W a)).val
    let h : LocallyConstant S C :=
      LocallyConstant.comapₐ C ⟨Q'.unop.proj, Q'.unop.proj_continuous⟩
        ⟨e, IsLocallyConstant.of_discrete e⟩
    have hid : IsIdempotentElem h := by
      ext s
      exact (isIdempotentElemEquivClopens.symm (W (Q'.unop.proj s))).property
    have hmul : h * r = 0 := by
      ext s
      have hh := idempotent_mul_eq_zero
        (isIdempotentElemEquivClopens.symm (W (Q'.unop.proj s))).property
        (hz (Q'.unop.proj s))
      change e (Q'.unop.proj s) * r s = 0
      convert hh using 1
      dsimp [v]
      rw [DiscreteQuotient.ofLE_proj]
      rfl
    apply restriction_killed _ hid ?_ hmul
    rw [WContractification.PullbackProfinite.preimage_mk_Z]
    rintro _ ⟨⟨s, x⟩, hx, rfl⟩
    change h s ∉ x.asIdeal
    have hh : x ∈ (W (Q'.unop.proj s) : Set (PrimeSpectrum C)) :=
      hW _ ⟨s, rfl, hx⟩
    change x ∈ (basicOpen (e (Q'.unop.proj s)) : Set (PrimeSpectrum C))
    change x ∈ (W (Q'.unop.proj s)).toOpens at hh
    change x ∈ basicOpen (isIdempotentElemEquivClopens.symm (W (Q'.unop.proj s))).val
    rw [basicOpen_isIdempotentElemEquivClopens_symm]
    exact hh
  · intro hr
    obtain ⟨W, hW, hz⟩ := (restriction_zero_iff
      (WContractification.PullbackProfinite.Z C S f) r).mp hr
    let h := (isIdempotentElemEquivClopens.symm W).val
    have hid : IsIdempotentElem h := (isIdempotentElemEquivClopens.symm W).property
    have hmul : h * r = 0 := idempotent_mul_eq_zero hid hz
    let Q := h.discreteQuotient ⊓ r.discreteQuotient
    let v : Q → C := fun a ↦ r.lift (DiscreteQuotient.ofLE inf_le_right a)
    have hv : ∀ a : Q, algebraMap C
        (WContractification.Restriction (f '' (Q.proj ⁻¹' {a}))) (v a) = 0 := by
      intro a
      obtain ⟨s, rfl⟩ := Q.proj_surjective a
      have he : IsIdempotentElem (h s) := by
        exact DFunLike.congr_fun hid s
      have hv' : v (Q.proj s) = r s := by
        dsimp [v]
        rw [DiscreteQuotient.ofLE_proj]
        rfl
      rw [hv']
      apply restriction_killed _ he ?_ (DFunLike.congr_fun hmul s)
      rintro x ⟨t, ht, hft⟩
      have hst : h t = h s := by
        have hh := congrArg (DiscreteQuotient.ofLE (show Q ≤ h.discreteQuotient from
          inf_le_left)) ht
        have hh' := congrArg (fun a ↦ h.lift a) hh
        simp only [DiscreteQuotient.ofLE_proj] at hh'
        exact hh'
      have hx : LocallyConstant.toPrimeSpectrum (t, x) ∈ (W : Set _) := by
        apply hW
        rw [WContractification.PullbackProfinite.preimage_mk_Z]
        exact ⟨(t, x), hft, rfl⟩
      have hx' : LocallyConstant.toPrimeSpectrum (t, x) ∈
          (basicOpen h : Set _) := by
        change LocallyConstant.toPrimeSpectrum (t, x) ∈ basicOpen
          (isIdempotentElemEquivClopens.symm W).val
        rw [basicOpen_isIdempotentElemEquivClopens_symm]
        exact hx
      change h s ∉ x.asIdeal
      change h t ∉ x.asIdeal at hx'
      rwa [hst] at hx'
    have heq : r = LocallyConstant.comapₐ C ⟨Q.proj, Q.proj_continuous⟩
        ⟨v, IsLocallyConstant.of_discrete v⟩ := by
      ext s
      change r s = r.lift (DiscreteQuotient.ofLE inf_le_right (Q.proj s))
      rw [DiscreteQuotient.ofLE_proj]
      rfl
    rw [heq, partitionFunction_apply]
    have hz' : (fun a ↦ algebraMap C
        (WContractification.Restriction (f '' (Q.proj ⁻¹' {a}))) (v a)) = 0 :=
      funext hv
    change (colimit.ι (stoneanPartitionDiagram C S f) (Opposite.op Q)).hom
      (fun a ↦ algebraMap C (WContractification.Restriction (f '' (Q.proj ⁻¹' {a})))
        (v a)) = 0
    exact (congrArg _ hz').trans (map_zero _)

/-- Realization of a Stonean cover by the finite partition colimit.

Source: Stacks Project, Tags 097C and 097D, and the blueprint
(blueprint: det-pe-wc-cover-second-stage).
The first conjunct identifies the specified partition colimit with the existing
canonical graph-restriction ring, as a `C`-algebra. These constructions are
canonically isomorphic. The displayed normalization on finite-stage functions fixes
that comparison: every stage is a quotient of the finite product of copies of `C`.

Proof, following the node step by step:

1. Put $X=\operatorname{Spec}C$. The component lemma identifies $P$ with the closed-point space
of $X$, in particular $P$ is profinite and $\pi$ is continuous. The inverse image of a clopen
$U\subseteq P$ is clopen in $X$, so the clopen-idempotent correspondence supplies the unique
$e_U$ with $D(e_U)=\pi^{-1}(U)$. If $V\subseteq U$, then $e_Ve_U=e_V$: both sides are the
idempotent of $D(e_V)\cap D(e_U)=D(e_V)$. Thus the image of $e_U$ is 1 in $C_{e_V}$, and the
localization universal property supplies the transition map. These maps compose uniquely. The
clopen neighborhoods of any $Z$ form a small nonempty directed set under reverse inclusion
(intersect two, with $P$ a neighborhood).
Dependencies: det-pe-wlocal-components, lem-weil-pbc-spec-clopen-idempotent, def-weil-ring-
localization-away, lem-weil-pbc-localization-away-universal-property.

2. For closed $Z\subseteq P$, let $M_Z=\{e_U:U\supseteq Z\text{ clopen}\}$. This is a
multiplicative subset: $e_P=1$ and $e_Ue_V=e_{U\cap V}$ by the clopen-idempotent correspondence.
A $C$-algebra map into a ring $T$ factors through every $C_{e_U}$ if and only if every element
of $M_Z$ maps to a unit; the factorizations are unique and hence compatible. The colimit
universal property and localization universal property thus identify $C_Z$ canonically with
$M_Z^{-1}C$. By the localization-spectrum embedding lemma its spectrum is the subspace of primes
avoiding $M_Z$, namely $\bigcap_U\pi^{-1}(U)$. This is $\pi^{-1}(Z)$: if $p\notin Z$, a clopen
neighborhood of $p$ disjoint from $Z$ exists in the profinite space, and its complement is a
neighborhood of $Z$ missing $p$. This proves the required restriction homeomorphism without
invoking a general spectrum-colimit theorem.
Dependencies: lem-weil-pbc-spec-clopen-idempotent, lem-weil-pbc-ring-localization-universal-
property, lem-weil-pbc-localization-away-universal-property, def-weil-pbc-category-colimit, lem-
weil-pbc-localization-spectrum-embedding.

3. At $x\in\pi^{-1}(Z)$ the colimit-localization theorem gives
$(C_Z)_x=\varinjlim_U(C_{e_U})_{x_U}$. Here each $(C_{e_U})_{x_U}$ is canonically $C_x$. Write
$e=e_U$. Since $e\notin x$, the localization universal property gives a map to $C_x$ sending
$(a/e^n)/(b/e^m)$ to $a/b$; here $b\notin x$ because the denominator is outside $x_U$, and
$e/1=1$ in $C_x$ since it is an invertible idempotent. In the other direction
$a/b\mapsto(a/1)/(b/1)$ is defined by inverting $C\setminus x$. In $C_e$ too the invertible
idempotent $e/1$ equals 1, so the two displayed fraction formulas compose to the identity in
both directions. A transition $C_{e_U}\to C_{e_V}$ for $V\subseteq U$ sends the image of each
$a\in C$ to the image of that same $a$; after prime localization its conjugate under these
isomorphisms sends every $a/b\in C_x$ to $a/b$. Thus this localized diagram is the constant
diagram $C_x$ with identity transitions. Its colimit is $C_x$: a compatible cocone on a nonempty
directed constant diagram is a single map from $C_x$, since any two indices have a common upper
bound. All the isomorphisms are of $C$-algebras.
Dependencies: lem-weil-pbc-filtered-colimit-localization-at-prime, def-weil-ring-localization-
away, def-weil-pbc-localization-at-prime, lem-weil-pbc-ring-localization-universal-property.

4. Each $f(A)$ is closed: a part $A$ is closed in compact $S$, its continuous image is compact,
and $P$ is Hausdorff. If $Z\subseteq Z^\prime$, every neighborhood used for $C_{Z^\prime}$ also
occurs for $C_Z$; the colimit universal property therefore gives a canonical map
$C_{Z^\prime}\to C_Z$, compatible with inclusions. This supplies exactly the transition maps for
refinements in the statement. Common refinements of finite clopen partitions consist of their
nonempty intersections, so the partition index is small, nonempty and directed. If $S$ is empty
its unique partition is the empty partition; since $f:S\to P$ exists and is surjective, $P$ is
empty too.
Dependencies: def-weil-pbc-category-colimit.

5. For a fixed partition $\mathcal Q$, index simultaneously by a choice of clopen neighborhood
$U_A\supseteq f(A)$ for every $A\in\mathcal Q$. This finite product of neighborhood index sets
is directed; each coordinate projection is cofinal, since all other coordinates can be chosen to
be $P$. Filtered colimits commute with finite products of underlying sets, and the comparison
here is a ring homomorphism because addition, multiplication and 1 are componentwise. Thus
$D_{\mathcal Q}=\varinjlim_{(U_A)}\prod_A C_{e_{U_A}}$ as rings and as $C$-algebras. One can
check bijectivity directly as well: a finite tuple of fractions lifts at a tuple of stages, and
equality of two such tuples holds after taking an upper bound of their finitely many equality-
witness stages. The elementwise colimit and equality lemmas justify these assertions for ring
colimits. By the definition, $C\to D_{\mathcal Q}$ is ind-Zariski. Stability under filtered
colimits then gives $C\to D$ ind-Zariski, hence ind-etale by the same definition; the stability
theorem makes it weakly etale, whose flatness is part of the cited definition.
Dependencies: lem-weil-pbc-filtered-colimits-commute-finite-limits, lem-weil-pbc-filtered-
colimit-algebras-elementwise, lem-weil-pbc-filtered-colimit-rings-zero, def-weil-pbc-ind-etale-
algebra, lem-weil-pbc-ind-etale-stability.

6. A compatible choice of a part $A_{\mathcal Q}$ for every partition has the finite
intersection property: a common refinement supplies a nonempty part inside any finite selection.
Its intersection is nonempty by compactness (otherwise the open complements cover $S$, and a
finite subcover contradicts that property). It contains at most one point, because distinct
points of a profinite space are separated by a clopen, and its two-part partition separates
them. Write the intersection as $\{s\}$. If $p\in\bigcap_{\mathcal Q}f(A_{\mathcal Q})$, the
sets $f^{-1}(p)\cap A_{\mathcal Q}$ are closed and have the finite intersection property: for
any finite list of partitions choose a common refinement $\mathcal R$; as $p\in f(A_{\mathcal
R})$, some $t\in A_{\mathcal R}$ has $f(t)=p$, and compatibility puts this $t$ in every selected
part. Compactness therefore gives a point in their intersection. That point is $s$, and
$p=f(s)$. Conversely $f(s)$ belongs to every image. The part maps also identify $S$
topologically with the compatible part families: the maps to finite partitions are continuous
and their inverse images include every clopen of $S$, a basis of its profinite topology. For
empty $S$ there are no such compatible families, as the empty partition has no part.
Dependencies: .

7. By the finite-affine-coproduct theorem, $\operatorname{Spec}D_{\mathcal Q}$ is the disjoint
union over $A\in\mathcal Q$ of $\operatorname{Spec}C_{f(A)}$. By step 2 its points are $(x,A)$
with $\pi(x)\in f(A)$, and its topology is the subspace topology from $X\times\mathcal Q$ with
$\mathcal Q$ finite discrete. Refinement contraction sends $(x,A^\prime)$ to $(x,A)$ for
$A^\prime\subseteq A$, by the definition of the transition maps. A prime $q$ of $D$ contracts to
a compatible family $q_{\mathcal Q}=(x,A_{\mathcal Q})$. If $S$ is nonempty, the one-part
partition has ring $C_P=C$, so all first coordinates are the same $x$. Step 6 supplies a unique
$s$ with $\bigcap_{\mathcal Q}A_{\mathcal Q}=\{s\}$ and forces $\pi(x)=f(s)$. For empty $S$, the
empty partition has zero ring and no primes. Conversely any pair $(x,s)$ with $\pi(x)=f(s)$
defines a compatible family of stage primes by choosing the part containing $s$.
Dependencies: lem-weil-pbc-finite-affine-coproduct-spectrum, def-weil-affine-spectrum.

8. We construct a prime of $D$ from that stage-prime family rather than assuming a spectrum-
limit theorem. Every $d\in D$ is represented by $d_{\mathcal Q}\in D_{\mathcal Q}$, by the
elementwise colimit lemma. Declare $d\in q$ exactly when $d_{\mathcal Q}\in q_{\mathcal Q}$.
This is independent of the representative: two representatives have equal images at a common
later stage by the eventual-equality lemma, and contraction compatibility makes membership in
the two stage primes equivalent to membership there. Addition and multiplication by arbitrary
elements are checked by taking all representatives to one common stage; there $q_{\mathcal Q}$
is an ideal. Likewise $1\notin q$, and if $ab\in q$, represent $a,b$ at one stage; their product
represents $ab$, so stage primeness puts $a$ or $b$ in $q$. Thus $q$ is prime and contracts to
every prescribed $q_{\mathcal Q}$. Any prime with these contractions has this same membership
test on every element of $D$, so is equal to $q$. Together with step 7 this proves the asserted
bijection of points.
Dependencies: lem-weil-pbc-filtered-colimit-algebras-elementwise, lem-weil-pbc-filtered-colimit-
rings-zero.

9. The bijection is a homeomorphism onto $X\times_PS$. Its $X$ coordinate is the continuous
spectrum map. Each partition coordinate is continuous, since it is the contraction map to
$\operatorname{Spec}D_{\mathcal Q}$ followed by the map to its finite disjoint-union index
$\mathcal Q$. Step 6 says that these partition coordinates generate the topology of $S$, so the
map to $S$ is continuous. For the inverse, the map $(x,s)\mapsto(x,A_{\mathcal Q}(s))$ into
$\operatorname{Spec}D_{\mathcal Q}\subseteq X\times\mathcal Q$ is continuous: on the clopen
slice $s\in A$ it is the map to the subspace $\pi^{-1}(f(A))\subseteq X$, and the compatibility
equation ensures the image lies there. If $d\in D$ is represented by $d_{\mathcal Q}$, the
membership construction in step 8 gives that the inverse image of the basic open $D(d)$ is
exactly the inverse image of $D(d_{\mathcal Q})$ under this continuous stage map. It is
therefore open. Basic opens form a basis, so the inverse is continuous. This proves the topology
claim without any unstated preservation-of-limits result.
Dependencies: lem-weil-pbc-finite-affine-coproduct-spectrum, def-weil-affine-spectrum, lem-weil-
pbc-filtered-colimit-algebras-elementwise, lem-weil-pbc-spec-localization-away-basic-open.

10. At the prime $q=(x,s)$ of $D$, let $q_{\mathcal Q}$ be its contraction to $D_{\mathcal Q}$.
The colimit-localization theorem gives $D_q=\varinjlim_{\mathcal Q}(D_{\mathcal Q})_{q_{\mathcal
Q}}$. The product-prime-localization theorem identifies the stage local ring with
$(C_{f(A_{\mathcal Q}(s))})_x$, which is $C_x$ by step 3. Under these identifications, $a/b\in
C_x$ is the fraction of the diagonal images of $a,b\in C$ in the stage local ring, with $b\notin
x$. Refinement maps fix those diagonal images, hence send this fraction to $a/b$ in the next
copy of $C_x$. These fractions exhaust $C_x$, so every conjugated transition is the identity.
The colimit of this nonempty directed constant diagram is $C_x$ by the cocone argument in step
3. Thus the canonical $C$-algebra map $C_x\to D_q$ is an isomorphism. This finishes clause 2.
Since $f$ is surjective, for every $x\in X$ there is $s$ with $f(s)=\pi(x)$, so steps 7–8 make
$\operatorname{Spec}D\to X$ surjective. Combined with flatness in step 5, the flat-surjective-
spectrum criterion gives faithful flatness and finishes clause 1.
Dependencies: lem-weil-pbc-filtered-colimit-localization-at-prime, lem-weil-pbc-product-prime-
localization, lem-weil-pbc-flat-surjective-spectrum-faithfully-flat.

11. We now use the topological identification $\operatorname{Spec}D=X\times_PS$ from step 9. If
$m$ is closed in $X$, then $(m,s)$ is closed, since its singleton is the intersection of the
inverse images of the closed singletons $\{m\}$ and $\{s\}$. For arbitrary $(x,s)$, let $m$ be
the unique closed specialization of $x$ in the w-local space $X$. The component lemma gives
$\pi(m)=\pi(x)=f(s)$. The point $(m,s)$ exists, and $(x,s)$ specializes to it: for each product
neighborhood $V\times W$ of $(m,s)$, $x\in V$ because $x$ specializes to $m$, and $s\in W$.
Hence if $(x,s)$ is closed then $x=m$. This proves exactly that the closed points are pairs with
first coordinate closed. Any closed specialization of $(x,s)$ has form $(m^\prime,s)$ (Hausdorff
$S$ has no nontrivial specializations), with $m^\prime$ a closed specialization of $x$, hence
$m^\prime=m$. The closed-point set is the inverse image of the closed set $X^c$. Thus $D$ is
w-local by the cited definition: closed maximal-point locus and a unique maximal specialization
of every prime.
Dependencies: det-pe-wlocal-components, det-pe-wlocal-strict-contractible.

12. The component lemma identifies $X^c\to P$ homeomorphically. Let $m(p)$ be its inverse.
Projection $(\operatorname{Spec}D)^c\to S$ is a continuous bijection with continuous inverse
$s\mapsto(m(f(s)),s)$ into $X\times_PS$. It is therefore a homeomorphism. This proves clause 3,
without assuming that an arbitrary closed-point space is Hausdorff before verifying w-locality.
At a closed point $(m,s)$, step 10 gives $D_{(m,s)}\simeq C_m$, which is strictly henselian by
the w-strict locality of $C$. Consequently $D$ is w-strictly local. Applying the component lemma
now to the w-local spectrum of $D$ identifies its component space with
$(\operatorname{Spec}D)^c\simeq S$. This space is extremally disconnected by hypothesis, so the
cited definition makes $D$ w-contractible, proving clause 4. If $C$ is the zero ring, both $P$
and $S$ are empty and the empty partition gives $D=0$; all local-ring assertions are vacuous and
the same definitions and flat-surjective criterion apply.
Dependencies: det-pe-wlocal-components, det-pe-wlocal-strict-contractible.

The comparison with graph restriction sends each finite-part selector idempotent
to the characteristic function of that part. Expanding the restrictions as
neighbourhood colimits, finite products commute with these filtered colimits;
locally constant functions factor through a finite discrete quotient. Intersecting
clopen graph neighbourhoods gives a common refinement, so both constructions have
the same compatible cocones. This gives the canonical comparison isomorphism.
-/
theorem stonean_cover_second_stage (C : Type u) [CommRing C]
    [IsWStrictlyLocalRing C]
    (S : Type u) [TopologicalSpace S] [CompactSpace S] [T2Space S]
    [TotallyDisconnectedSpace S] [ExtremallyDisconnected S]
    (f : C(S, ConnectedComponents (PrimeSpectrum C)))
    (hf : Function.Surjective f) :
    (∃ e : (colimit (stoneanPartitionDiagram C S f) : CommAlgCat C) ≃ₐ[C]
        WContractification.PullbackProfinite C S f,
      ∀ (Q : DiscreteQuotient S) (r : Q → C),
        e ((colimit.ι (stoneanPartitionDiagram C S f) (Opposite.op Q)).hom
          (fun a => algebraMap C _ (r a))) =
        algebraMap (LocallyConstant S C) (WContractification.PullbackProfinite C S f)
          (LocallyConstant.comapₐ C ⟨Q.proj, Q.proj_continuous⟩
            ⟨r, IsLocallyConstant.of_discrete r⟩)) ∧
      Algebra.IsIndPrincipalZariski C (WContractification.PullbackProfinite C S f) ∧
      RingHom.FaithfullyFlat (algebraMap C (WContractification.PullbackProfinite C S f)) ∧
      Algebra.IndEtale C (WContractification.PullbackProfinite C S f) ∧
      Function.Bijective (stoneanCoverPointMap C S f) ∧
      (∀ q : PrimeSpectrum (WContractification.PullbackProfinite C S f),
        Function.Bijective (Localization.localRingHom
          (q.asIdeal.comap (algebraMap C (WContractification.PullbackProfinite C S f)))
          q.asIdeal (algebraMap C (WContractification.PullbackProfinite C S f)) rfl)) ∧
      IsWLocalRing (WContractification.PullbackProfinite C S f) ∧
      closedPoints (PrimeSpectrum (WContractification.PullbackProfinite C S f)) =
        PrimeSpectrum.comap (algebraMap C (WContractification.PullbackProfinite C S f)) ⁻¹'
          closedPoints (PrimeSpectrum C) ∧
      IsHomeomorph (fun q :
          closedPoints (PrimeSpectrum (WContractification.PullbackProfinite C S f)) =>
        (stoneanCoverPointMap C S f q.1).1.2) ∧
      IsWContractibleRing (WContractification.PullbackProfinite C S f) := by
  classical
  let D := WContractification.PullbackProfinite C S f
  have pb := WContractification.PullbackProfinite.isPullback C S f
  let : IsWLocalRing D :=
    ⟨ConnectedComponents.wlocalSpace_of_isPullback pb⟩
  have hlocal : ∀ (q : Ideal D) [q.IsPrime], Function.Bijective
      (Localization.localRingHom (q.comap (algebraMap C D)) q (algebraMap C D) rfl) :=
    fun q _ ↦ (Algebra.IndZariski.bijectiveOnStalks C D).bijective_localRingHom q
  have hclosed :=
    ConnectedComponents.preimage_closedPoints_eq_closedPoints_of_isPullback pb
  have hlift := ConnectedComponents.isHomeomorph_lift_of_isPullback pb
  let : IsWStrictlyLocalRing D := by
    refine ⟨fun m hm ↦ ?_⟩
    have : m.IsPrime := hm.isPrime
    let y : PrimeSpectrum D := ⟨m, inferInstance⟩
    have hy : y ∈ closedPoints (PrimeSpectrum D) :=
      (PrimeSpectrum.isClosed_singleton_iff_isMaximal y).mpr hm
    have hxc : WContractification.PullbackProfinite.projSpec C S f y ∈
        closedPoints (PrimeSpectrum C) := by
      rw [← hclosed] at hy
      exact hy
    have : (m.comap (algebraMap C D)).IsMaximal :=
      (PrimeSpectrum.isClosed_singleton_iff_isMaximal _).mp hxc
    have := IsWStrictlyLocalRing.isStrictlyHenselianLocalRing_localization
      (R := C) (m.comap (algebraMap C D))
    exact IsStrictlyHenselianLocalRing.of_ringEquiv
      (RingEquiv.ofBijective _ (hlocal m))
  have hpoint : Function.Bijective (stoneanCoverPointMap C S f) := by
    constructor
    · intro q q' h
      apply (WContractification.PullbackProfinite.fiberHomeo C S f).injective
      apply Subtype.ext
      exact Prod.ext (congrArg (fun z ↦ z.val.2) h) (congrArg (fun z ↦ z.val.1) h)
    · rintro ⟨⟨x, s⟩, h⟩
      refine ⟨(WContractification.PullbackProfinite.fiberHomeo C S f).symm
        ⟨(s, x), h.symm⟩, ?_⟩
      simp [stoneanCoverPointMap]
  have hc : IsHomeomorph (fun q : closedPoints (PrimeSpectrum D) ↦
      (stoneanCoverPointMap C S f q.val).val.2) := by
    have heq : (fun q : closedPoints (PrimeSpectrum D) ↦
        (stoneanCoverPointMap C S f q.val).val.2) =
        (fun q : closedPoints (PrimeSpectrum D) ↦
          Continuous.connectedComponentsLift
            (WContractification.PullbackProfinite.projT C S f).continuous
            (ConnectedComponents.mk q.val)) := by
      funext q
      rw [Continuous.connectedComponentsLift_apply_coe]
      exact WContractification.PullbackProfinite.fst_fiberHomeo C S f q.val
    rw [heq]
    exact hlift.comp
      (WLocalSpace.isHomeomorph_connectedComponents_closedPoints (PrimeSpectrum D))
  refine ⟨?_, Algebra.isIndPrincipalZariski_of_bijective_localRingHom C D hlocal,
    ?_, inferInstance, hpoint, (fun q ↦ hlocal q.asIdeal), inferInstance,
    hclosed.symm, hc, ?_⟩
  · let α : LocallyConstant S C →ₐ[C] D := IsScalarTower.toAlgHom C _ _
    have hα : Function.Surjective α :=
      WContractification.Restriction.algebraMap_surjective
        (WContractification.PullbackProfinite.Z C S f)
    have hk : RingHom.ker (partitionFunction f).toRingHom = RingHom.ker α.toRingHom := by
      ext r
      exact partitionFunction_zero_iff f r
    let e := (Ideal.quotientKerAlgEquivOfSurjective (partitionFunction_surjective f)).symm.trans
      ((Ideal.quotientEquivAlgOfEq C hk).trans
        (Ideal.quotientKerAlgEquivOfSurjective hα))
    refine ⟨e, fun Q r ↦ ?_⟩
    have hp := partitionFunction_apply f Q ⟨r, IsLocallyConstant.of_discrete r⟩
    change partitionFunction f _ =
      (colimit.ι (stoneanPartitionDiagram C S f) (Opposite.op Q)).hom
        (fun a ↦ algebraMap C _ (r a)) at hp
    exact (congrArg e hp).symm.trans (by
      dsimp [e]
      erw [Ideal.quotientKerAlgEquivOfSurjective_symm_apply,
        Ideal.quotientEquivAlgOfEq_mk, Ideal.quotientKerAlgEquivOfSurjective_mk])
  · exact (RingHom.faithfullyFlat_algebraMap_iff).mpr
      (WContractification.PullbackProfinite.faithfullyFlat C S f hf)
  · have : ExtremallyDisconnected (ConnectedComponents (PrimeSpectrum D)) :=
      extremallyDisconnected_of_homeo hlift.homeomorph.symm
    exact ⟨inferInstance⟩

end Algebra
