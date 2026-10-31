/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Coherent
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.Ideal.AssociatedPrime.Basic
public import Mathlib.Topology.GDelta.Basic
public import Mathlib.Topology.KrullDimension
import WeilConjectures.AlgebraicGeometry.CanonicalEmbeddedPointsGluing
import WeilConjectures.RingTheory.RemoveEmbeddedPrimes
import WeilConjectures.AlgebraicGeometry.NowhereDenseDimensionDrop
import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import WeilConjectures.Mathlib.Topology.KrullDimension
import WeilConjectures.AlgebraicGeometry.FiniteTypeModuleSupportClosed
import WeilConjectures.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian
import WeilConjectures.AlgebraicGeometry.QuasicoherentFiniteTypeAffine
import WeilConjectures.AlgebraicGeometry.CoherentKernelCokernelLocallyNoetherian
import WeilConjectures.AlgebraicGeometry.Modules.QuasiCoherentCokernelImage
import WeilConjectures.Algebra.Homology.ModuleStalkExact

/-! # Removing embedded associated points of a coherent module

Source: Stacks Project, Divisors, Tag 02OL (blueprint: lem-sc-hilbert-embedded-points).
The dimension clause is the additional support-dimension argument recorded in the DAG.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules

private theorem dimension_drop_of_closed_support
    (X : Scheme.{u}) [IsLocallyNoetherian X]
    (S T : Set X) (hS : IsClosed S) (hT : IsClosed T) (hTS : T ⊆ S)
    (hnow : IsNowhereDense {x : S | x.val ∈ T})
    (d : ℕ) (hd : topologicalKrullDim S = (d : WithBot ℕ∞)) :
    topologicalKrullDim T < (d : WithBot ℕ∞) := by
  let I := Scheme.IdealSheafData.vanishingIdeal ⟨S, hS⟩
  let Z := I.subscheme
  let i : Z ⟶ X := I.subschemeι
  have hrange : Set.range i = S := by
    rw [Scheme.IdealSheafData.range_subschemeι]
    exact Scheme.IdealSheafData.coe_support_vanishingIdeal _
  have : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian i
  let e : Z ≃ₜ S := i.isEmbedding.toHomeomorph.trans (Homeomorph.setCongr hrange)
  have hdim : topologicalKrullDim Z = (d : WithBot ℕ∞) := by
    rw [e.isHomeomorph.topologicalKrullDim_eq, hd]
  have : Nonempty Z := by
    by_contra hn
    have : IsEmpty Z := not_nonempty_iff.mp hn
    have hz : topologicalKrullDim Z = ⊥ := by
      unfold topologicalKrullDim
      apply Order.krullDim_eq_bot_iff.mpr
      exact ⟨fun C ↦ this.false C.2.nonempty.choose⟩
    rw [hz] at hdim
    exact WithBot.bot_ne_coe hdim
  have hnow' : IsNowhereDense (i ⁻¹' T) := by
    convert e.symm.isInducing.isNowhereDense_image hnow using 1
    ext z
    simp only [Set.mem_preimage, Set.mem_image, Set.mem_ofPred_eq]
    constructor
    · intro hz
      exact ⟨e z, hz, e.symm_apply_apply z⟩
    · rintro ⟨x, hx, hzx⟩
      subst z
      change (e (e.symm x)).val ∈ T
      simpa only [e.apply_symm_apply] using hx
  have hlt := Scheme.topologicalKrullDim_lt_of_isNowhereDense Z d hdim
    (i ⁻¹' T) (hT.preimage i.continuous) hnow'
  let f : (i ⁻¹' T) → X := fun z ↦ i z.val
  have hf : Topology.IsEmbedding f := i.isEmbedding.comp .subtypeVal
  have hfrange : Set.range f = T := by
    ext x
    constructor
    · rintro ⟨z, rfl⟩
      exact z.2
    · intro hx
      obtain ⟨z, rfl⟩ := hrange.symm ▸ hTS hx
      exact ⟨⟨z, hx⟩, rfl⟩
  rw [hf.topologicalKrullDim_eq_range, hfrange] at hlt
  exact hlt

private theorem support_closed (X : Scheme.{u}) [IsLocallyNoetherian X]
    (F : X.Modules) (hF : RingedSpace.IsCoherent X.toRingedSpace F) :
    IsClosed {x : X | ¬ Subsingleton (F.presheaf.stalk x)} := by
  obtain ⟨hq, ht⟩ := (isCoherent_iff_isQuasicoherent_and_isFiniteType X F).mp hF
  have := hq
  have := ht
  exact (finite_type_module_support_closed X F).2.2.2

private theorem support_subobject_subset (X : Scheme.{u}) (F : X.Modules)
    (K : Subobject F) :
    {x : X | ¬ Subsingleton ((K : X.Modules).presheaf.stalk x)} ⊆
      {x : X | ¬ Subsingleton (F.presheaf.stalk x)} := by
  intro x hx hs
  have : Subsingleton (F.presheaf.stalk x) := hs
  have hmono := (RingedSpace.module_stalk_exact X.toRingedSpace K.arrow).1
    (fun V ↦ (ModuleCat.mono_iff_injective _).mp
      ((SheafOfModules.evaluation X.ringCatSheaf (.op V)).map_mono K.arrow)) x
  have hinj := (ModuleCat.mono_iff_injective _).mp hmono
  change Function.Injective (RingedSpace.stalkAddMap X.toRingedSpace x K.arrow) at hinj
  apply hx
  constructor
  intro a b
  apply hinj
  exact hs.elim _ _

private theorem support_iff_affine (X : Scheme.{u}) (F : X.Modules)
    [F.IsQuasicoherent] [F.IsFiniteType] (V : X.affineOpens) (x : X) (hx : x ∈ V.1) :
    (¬ Subsingleton (F.presheaf.stalk x)) ↔
      V.2.primeIdealOf ⟨x, hx⟩ ∈ Module.support Γ(X, V.1) Γ(F, V.1) := by
  have := finite_sections_of_finiteType F V.2
  rw [(finite_type_module_support_closed X F).2.1 V x hx,
    Module.mem_support_iff_of_finite]

private noncomputable def affine_support_homeomorph (X : Scheme.{u}) (F : X.Modules)
    [F.IsQuasicoherent] [F.IsFiniteType] (V : X.affineOpens) :
    {x : {x : X | ¬ Subsingleton (F.presheaf.stalk x)} | x.val ∈ V.1} ≃ₜ
      Module.support Γ(X, V.1) Γ(F, V.1) := by
  let e : {x : {x : X | ¬ Subsingleton (F.presheaf.stalk x)} | x.val ∈ V.1} ≃ₜ
      {x : V.1 | ¬ Subsingleton (F.presheaf.stalk x.val)} :=
    { toEquiv :=
        { toFun := fun x ↦ ⟨⟨x.val.val, x.property⟩, x.val.property⟩
          invFun := fun x ↦ ⟨⟨x.val.val, x.property⟩, x.val.property⟩ }
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop }
  exact e.trans (V.2.isoSpec.hom.homeomorph.subtype
    (fun x ↦ support_iff_affine X F V x.val x.property))

private theorem nowhereDense_preimage_open {A B : Type*}
    [TopologicalSpace A] [TopologicalSpace B] (f : A → B)
    (hf : Continuous f) (ho : IsOpenMap f) (S : Set B) (hS : IsNowhereDense S) :
    IsNowhereDense (f ⁻¹' S) := by
  unfold IsNowhereDense at *
  rw [← ho.preimage_closure_eq_closure_preimage hf,
    ← ho.preimage_interior_eq_interior_preimage hf, hS, Set.preimage_empty]

private theorem affine_support_nowhereDense_image
    (X : Scheme.{u}) (F G : X.Modules)
    [F.IsQuasicoherent] [F.IsFiniteType] [G.IsQuasicoherent] [G.IsFiniteType]
    (V : X.affineOpens)
    (hnow : IsNowhereDense {p : Module.support Γ(X, V.1) Γ(F, V.1) |
      p.val ∈ Module.support Γ(X, V.1) Γ(G, V.1)}) :
    IsNowhereDense {x : {x : X | ¬ Subsingleton (F.presheaf.stalk x)} |
      x.val ∈ V.1 ∧ ¬ Subsingleton (G.presheaf.stalk x.val)} := by
  let e := affine_support_homeomorph X F V
  have h : Topology.IsEmbedding (fun p ↦ (e.symm p).val) :=
    Topology.IsEmbedding.subtypeVal.comp e.symm.isEmbedding
  have hi := h.isNowhereDense_image hnow
  convert hi using 1
  ext x
  simp only [Set.mem_ofPred_eq, Set.mem_image]
  constructor
  · rintro ⟨hxV, hxG⟩
    refine ⟨e ⟨x, hxV⟩, ?_, ?_⟩
    · exact (support_iff_affine X G V x.val hxV).mp hxG
    · exact congrArg Subtype.val (e.symm_apply_apply ⟨x, hxV⟩)
  · rintro ⟨p, hp, hpx⟩
    have hxV : x.val ∈ V.1 := by
      exact hpx ▸ (e.symm p).property
    refine ⟨hxV, ?_⟩
    apply (support_iff_affine X G V x.val hxV).mpr
    have he : e ⟨x, hxV⟩ = p := by
      apply e.symm.injective
      apply Subtype.ext
      simpa only [e.symm_apply_apply] using hpx.symm
    change (e ⟨x, hxV⟩).val ∈ Module.support Γ(X, V.1) Γ(G, V.1)
    rwa [he]

private theorem affine_support_nowhereDense_preimage
    (X : Scheme.{u}) (F G : X.Modules)
    [F.IsQuasicoherent] [F.IsFiniteType] [G.IsQuasicoherent] [G.IsFiniteType]
    (V : X.affineOpens)
    (hnow : IsNowhereDense {x : {x : X | ¬ Subsingleton (F.presheaf.stalk x)} |
      ¬ Subsingleton (G.presheaf.stalk x.val)}) :
    IsNowhereDense {p : Module.support Γ(X, V.1) Γ(F, V.1) |
      p.val ∈ Module.support Γ(X, V.1) Γ(G, V.1)} := by
  let e := affine_support_homeomorph X F V
  have h := nowhereDense_preimage_open Subtype.val continuous_subtype_val
    ((V.1.2.preimage continuous_subtype_val).isOpenMap_subtype_val) _ hnow
  have hi := e.isInducing.isNowhereDense_image h
  convert hi using 1
  ext p
  simp only [Set.mem_ofPred_eq, Set.mem_image, Set.mem_preimage]
  constructor
  · intro hp
    refine ⟨e.symm p, ?_, e.apply_symm_apply p⟩
    apply (support_iff_affine X G V (e.symm p).val.val (e.symm p).property).mpr
    change (e (e.symm p)).val ∈ Module.support Γ(X, V.1) Γ(G, V.1)
    simpa only [e.apply_symm_apply] using hp
  · rintro ⟨x, hx, rfl⟩
    exact (support_iff_affine X G V x.val.val x.property).mp hx

private theorem support_range_eq (X : Scheme.{u}) (F : X.Modules) (K : Subobject F)
    (V : X.affineOpens) :
    Module.support Γ(X, V.1) Γ((K : X.Modules), V.1) =
      Module.support Γ(X, V.1) (LinearMap.range (K.arrow.val.app (.op V.1)).hom) := by
  let f : Γ((K : X.Modules), V.1) →ₗ[Γ(X, V.1)] Γ(F, V.1) :=
    (K.arrow.val.app (.op V.1)).hom
  have hf : Function.Injective f := (ModuleCat.mono_iff_injective _).mp
    ((SheafOfModules.evaluation X.ringCatSheaf (.op V.1)).map_mono K.arrow)
  exact (LinearEquiv.ofInjective f hf).support_eq

private theorem subobject_le_of_affine_range (X : Scheme.{u}) (F : X.Modules)
    (K L : Subobject F)
    (h : ∀ V : X.affineOpens, LinearMap.range (K.arrow.val.app (.op V.1)).hom ≤
      LinearMap.range (L.arrow.val.app (.op V.1)).hom) : K ≤ L := by
  have hz : K.arrow ≫ cokernel.π L.arrow = 0 := by
    apply hom_ext
    intro W
    ext s
    let Q : TopCat.Sheaf AddCommGrpCat.{u} X :=
      ⟨(cokernel L.arrow).presheaf, (cokernel L.arrow).isSheaf⟩
    apply Q.eq_of_locally_eq'
      (fun i : {V : X.affineOpens // V.1 ≤ W} ↦ i.val.val) W
      (fun i ↦ homOfLE i.property)
    · intro x hx
      obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVW⟩ :=
        X.isBasis_affineOpens.exists_subset_of_mem_open hx W.2
      exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨⟨V, hV⟩, hVW⟩, hxV⟩
    · intro i
      change (cokernel L.arrow).presheaf.map (homOfLE i.property).op
        ((K.arrow ≫ cokernel.π L.arrow).app W s) =
          (cokernel L.arrow).presheaf.map (homOfLE i.property).op 0
      rw [map_zero]
      have hn := PresheafOfModules.naturality_apply
        (K.arrow ≫ cokernel.π L.arrow).val (homOfLE i.property).op s
      change (K.arrow ≫ cokernel.π L.arrow).app i.val.val
        ((K : X.Modules).presheaf.map (homOfLE i.property).op s) =
          (cokernel L.arrow).presheaf.map (homOfLE i.property).op
            ((K.arrow ≫ cokernel.π L.arrow).app W s) at hn
      rw [← hn]
      have ht : K.arrow.app i.val.val
          ((K : X.Modules).presheaf.map (homOfLE i.property).op s) ∈
          LinearMap.range (K.arrow.val.app (.op i.val.val)).hom := ⟨_, rfl⟩
      obtain ⟨s', hs'⟩ := h i.val ht
      change L.arrow.app i.val.val s' = K.arrow.app i.val.val
        ((K : X.Modules).presheaf.map (homOfLE i.property).op s) at hs'
      change (cokernel.π L.arrow).app i.val.val
        (K.arrow.app i.val.val ((K : X.Modules).presheaf.map _ s)) = 0
      rw [← hs']
      exact congrArg (fun q ↦ q.app i.val.val s') (cokernel.condition L.arrow)
  have hle := Subobject.mk_le_mk_of_comm
    (Abelian.monoLift L.arrow K.arrow hz) (Abelian.monoLift_comp L.arrow K.arrow hz)
  simpa only [Subobject.mk_arrow] using hle

/-- A coherent module on a locally Noetherian scheme has a maximal coherent subobject
whose support is nowhere dense in the original support. Its quotient has the same support,
no embedded associated points, and agrees with the original module on a dense open which
also meets the support densely. The kernel support has strictly smaller dimension when the
original support has finite positive dimension.

Support means nonzero stalks. Nowhere density and density in the support use the subspace
topology. No embedded associated points is expressed on every affine open by minimality
of every associated prime of the section module, as in `lem-sc-hilbert-difference`.
Mathlib defines associated primes using radicals of annihilators; on the Noetherian
coordinate rings here, `isAssociatedPrime_iff` identifies this with the source's
annihilator definition. The affine correspondence in Divisors, Tag 02OK, and
`definition-embedded` in that chapter justify the affine formulation.
The quotient is the categorical cokernel of the subobject inclusion.
Source: Stacks Project, Divisors, Tag 02OL (blueprint: lem-sc-hilbert-embedded-points).

Proof:
1. On every affine open, apply the affine embedded-prime removal theorem to the
   finite section module over the Noetherian coordinate ring. Choose its maximal
   submodule with nowhere-dense support.
2. The canonical gluing theorem gives a coherent subobject K with the chosen affine
   section ranges. Homeomorphisms of affine supports transfer nowhere density in both
   directions, so K has nowhere-dense support globally. Any larger coherent subobject
   with nowhere-dense support has the same affine ranges by local maximality. Sheaf
   separation and the kernel-of-cokernel property imply it is K. The affine cokernel
   theorem identifies quotient sections with the affine quotients. Their support and
   associated-prime conclusions transfer through these linear equivalences; the affine
   stalk-support criterion
   identifies their support with the support defined by nonzero stalks.
3. Let U be the complement of Supp(K), which is closed by coherence. The support of a
   subobject is contained in that of F (injectivity on stalks). Nowhere density in
   Supp(F) implies nowhere density in X, so U is dense in both. K restricts to zero
   there, as checked on germs of sections. Restriction preserves cokernels, so the
   restricted cokernel projection is an isomorphism.
4. Realize the closed set Supp(F) as the underlying space of its reduced closed
   subscheme. This subscheme is locally Noetherian. Apply the existing strict
   dimension-drop theorem to its closed nowhere-dense subset Supp(K), and transfer
   dimensions along the resulting homeomorphisms. The finite-dimension assumption
   excludes the empty ambient support; the empty kernel needs no separate case.
-/
theorem exists_maximal_nowhereDense_support_cokernel
    (X : Scheme.{u}) [IsLocallyNoetherian X] (F : X.Modules)
    (hF : RingedSpace.IsCoherent X.toRingedSpace F) :
    ∃ K : Subobject F,
      Maximal (fun L : Subobject F ↦
        RingedSpace.IsCoherent X.toRingedSpace (L : X.Modules) ∧
          IsNowhereDense {x : {x : X | ¬ Subsingleton (F.presheaf.stalk x)} |
            ¬ Subsingleton ((L : X.Modules).presheaf.stalk x.val)}) K ∧
      {x : X | ¬ Subsingleton ((cokernel K.arrow : X.Modules).presheaf.stalk x)} =
        {x : X | ¬ Subsingleton (F.presheaf.stalk x)} ∧
      (∀ (V : X.Opens) (_ : IsAffineOpen V) (p : Ideal Γ(X, V)),
        p ∈ associatedPrimes Γ(X, V) Γ((cokernel K.arrow : X.Modules), V) →
          Minimal (fun q : Ideal Γ(X, V) ↦
            q ∈ associatedPrimes Γ(X, V) Γ((cokernel K.arrow : X.Modules), V)) p) ∧
      (∃ U : X.Opens, Dense (U : Set X) ∧
        Dense {x : {x : X | ¬ Subsingleton (F.presheaf.stalk x)} | x.val ∈ U} ∧
        Nonempty ((cokernel K.arrow : X.Modules).over U ≅ F.over U)) ∧
      (∀ d : ℕ, 0 < d →
        topologicalKrullDim {x : X | ¬ Subsingleton (F.presheaf.stalk x)} =
          (d : WithBot ℕ∞) →
        topologicalKrullDim {x : X | ¬ Subsingleton ((K : X.Modules).presheaf.stalk x)} <
          topologicalKrullDim {x : X | ¬ Subsingleton (F.presheaf.stalk x)}) := by
  classical
  obtain ⟨hqF, htF⟩ := (isCoherent_iff_isQuasicoherent_and_isFiniteType X F).mp hF
  have := hqF
  have := htF
  have (V : X.affineOpens) : IsNoetherianRing Γ(X, V.1) :=
    IsLocallyNoetherian.component_noetherian V
  have (V : X.affineOpens) : Module.Finite Γ(X, V.1) Γ(F, V.1) :=
    finite_sections_of_finiteType F V.2
  choose N hN hNsupp hNass hNloc using fun V : X.affineOpens ↦
    Module.exists_maximal_nowhereDense_support_quotient Γ(X, V.1) Γ(F, V.1)
  obtain ⟨K, hKcoh, hKV⟩ :=
    exists_coherent_subobject_of_affine_maxima X F hF N hN
  obtain ⟨hqK, htK⟩ := (isCoherent_iff_isQuasicoherent_and_isFiniteType X _).mp hKcoh
  have := hqK
  have := htK
  have hK : Maximal (fun L : Subobject F ↦
      RingedSpace.IsCoherent X.toRingedSpace (L : X.Modules) ∧
        IsNowhereDense {x : {x : X | ¬ Subsingleton (F.presheaf.stalk x)} |
          ¬ Subsingleton ((L : X.Modules).presheaf.stalk x.val)}) K := by
    have hnow : IsNowhereDense
        {x : {x : X | ¬ Subsingleton (F.presheaf.stalk x)} |
          ¬ Subsingleton ((K : X.Modules).presheaf.stalk x.val)} := by
      let T : Set {x : X | ¬ Subsingleton (F.presheaf.stalk x)} :=
        {x | ¬ Subsingleton ((K : X.Modules).presheaf.stalk x.val)}
      have hT : IsClosed T := (support_closed X _ hKcoh).preimage continuous_subtype_val
      apply hT.isNowhereDense_iff.mpr
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro x hx
      obtain ⟨V, hV, hxV, _⟩ := exists_isAffineOpen_mem_and_subset
        (U := ⊤) (x := x.val) (by trivial)
      let W : X.affineOpens := ⟨V, hV⟩
      have hW : IsNowhereDense {p : Module.support Γ(X, V) Γ(F, V) |
          p.val ∈ Module.support Γ(X, V) Γ((K : X.Modules), V)} := by
        change IsNowhereDense {p : Module.support Γ(X, W.1) Γ(F, W.1) |
          p.val ∈ Module.support Γ(X, W.1) Γ((K : X.Modules), W.1)}
        rw [support_range_eq X F K W, hKV W]
        exact (hN W).1
      have hi := affine_support_nowhereDense_image X F (K : X.Modules) W hW
      have hm : x ∈ interior
          {y : {x : X | ¬ Subsingleton (F.presheaf.stalk x)} |
            y.val ∈ W.1 ∧ ¬ Subsingleton ((K : X.Modules).presheaf.stalk y.val)} := by
        have ho : IsOpen {y : {x : X | ¬ Subsingleton (F.presheaf.stalk x)} |
            y.val ∈ W.1} := W.1.2.preimage continuous_subtype_val
        change x ∈ interior
          ({y : {x : X | ¬ Subsingleton (F.presheaf.stalk x)} | y.val ∈ W.1} ∩ T)
        rw [interior_inter, ho.interior_eq]
        exact ⟨hxV, hx⟩
      exact Set.notMem_empty x (hi ▸ interior_mono subset_closure hm)
    refine ⟨⟨hKcoh, hnow⟩, ?_⟩
    intro L hL hKL
    obtain ⟨hqL, htL⟩ := (isCoherent_iff_isQuasicoherent_and_isFiniteType X _).mp hL.1
    have := hqL
    have := htL
    apply subobject_le_of_affine_range X F L K
    intro V
    have hr : LinearMap.range (K.arrow.val.app (.op V.1)).hom ≤
        LinearMap.range (L.arrow.val.app (.op V.1)).hom := by
      rintro s ⟨t, rfl⟩
      refine ⟨(Subobject.ofLE K L hKL).app V.1 t, ?_⟩
      exact congrArg (fun q ↦ q.app V.1 t) (Subobject.ofLE_arrow hKL)
    have hLN := affine_support_nowhereDense_preimage X F (L : X.Modules) V hL.2
    rw [support_range_eq X F L V] at hLN
    have hle := (hN V).2 hLN (by rwa [← hKV V])
    rwa [← hKV V] at hle
  have hQ := (isCoherent_kernel_cokernel_biprod_and_submodule X).2 F
    (K : X.Modules) K.arrow hF inferInstance hqK |>.2
  obtain ⟨hqQ, htQ⟩ := (isCoherent_iff_isQuasicoherent_and_isFiniteType X _).mp hQ
  have := hqQ
  have := htQ
  have hQaff (V : X.affineOpens) :
      Nonempty (Γ((cokernel K.arrow : X.Modules), V.1) ≃ₗ[Γ(X, V.1)]
        (Γ(F, V.1) ⧸ N V)) := by
    obtain ⟨e, _⟩ := (quasiCoherent_cokernel_image K.arrow).2.2.2.2.2.2.2.2 V |>.2.2.2
    exact ⟨e.symm.trans (Submodule.quotEquivOfEq _ _ (hKV V))⟩
  refine ⟨K, hK, ?_, ?_, ?_, ?_⟩
  · ext x
    obtain ⟨V, hV, hx, _⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤) (x := x)
      (by trivial)
    let W : X.affineOpens := ⟨V, hV⟩
    rw [Set.mem_ofPred, Set.mem_ofPred, support_iff_affine X _ W x hx,
      support_iff_affine X F W x hx, (hQaff W).some.support_eq, hNsupp W]
  · intro V hV p hp
    let W : X.affineOpens := ⟨V, hV⟩
    have he := LinearEquiv.AssociatedPrimes.eq (hQaff W).some
    have hmin := hNass W p (he ▸ hp)
    simpa only [← he] using hmin
  · let T : Set X := {x : X | ¬ Subsingleton ((K : X.Modules).presheaf.stalk x)}
    have hT : IsClosed T := support_closed X _ hKcoh
    let U : X.Opens := ⟨Tᶜ, hT.isOpen_compl⟩
    have hnow : IsNowhereDense T := by
      have himg := hK.1.2.image_val
      have heq : Subtype.val ''
          {x : {x : X | ¬ Subsingleton (F.presheaf.stalk x)} | x.val ∈ T} = T := by
        ext x
        exact ⟨fun ⟨y, hy, hyx⟩ ↦ hyx ▸ hy,
          fun hx ↦ ⟨⟨x, support_subobject_subset X F K hx⟩, hx, rfl⟩⟩
      change IsNowhereDense (Subtype.val ''
        {x : {x : X | ¬ Subsingleton (F.presheaf.stalk x)} | x.val ∈ T}) at himg
      rwa [heq] at himg
    have hzero : IsZero ((K : X.Modules).over U) := by
      apply (IsZero.iff_id_eq_zero _).mpr
      ext V z
      change z = 0
      apply TopCat.Presheaf.section_ext
        ((SheafOfModules.toSheaf X.ringCatSheaf).obj (K : X.Modules))
      intro x hx
      have hs : Subsingleton ((K : X.Modules).presheaf.stalk x) := by
        by_contra hn
        exact (V.unop.hom.le hx) hn
      exact hs.elim _ _
    let R := SheafOfModules.overFunctor X.ringCatSheaf U
    have hmapzero : R.map K.arrow = 0 := hzero.eq_of_src _ _
    have hpres : PreservesColimitsOfSize.{u, u} R := by
      dsimp [R, SheafOfModules.overFunctor]
      infer_instance
    have hπ : IsIso (R.map (cokernel.π K.arrow)) := by
      have hcomp : IsIso (cokernelComparison K.arrow R) := inferInstance
      have hπ' : IsIso (cokernel.π (R.map K.arrow)) := by
        exact cokernel.π_of_zero hmapzero
      rw [← π_comp_cokernelComparison]
      infer_instance
    refine ⟨U, ?_, ?_, ⟨(asIso (R.map (cokernel.π K.arrow))).symm⟩⟩
    · exact interior_eq_empty_iff_dense_compl.mp (hT.isNowhereDense_iff.mp hnow)
    · exact interior_eq_empty_iff_dense_compl.mp
        ((hT.preimage continuous_subtype_val).isNowhereDense_iff.mp hK.1.2)
  · intro d _ hd
    rw [hd]
    exact dimension_drop_of_closed_support X _ _ (support_closed X F hF)
      (support_closed X _ hKcoh) (support_subobject_subset X F K) hK.1.2 d hd

end AlgebraicGeometry.Scheme.Modules
