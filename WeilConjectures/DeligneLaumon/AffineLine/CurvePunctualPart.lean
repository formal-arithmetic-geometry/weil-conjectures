/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.DeligneLaumon.AffineLine.DirectImageUnit
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.WeilSheaf.MiddleExtension

/-!
# The punctual part of a Weil sheaf on a smooth curve

Let `X` be a smooth curve over `k₀`. This file proves the two inputs for the punctual part
`ker(F ⟶ j_* j^* F)` of a Weil sheaf `F` on `X` (see
`WeilConjectures.DeligneLaumon.AffineLine.PunctualPart`): a sheaf vanishing on a dense open is
punctual, and a punctual sheaf maps to zero in the direct image of a lisse sheaf.

## Main statements

- `IsOpen.finite_compl_of_genericPoints_subset`: in a Noetherian quasi-sober `T₀` space of
  dimension at most one, an open set containing all generic points has finite complement.
- `AlgebraicGeometry.WeilSheaf.support_finite_of_isZero_upperStar_of_dense`: a Weil sheaf on a
  smooth curve vanishing on a dense open is punctual.
- `AlgebraicGeometry.WeilSheaf.eq_zero_of_support_finite_of_isLisse`: every morphism from a
  punctual Weil sheaf to the direct image of a lisse sheaf on an open of a smooth curve vanishes.
-/

@[expose] public section

universe u

open CategoryTheory Limits Topology TopologicalSpace

section Topology

variable {α : Type*} [TopologicalSpace α] [QuasiSober α] [T0Space α]

/-- In a quasi-sober `T₀` space of dimension at most one, a point outside an open set containing
all generic points is closed: a proper specialization of it would give a chain of three
irreducible closed subsets, the last one being its irreducible component. -/
theorem isClosed_singleton_of_genericPoints_subset (h : topologicalKrullDim α ≤ 1) {U : Set α}
    (hU : genericPoints α ⊆ U) {x : α} (hx : x ∉ U) : IsClosed ({x} : Set α) := by
  by_contra hcl
  obtain ⟨y, hy, hyx⟩ : ∃ y ∈ closure {x}, y ≠ x := by
    by_contra! H
    exact hcl (closure_subset_iff_isClosed.mp fun y hy ↦ H y hy)
  have hC := irreducibleComponent_mem_irreducibleComponents x
  have hCc := isClosed_of_mem_irreducibleComponents _ hC
  have hg := hC.1.isGenericPoint_genericPoint hCc
  have hcU : hC.1.genericPoint ∈ U := hU (by
    change closure {hC.1.genericPoint} ∈ irreducibleComponents α
    rw [hg.def]
    exact hC)
  let Y : IrreducibleCloseds α := ⟨closure {y}, isIrreducible_singleton.closure, isClosed_closure⟩
  let Z : IrreducibleCloseds α := ⟨closure {x}, isIrreducible_singleton.closure, isClosed_closure⟩
  let T : IrreducibleCloseds α := ⟨irreducibleComponent x, hC.1, hCc⟩
  have h₁ : Y < Z := by
    refine lt_of_le_of_ne (show closure {y} ⊆ closure {x} from
      closure_minimal (by simpa using hy) isClosed_closure) fun h ↦ hyx ?_
    exact (inseparable_iff_closure_eq.mpr congr(($h : Set α))).eq
  have h₂ : Z < T := by
    refine lt_of_le_of_ne (show closure {x} ⊆ irreducibleComponent x from
      closure_minimal (Set.singleton_subset_iff.2 mem_irreducibleComponent) hCc) fun h ↦ hx ?_
    have hgx : IsGenericPoint x (irreducibleComponent x) := by
      rw [isGenericPoint_def]
      exact congr(($h : Set α))
    rwa [hgx.eq hg]
  let q₁ : LTSeries (IrreducibleCloseds α) := (RelSeries.singleton _ Y).snoc Z h₁
  let q : LTSeries (IrreducibleCloseds α) :=
    q₁.snoc T (by rw [show q₁.last = Z from RelSeries.last_snoc _ _ _]; exact h₂)
  have hq : q.length = 2 := rfl
  have := Order.LTSeries.length_le_krullDim q
  rw [hq] at this
  have h2 : ((2 : ℕ) : WithBot ℕ∞) ≤ 1 := this.trans h
  exact absurd h2 (by decide)

/-- In a Noetherian quasi-sober `T₀` space of dimension at most one, an open set containing all
generic points has finite complement: the irreducible components of the complement are closed
points. -/
theorem IsOpen.finite_compl_of_genericPoints_subset [NoetherianSpace α]
    (h : topologicalKrullDim α ≤ 1) {U : Set α} (hU : IsOpen U) (hg : genericPoints α ⊆ U) :
    Uᶜ.Finite := by
  obtain ⟨S, hSf, hSc, hSi, hS⟩ := NoetherianSpace.exists_finite_set_isClosed_irreducible
    hU.isClosed_compl
  have key : ∀ t ∈ S, ∃ z, t = {z} := by
    intro t ht
    obtain ⟨z, hz⟩ := QuasiSober.sober (hSi t ht) (hSc t ht)
    have hzU : z ∉ U := by
      have : z ∈ Uᶜ := hS ▸ Set.mem_sUnion_of_mem hz.mem ht
      exact this
    exact ⟨z, by rw [← hz.def, (isClosed_singleton_of_genericPoints_subset h hg hzU).closure_eq]⟩
  rw [hS]
  refine hSf.sUnion fun t ht ↦ ?_
  obtain ⟨z, rfl⟩ := key t ht
  exact Set.finite_singleton z

end Topology

namespace AlgebraicGeometry

/-- On a scheme smooth of relative dimension one over a field, the generic point of an
irreducible component is not a closed point: closed points have codimension one. -/
theorem not_isClosed_singleton_of_mem_genericPoints {K : Type u} [Field K] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of K)) [SmoothOfRelativeDimension 1 f] {c : X} (hc : c ∈ genericPoints X) :
    ¬ IsClosed ({c} : Set X) := by
  intro hcl
  have h := coheight_eq_of_smoothOfRelativeDimension_of_isClosed f 1 hcl
  have hm : ¬ IsMax c := by
    intro hm
    rw [← Order.coheight_eq_zero] at hm
    rw [hm] at h
    exact absurd h (by decide)
  obtain ⟨b, hb⟩ := not_isMax_iff.1 hm
  have hbc : b ⤳ c := Scheme.le_iff_specializes.1 hb.le
  obtain rfl := mem_genericPoints_iff_forall_specializes.1 hc b hbc
  exact lt_irrefl _ hb

variable {k₀ : Type u} [Field k₀]

/-- A dense open of a smooth curve over `k₀` misses only finitely many closed points. -/
theorem finite_setOf_notMem_of_dense {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
    [SmoothOfRelativeDimension 1 (X ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))] {O : Set X} (hO : IsOpen O)
    (hd : Dense O) : {x : X.finitePoints | x.1 ∉ O}.Finite := by
  have : IsNoetherian X := isNoetherian_of_locallyOfFiniteType (X ↘ Spec (.of k₀))
  have hdim := topologicalKrullDim_le_of_smoothOfRelativeDimension (X ↘ Spec (.of k₀)) 1
  exact (hO.finite_compl_of_genericPoints_subset (by exact_mod_cast hdim)
    (Scheme.genericPoints_subset_of_isOpen_of_dense hO hd)).preimage
    Subtype.val_injective.injOn

namespace WeilSheaf

variable [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
  {X U : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))] [U.Over (Spec (CommRingCat.of k₀))]

/-- A Weil sheaf on a smooth curve vanishing on a dense open is punctual. -/
theorem support_finite_of_isZero_upperStar_of_dense
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
    [SmoothOfRelativeDimension 1 (X ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))] (j : U ⟶ X) [IsOpenImmersion j]
    [j.IsOver (Spec (CommRingCat.of k₀))] (hj : Dense (Set.range j.base)) (G : WeilSheaf k₀ l X)
    (hG : IsZero ((upperStar j).obj G)) : G.support.Finite := by
  refine (finite_setOf_notMem_of_dense (k₀ := k₀) j.isOpenEmbedding.isOpen_range hj).subset
    fun x hx ↦ ?_
  rintro ⟨y, hy⟩
  have hy' : y ∈ U.finitePoints := Scheme.Hom.mem_finitePoints_of_isOpenImmersion j (hy ▸ x.2)
  have h := (mem_support_upperStar_iff j G ⟨y, hy'⟩).2 (by convert hx)
  rw [support_eq_empty_of_isZero hG] at h
  exact h

open scoped ProEtale in
/-- **The direct image of a lisse sheaf has no punctual subsheaf**: every morphism from a Weil
sheaf `G` of finite support on a smooth curve `X` to the direct image `j_* N` of a lisse Weil
sheaf on an open `j : U ↪ X` vanishes. Let `V₀` be the complement of the support of `G`, so that
`G|_{V₀} = 0`. Every point of the geometric fibre `Ū` specializes from a generic point `η` of
`Ū`; it lies over a generic point of `X` (the projection `X̄ ⟶ X` is flat), which is not a closed
point, hence lies in `V₀`. The adjoint `j̄^* G ⟶ N` thus vanishes on `Ū ∩ V̄₀`, and a morphism to
the lisse `N` vanishing there vanishes
(`AlgebraicGeometry.ProEtale.IsAdicLisseSheaf.eq_zero_of_adicUpperStar_map_eq_zero`). -/
theorem eq_zero_of_support_finite_of_isLisse
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
    [SmoothOfRelativeDimension 1 (X ↘ Spec (CommRingCat.of k₀))]
    (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j] [j.IsOver (Spec (CommRingCat.of k₀))]
    {N : WeilSheaf k₀ l U} (hN : N.IsLisse) {G : WeilSheaf k₀ l X} (hG : G.support.Finite)
    (i : G ⟶ (lowerStar j).obj N) : i = 0 := by
  classical
  set S : Set X := ⋃ x ∈ G.support, {x.1} with hS
  have hSc : IsClosed S :=
    hG.isClosed_biUnion fun x _ ↦ X.isClosed_singleton_of_mem_finitePoints x.2
  let V₀ : X.Opens := ⟨Sᶜ, hSc.isOpen_compl⟩
  -- `G` vanishes on `V₀`
  have hz : IsZero ((upperStar V₀.ι).obj G) := by
    refine isZero_upperStar_of_forall_notMem_support V₀.ι G fun y hy ↦ ?_
    have hV : V₀.ι.base y.1 ∈ (V₀ : Set X) := by
      rw [Scheme.Opens.ι_apply]
      exact y.1.2
    exact hV (Set.mem_biUnion hy rfl)
  set jb := Scheme.Hom.geometricFiberMap j (comp_over j (Spec (CommRingCat.of k₀)))
  set gb := Scheme.Hom.geometricFiberMap V₀.ι (comp_over V₀.ι (Spec (CommRingCat.of k₀)))
  set prX := (X ↘ Spec (CommRingCat.of k₀)).geometricFiberProj
  have : Flat prX :=
    MorphismProperty.pullback_fst _ _
      (Flat.SpecMap_iff.mpr (RingHom.flat_algebraMap_iff.mpr inferInstance) :
        Flat (Spec.map (CommRingCat.ofHom (algebraMap k₀ (AlgebraicClosure k₀)))))
  -- every point of `Ū` specializes from a point of `Ū ∩ V̄₀`
  have hgen : ∀ y, ∃ p : (Limits.pullback jb gb : Scheme.{u}),
      (pullback.fst jb gb).base p ⤳ y := by
    intro y
    have hC := irreducibleComponent_mem_irreducibleComponents y
    have hg := hC.1.isGenericPoint_genericPoint (isClosed_of_mem_irreducibleComponents _ hC)
    set η := hC.1.genericPoint
    have hη : η ∈ genericPoints _ := by
      change closure {η} ∈ irreducibleComponents _
      rw [hg.def]
      exact hC
    -- `prX (jb η)` is a generic point of `X`
    have hξg : prX.base (jb.base η) ∈ genericPoints X := by
      rw [mem_genericPoints_iff_forall_specializes]
      intro c hc
      obtain ⟨η', hη'η, rfl⟩ := Flat.generalizingMap prX hc
      obtain ⟨η'', rfl⟩ : η' ∈ Set.range jb.base :=
        hη'η.mem_open jb.isOpenEmbedding.isOpen_range ⟨η, rfl⟩
      rw [mem_genericPoints_iff_forall_specializes.1 hη η''
        (jb.isOpenEmbedding.isInducing.specializes_iff.1 hη'η)]
    have hξ : prX.base (jb.base η) ∈ (V₀ : Set X) := by
      intro hS'
      obtain ⟨x, -, hxe⟩ := Set.mem_iUnion₂.1 hS'
      rw [Set.mem_singleton_iff] at hxe
      refine not_isClosed_singleton_of_mem_genericPoints (X ↘ Spec (CommRingCat.of k₀)) hξg ?_
      rw [hxe]
      exact X.isClosed_singleton_of_mem_finitePoints x.2
    obtain ⟨v, hv1, -⟩ := Scheme.exists_preimage_of_isPullback
      (Scheme.Hom.isPullback_geometricFiberMap V₀.ι (comp_over V₀.ι _))
      (jb.base η) ⟨_, hξ⟩ (by rw [Scheme.Opens.ι_apply])
    obtain ⟨p, hp1, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := jb) (g := gb) η v
      hv1.symm
    exact ⟨p, hp1 ▸ hg.specializes mem_irreducibleComponent⟩
  -- the adjoint morphism `j̄^* G ⟶ N` vanishes
  have hcar : IsZero ((gb)^*ᵃ[l].obj G.obj.carrier) := isZero_iff_isZero_carrier.1 hz
  let adj := ProEtale.adicUpperStarLowerStarAdjunction l jb
  let φ := (adj.homEquiv _ _).symm i.hom.hom.f
  have hφ : (pullback.fst jb gb)^*ᵃ[l].map φ = 0 :=
    ((Functor.map_isZero ((pullback.snd jb gb)^*ᵃ[l]) hcar).of_iso
      ((ProEtale.adicUpperStarCompIso l (pullback.condition (f := jb) (g := gb))).app
        G.obj.carrier)).eq_of_src _ _
  have hφ0 : φ = 0 :=
    ProEtale.IsAdicLisseSheaf.eq_zero_of_adicUpperStar_map_eq_zero _ hgen hN φ hφ
  have hf : i.hom.hom.f = 0 := by
    rw [← (adj.homEquiv _ _).apply_symm_apply i.hom.hom.f]
    change adj.homEquiv _ _ φ = 0
    rw [hφ0, Adjunction.homEquiv_unit, Functor.map_zero, comp_zero]
  exact ObjectProperty.hom_ext _ <| ObjectProperty.hom_ext _ <| Endofunctor.Algebra.Hom.ext hf

end WeilSheaf

end AlgebraicGeometry
