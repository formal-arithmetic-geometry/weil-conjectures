/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NE
-/
module

public import Mathlib.Topology.Spectral.Basic
public import Mathlib.Topology.KrullDimension
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.Topology.Sheaves.Sheaf
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.Algebra.Category.Grp.AB
public import WeilConjectures.Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf

import WeilConjectures.CategoryTheory.Abelian.ExtEpiEffacement
import Sheaf.Topology.ProfiniteCohomologyVanishing
import Sheaf.Topology.PuncturedNeighborhoodCohomologyColimit
import Sheaf.Topology.PuncturedSpectralNeighborhoodDimension
import WeilConjectures.Mathlib.Topology.Sheaves.Flasque
import WeilConjectures.Topology.SpectralSpace.Constructible
import WeilConjectures.Mathlib.Topology.KrullDimension
import Mathlib.Topology.Sheaves.LocallySurjective
import Mathlib.CategoryTheory.Sites.SheafCohomology.MayerVietoris
import Mathlib.Topology.Sheaves.MayerVietoris
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.CategoryTheory.Limits.ConcreteCategory.Filtered

/-! # Cohomological dimension of a spectral space

Source: Stacks Project, Cohomology of Sheaves, Tag 0A3G, part (1),
`proposition-cohomological-dimension-spectral`.
(blueprint: lem-sfb-spectral-space-cohomology-dimension)

The dimension is bounded above, rather than required to equal the bound. In particular,
the empty space is allowed, with Krull dimension minus infinity. No Noetherian assumption
is needed. Cohomology uses the recorded abelian-sheaf cohomology at the top open.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true

universe u v

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite Topology

namespace TopCat.Sheaf

private lemma freeOpenHomEquiv_postcomp
    {T : TopCat.{u}}
    (U : Opens T)
    {A B : CategoryTheory.Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{u}}
    (f : A ⟶ B) (a : freeOpen U ⟶ A) :
    freeOpenHomEquiv U B (a ≫ f) = f.hom.app (op U) (freeOpenHomEquiv U A a) := by
  unfold freeOpenHomEquiv
  dsimp only [Equiv.trans_apply]
  rw [Adjunction.homEquiv_naturality_right]
  rfl

set_option backward.isDefEq.respectTransparency false in
private lemma locally_zero
    {T : TopCat.{u}}
    [HasExt.{u} (CategoryTheory.Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{u})]
    (F : CategoryTheory.Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{u})
    (q : ℕ) (hq : 0 < q) (U : Opens T)
    (x : Abelian.Ext (freeOpen U) F q) (t : T) (ht : t ∈ U) :
    ∃ (V : Opens T) (hVU : V ≤ U), t ∈ V ∧
      (Abelian.Ext.mk₀ (freeOpenMap (homOfLE hVU))).comp x (Nat.zero_add q) = 0 := by
  obtain ⟨G, g, hg, hx⟩ :=
    Abelian.Ext.exists_epi_comp_eq_zero (X := freeOpen U) (Y := F) q hq x
  have : Epi g := hg
  let s := freeOpenHomEquiv U (freeOpen U) (𝟙 _)
  have hlocal := (TopCat.Presheaf.isLocallySurjective_iff g.hom).mp
    ((TopCat.Sheaf.isLocallySurjective_iff_epi g).mpr inferInstance)
  obtain ⟨V, hVU, ⟨a, ha⟩, htV⟩ := hlocal U s t ht
  let i : V ⟶ U := homOfLE hVU
  let b := (freeOpenHomEquiv V G).symm a
  have hb : b ≫ g = freeOpenMap i := by
    apply (freeOpenHomEquiv V (freeOpen U)).injective
    rw [freeOpenHomEquiv_postcomp, Equiv.apply_symm_apply]
    apply ha.trans
    simpa [s, Presheaf.restrictOpen, Presheaf.restrict, i] using
      (freeOpenHomEquiv_comp i (𝟙 (freeOpen U))).symm
  refine ⟨V, leOfHom i, htV, ?_⟩
  rw [← hb, ← Abelian.Ext.mk₀_comp_mk₀_assoc, hx, Abelian.Ext.comp_zero]

attribute [local irreducible] CategoryTheory.Sheaf.cohomologyPresheafFunctor

private lemma t1_of_dimension_zero
    (T : Type u) [TopologicalSpace T] [T0Space T]
    (hd : topologicalKrullDim T ≤ 0) : T1Space T := by
  constructor
  intro x
  apply closure_subset_iff_isClosed.mp
  intro y hy
  let A : IrreducibleCloseds T :=
    ⟨closure ({y} : Set T), isIrreducible_singleton.closure, isClosed_closure⟩
  let B : IrreducibleCloseds T :=
    ⟨closure ({x} : Set T), isIrreducible_singleton.closure, isClosed_closure⟩
  have hAB : A ≤ B := closure_minimal (Set.singleton_subset_iff.mpr hy) isClosed_closure
  have heq := IrreducibleCloseds.eq_of_le_of_topologicalKrullDim_le_zero hd hAB
  exact Set.mem_singleton_iff.mpr
    (inseparable_iff_closure_eq.mpr (congrArg (fun C : IrreducibleCloseds T ↦
      (C : Set T)) heq)).eq

private lemma zero_dimension_vanishing
    (T : Type u) [TopologicalSpace T]
    [SpectralSpace T]
    (hd : topologicalKrullDim T ≤ 0)
    (F : CategoryTheory.Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{u})
    (q : ℕ) (hq : 0 < q) : Subsingleton (F.H' q ⊤) := by
  have : T1Space T := t1_of_dimension_zero T hd
  have : TotallySeparatedSpace T := inferInstance
  have : T2Space T := inferInstance
  exact subsingleton_H'_top_of_profinite (TopCat.of T) F q hq

-- Record the square's objects and arrows directly. Reducing these projections must not
-- re-elaborate the general pullback constructor used by `Opens.mayerVietorisSquare`.
private noncomputable def openMayerVietorisSquare
    {T : Type u} [TopologicalSpace T] (U V : Opens T) :
    (Opens.grothendieckTopology T).MayerVietorisSquare where
  X₁ := U ⊓ V
  X₂ := U
  X₃ := V
  X₄ := U ⊔ V
  f₁₂ := homOfLE inf_le_left
  f₁₃ := homOfLE inf_le_right
  f₂₄ := homOfLE le_sup_left
  f₃₄ := homOfLE le_sup_right
  fac := Subsingleton.elim _ _
  isPushout := (Opens.mayerVietorisSquare U V).isPushout

private lemma mv_lift_general
    {T : Type u} [TopologicalSpace T]
    [HasExt.{u} (CategoryTheory.Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{u})]
    (S : (Opens.grothendieckTopology T).MayerVietorisSquare)
    (F : CategoryTheory.Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{u})
    (q : ℕ) (x : F.H' q S.X₂)
    (hx : (F.cohomologyPresheaf q).map S.f₁₂.op x = 0) :
    ∃ y : F.H' q S.X₄, (F.cohomologyPresheaf q).map S.f₂₄.op y = x := by
  let z := (AddCommGrpCat.biprodIsoProd (F.H' q S.X₂) (F.H' q S.X₃)).inv (x, 0)
  have hz : S.fromBiprod F q z = 0 := by
    dsimp only [z]
    rw [S.fromBiprod_biprodIsoProd_inv_apply]
    simp only [hx, map_zero, sub_zero]
  have he := (S.sequence_exact F q (q + 1) rfl).exact 0
  rw [ShortComplex.ab_exact_iff] at he
  change ∀ z, S.fromBiprod F q z = 0 → ∃ y, S.toBiprod F q y = z at he
  obtain ⟨y, hy⟩ := he z hz
  refine ⟨y, ?_⟩
  have hy' := congrArg (fun a ↦
    ((AddCommGrpCat.biprodIsoProd (F.H' q S.X₂) (F.H' q S.X₃)).hom a).1) hy
  rw [S.toBiprod_apply] at hy'
  dsimp only [z] at hy'
  simpa only [Iso.inv_hom_id_apply] using hy'

private lemma mv_lift
    {T : Type u} [TopologicalSpace T]
    [HasExt.{u} (CategoryTheory.Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{u})]
    (F : CategoryTheory.Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{u})
    (U V : Opens T) (q : ℕ) (x : F.H' q U)
    (hx : (F.cohomologyPresheaf q).map (homOfLE (inf_le_left : U ⊓ V ≤ U)).op x = 0) :
    ∃ y : F.H' q (U ⊔ V),
      (F.cohomologyPresheaf q).map (homOfLE (le_sup_left : U ≤ U ⊔ V)).op y = x :=
  mv_lift_general (openMayerVietorisSquare U V) F q x hx

private lemma map_transport_zero
    {T : Type u} [TopologicalSpace T]
    (P : (Opens T)ᵒᵖ ⥤ AddCommGrpCat.{u})
    {A B C D : Opens T} (hAB : A = B) (hCD : C = D)
    (f : C ⟶ A) (g : D ⟶ B) (x : P.obj (op B))
    (hx : P.map f.op (P.map (eqToHom (congrArg op hAB.symm)) x) = 0) :
    P.map g.op x = 0 := by
  subst B D
  have hfg : f = g := Subsingleton.elim _ _
  simp only [eqToHom_refl] at hx
  rw [P.map_id] at hx
  simpa only [hfg, ConcreteCategory.id_apply] using hx

private lemma neighborhood_zero
    {T : Type u} [TopologicalSpace T]
    [HasExt.{u} (CategoryTheory.Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{u})]
    [SpectralSpace T]
    (n : ℕ) (hd : topologicalKrullDim T ≤ ((n + 1 : ℕ) : WithBot ℕ∞))
    (ih : ∀ (Y : Type u) [TopologicalSpace Y] [SpectralSpace Y]
      [HasExt.{u} (CategoryTheory.Sheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u})],
      topologicalKrullDim Y ≤ (n : WithBot ℕ∞) →
      ∀ (G : CategoryTheory.Sheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u})
        (q : ℕ), n < q → Subsingleton (G.H' q ⊤))
    (F : CategoryTheory.Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{u})
    (U : Opens T) (hU : IsCompact (U : Set T)) (x : F.H' (n + 1) U) :
    ∃ V : Opens T, (U : Set T)ᶜ ⊆ V ∧
      (F.cohomologyPresheaf (n + 1)).map
        (homOfLE (inf_le_left : U ⊓ V ≤ U)).op x = 0 := by
  let Z : Set T := (U : Set T)ᶜ
  have hZ : IsClosed Z := U.isOpen.isClosed_compl
  have hUc : IsCompact Zᶜ := by simpa [Z] using hU
  obtain ⟨hs, hdim⟩ := Topology.spectralSpace_puncturedGeneralizations_and_dimension
    T (n + 1) (by omega) hd Z hZ hUc
  have : SpectralSpace (TopCat.puncturedGeneralizations Z) := hs
  let D := TopCat.puncturedNeighborhoodCohomologyDiagram Z hZ F (n + 1)
  let c := TopCat.puncturedNeighborhoodCohomologyCocone Z hZ F (n + 1)
  obtain ⟨hf, hi⟩ := TopCat.puncturedNeighborhoodCohomology_colimit Z hZ hUc F (n + 1)
  have : IsFiltered (TopCat.compactOpenNeighborhoods Z)ᵒᵖ := hf
  have : IsIso (colimit.desc D c) := hi
  have hc : IsColimit c := by
    have : IsIso ((colimit.isColimit D).desc c) := hi
    exact (colimit.isColimit D).ofPointIso
  have hzero : Subsingleton c.pt := ih (TopCat.puncturedGeneralizations Z)
    (by simpa using hdim) _ (n + 1) (by omega)
  let N : TopCat.compactOpenNeighborhoods Z := ⟨⊤, Set.subset_univ _, isCompact_univ⟩
  have hNU : TopCat.puncturedNeighborhoodOpen Z hZ N = U := by
    ext t
    simp [TopCat.puncturedNeighborhoodOpen, N, Z]
  let e := (F.cohomologyPresheaf (n + 1)).mapIso (eqToIso (congrArg op hNU.symm))
  let x' : D.obj (op N) := e.hom x
  obtain ⟨M, f, hm⟩ := hc.eq_iff' x' 0 |>.mp (show (c.ι.app (op N)) x' = (c.ι.app (op N)) 0 from
    hzero.elim _ _)
  let V := M.unop.val
  refine ⟨V, M.unop.property.1, ?_⟩
  have hMV : TopCat.puncturedNeighborhoodOpen Z hZ M.unop = U ⊓ V := by
    ext t
    simp [TopCat.puncturedNeighborhoodOpen, Z, V, and_comm]
  have hm' : (F.cohomologyPresheaf (n + 1)).map
      (homOfLE ((TopCat.puncturedNeighborhoodOpen Z hZ).monotone (leOfHom f.unop))).op
      ((F.cohomologyPresheaf (n + 1)).map
        (eqToHom (congrArg op hNU.symm)) x) = 0 := by
    exact (hm.trans (map_zero _))
  exact map_transport_zero (F.cohomologyPresheaf (n + 1)) hNU hMV _ _ x hm'


private lemma mv_zero_general
    {T : Type u} [TopologicalSpace T]
    [HasExt.{u} (CategoryTheory.Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{u})]
    (S : (Opens.grothendieckTopology T).MayerVietorisSquare)
    (F : CategoryTheory.Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{u})
    (n : ℕ)
    (hs : Function.Surjective ((F.cohomologyPresheaf n).map S.f₁₂.op))
    (x : F.H' (n + 1) S.X₄)
    (hU : (F.cohomologyPresheaf (n + 1)).map S.f₂₄.op x = 0)
    (hV : (F.cohomologyPresheaf (n + 1)).map S.f₃₄.op x = 0) : x = 0 := by
  have hx : S.toBiprod F (n + 1) x = 0 := by
    rw [S.toBiprod_apply, hU, hV]
    exact map_zero _
  have he := (S.sequence_exact F n (n + 1) rfl).exact 2
  rw [ShortComplex.ab_exact_iff] at he
  change ∀ x, S.toBiprod F (n + 1) x = 0 → ∃ z, S.δ F n (n + 1) rfl z = x at he
  obtain ⟨z, hz⟩ := he x hx
  obtain ⟨w, hw⟩ := hs z
  let b := (AddCommGrpCat.biprodIsoProd (F.H' n S.X₂) (F.H' n S.X₃)).inv (w, 0)
  have hb : S.fromBiprod F n b = z := by
    dsimp only [b]
    rw [S.fromBiprod_biprodIsoProd_inv_apply, map_zero, sub_zero, hw]
  rw [← hz, ← hb, ← ConcreteCategory.comp_apply, S.fromBiprod_δ]
  rfl

private lemma mv_zero
    {T : Type u} [TopologicalSpace T]
    [HasExt.{u} (CategoryTheory.Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{u})]
    (F : CategoryTheory.Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{u})
    (U V : Opens T) (n : ℕ)
    (hs : Function.Surjective
      ((F.cohomologyPresheaf n).map (homOfLE (inf_le_left : U ⊓ V ≤ U)).op))
    (x : F.H' (n + 1) (U ⊔ V))
    (hU : (F.cohomologyPresheaf (n + 1)).map
      (homOfLE (le_sup_left : U ≤ U ⊔ V)).op x = 0)
    (hV : (F.cohomologyPresheaf (n + 1)).map
      (homOfLE (le_sup_right : V ≤ U ⊔ V)).op x = 0) : x = 0 :=
  mv_zero_general (openMayerVietorisSquare U V) F n hs x hU hV

attribute [local semireducible] CategoryTheory.Sheaf.cohomologyPresheafFunctor

private lemma bottom_vanishing
    {T : TopCat.{u}}
    [HasExt.{u} (CategoryTheory.Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{u})]
    (F : CategoryTheory.Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{u})
    (q : ℕ) (hq : 0 < q) : Subsingleton (F.H' q ⊥) := by
  have (G : CategoryTheory.Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{u}) :
      Subsingleton (G.obj.obj (op ⊥)) :=
    AddCommGrpCat.subsingleton_of_isZero (TopCat.Sheaf.isTerminalOfEqEmpty G rfl).isZero
  have : Projective (freeOpen (X := T) (⊥ : Opens T)) := by
    constructor
    intro A B f g _
    refine ⟨0, ?_⟩
    apply (freeOpenHomEquiv ⊥ B).injective
    exact Subsingleton.elim _ _
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hq)
  unfold CategoryTheory.Sheaf.H' CategoryTheory.Sheaf.cohomologyPresheaf
    CategoryTheory.Sheaf.cohomologyPresheafFunctor
  exact Abelian.Ext.subsingleton_of_projective (freeOpen (X := T) (⊥ : Opens T)) F k

attribute [local irreducible] CategoryTheory.Sheaf.cohomologyPresheafFunctor

private lemma finite_cover_vanishing
    {T : TopCat.{u}} [SpectralSpace T]
    (P Q : (Opens T)ᵒᵖ ⥤ AddCommGrpCat.{u})
    (hs : ∀ (U : Opens T), IsCompact (U : Set T) → Function.Surjective
      (P.map (homOfLE (le_top : U ≤ ⊤)).op))
    (hlocal : ∀ (x : Q.obj (op ⊤)) (t : T), ∃ (V : Opens T),
      t ∈ V ∧ IsCompact (V : Set T) ∧ Q.map (homOfLE (le_top : V ≤ ⊤)).op x = 0)
    (hzero : Subsingleton (Q.obj (op ⊥)))
    (hmv : ∀ (U V : Opens T),
      Function.Surjective (P.map (homOfLE (inf_le_left : U ⊓ V ≤ U)).op) →
      ∀ (x : Q.obj (op (U ⊔ V))),
      Q.map (homOfLE (le_sup_left : U ≤ U ⊔ V)).op x = 0 →
      Q.map (homOfLE (le_sup_right : V ≤ U ⊔ V)).op x = 0 → x = 0) :
    Subsingleton (Q.obj (op ⊤)) := by
  classical
  apply subsingleton_of_forall_eq 0
  intro x
  obtain ⟨V, hV⟩ := Classical.axiomOfChoice (hlocal x)
  obtain ⟨s, hscover⟩ := isCompact_univ.elim_finite_subcover
    (fun t ↦ (V t : Set T)) (fun t ↦ (V t).isOpen)
    (fun t _ ↦ Set.mem_iUnion.mpr ⟨t, (hV t).1⟩)
  have hfinite (s : Finset T) :
      IsCompact ((s.sup V : Opens T) : Set T) ∧
        Q.map
          (homOfLE (le_top : s.sup V ≤ ⊤)).op x = 0 := by
    induction s using Finset.induction_on with
    | empty =>
      simp only [Finset.sup_empty]
      refine ⟨isCompact_empty, ?_⟩
      change Q.map
        (homOfLE (bot_le : (⊥ : Opens T) ≤ ⊤)).op x = 0
      exact hzero.elim _ _
    | @insert t s hts ih =>
      rw [Finset.sup_insert]
      refine ⟨((hV t).2.1).union ih.1, ?_⟩
      let y := Q.map
        (homOfLE (le_top : V t ⊔ s.sup V ≤ ⊤)).op x
      have hI : IsCompact ((V t ⊓ s.sup V : Opens T) : Set T) :=
        ((hV t).2.1).inter_of_isOpen ih.1 (V t).isOpen (s.sup V).isOpen
      have hr : Function.Surjective (P.map
          (homOfLE (inf_le_left : V t ⊓ s.sup V ≤ V t)).op) := by
        intro z
        obtain ⟨w, hw⟩ := hs (V t ⊓ s.sup V) hI z
        refine ⟨P.map
          (homOfLE (le_top : V t ≤ ⊤)).op w, ?_⟩
        rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
        exact hw
      apply hmv (V t) (s.sup V) hr y
      · dsimp only [y]
        rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
        exact (hV t).2.2
      · dsimp only [y]
        rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
        exact ih.2
  have htop : s.sup V = ⊤ := by
    apply top_unique
    intro t _
    obtain ⟨i, hi, hti⟩ := Set.mem_iUnion₂.mp (hscover (Set.mem_univ t))
    exact (Finset.le_sup hi : V i ≤ s.sup V) hti
  have hh := (hfinite s).2
  have hmono : Mono (Q.map
      (homOfLE (le_top : s.sup V ≤ ⊤)).op) := by
    have hmap : (homOfLE (le_top : s.sup V ≤ ⊤)).op =
        eqToHom (congrArg op htop.symm) := Subsingleton.elim _ _
    rw [hmap]
    infer_instance
  exact (AddCommGrpCat.mono_iff_injective _).mp hmono
    (hh.trans (map_zero _).symm)

private lemma vanishing_of_top_restriction_surjective
    {T : TopCat.{u}}
    [HasExt.{u} (CategoryTheory.Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{u})]
    [SpectralSpace T]
    (F : CategoryTheory.Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{u})
    (n : ℕ)
    (hs : ∀ (U : Opens T), IsCompact (U : Set T) → Function.Surjective
      ((F.cohomologyPresheaf n).map (homOfLE (le_top : U ≤ ⊤)).op)) :
    Subsingleton (F.H' (n + 1) ⊤) := by
  classical
  have hlocal (x : (F.cohomologyPresheaf (n + 1)).obj (op ⊤)) (t : T) :
      ∃ (V : Opens T), t ∈ V ∧ IsCompact (V : Set T) ∧
      (F.cohomologyPresheaf (n + 1)).map (homOfLE (le_top : V ≤ ⊤)).op x = 0 := by
    with_unfolding_all
      obtain ⟨W, hW, ht, hx⟩ :=
        locally_zero (T := T) F (n + 1) (by omega) ⊤ x t (by trivial)
    with_unfolding_all
      change (F.cohomologyPresheaf (n + 1)).map (homOfLE hW).op x = 0 at hx
    obtain ⟨V, ⟨hVo, hVc⟩, htV, hVW⟩ :=
      PrespectralSpace.isTopologicalBasis.exists_subset_of_mem_open ht W.isOpen
    refine ⟨⟨V, hVo⟩, htV, hVc, ?_⟩
    have hh := congrArg (fun a ↦ (F.cohomologyPresheaf (n + 1)).map
      (homOfLE (show (⟨V, hVo⟩ : Opens T) ≤ W from hVW)).op a) hx
    rw [map_zero, ← ConcreteCategory.comp_apply, ← Functor.map_comp] at hh
    exact hh
  have hzero : Subsingleton ((F.cohomologyPresheaf (n + 1)).obj (op ⊥)) :=
    bottom_vanishing F (n + 1) (by omega)
  have hmv (U V : Opens T)
      (hs : Function.Surjective ((F.cohomologyPresheaf n).map
        (homOfLE (inf_le_left : U ⊓ V ≤ U)).op))
      (x : (F.cohomologyPresheaf (n + 1)).obj (op (U ⊔ V)))
      (hxU : (F.cohomologyPresheaf (n + 1)).map
        (homOfLE (le_sup_left : U ≤ U ⊔ V)).op x = 0)
      (hxV : (F.cohomologyPresheaf (n + 1)).map
        (homOfLE (le_sup_right : V ≤ U ⊔ V)).op x = 0) : x = 0 :=
    mv_zero F U V n hs x hxU hxV
  exact finite_cover_vanishing (F.cohomologyPresheaf n)
    (F.cohomologyPresheaf (n + 1)) hs hlocal hzero hmv

attribute [local semireducible] CategoryTheory.Sheaf.cohomologyPresheafFunctor

private lemma higher_vanishing
    {C : Type v} [Category.{u} C] [Abelian C] [HasExt.{u} C] [EnoughInjectives C]
    (X : C) (n : ℕ) (h : ∀ F : C, Subsingleton (Abelian.Ext X F (n + 1))) :
    ∀ (q : ℕ), n < q → ∀ F : C, Subsingleton (Abelian.Ext X F q) := by
  intro q
  induction q using Nat.strong_induction_on with
  | h q ih =>
    intro hq F
    by_cases heq : q = n + 1
    · subst q
      exact h F
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt (show 0 < q by omega))
    let S := ShortComplex.mk (Injective.ι F) (cokernel.π (Injective.ι F))
      (cokernel.condition _)
    have hS : S.ShortExact :=
      ShortComplex.ShortExact.mk' (ShortComplex.exact_cokernel _) inferInstance inferInstance
    have : Subsingleton (Abelian.Ext X S.X₃ k) := ih k (by omega) (by omega) S.X₃
    apply subsingleton_of_forall_eq 0
    intro x
    obtain ⟨y, hy⟩ := Abelian.Ext.covariant_sequence_exact₁ X hS x
      (Abelian.Ext.eq_zero_of_injective _) (n₀ := k) rfl
    rw [← hy, Subsingleton.elim y 0, Abelian.Ext.zero_comp]


/-- Abelian sheaf cohomology on a spectral space vanishes above any finite upper
bound on its topological Krull dimension, including for the empty space.

Source: Stacks Project, Cohomology of Sheaves, Tag 0A3G, part (1),
`proposition-cohomological-dimension-spectral`.
(blueprint: lem-sfb-spectral-space-cohomology-dimension)

Proof: Induct on the finite dimension bound, retaining vanishing for all larger degrees.
At dimension zero, distinct comparable point closures would give a chain of length one.
Thus singletons are closed. A spectral T1 space is profinite, so positive cohomology
vanishes by Tag 0A3F; this includes the empty space.

At bound n+1, let U be compact open and put Z = X \ U. The punctured generalization
subspace S is spectral of dimension at most n. Induction kills its degree-(n+1)
cohomology. The punctured-neighborhood comparison of Tag 0A3D and the filtered-colimit
zero criterion therefore kill a given class on U intersected with some neighborhood V
of Z. Abelian-sheaf Mayer--Vietoris lifts the pair consisting of that class and zero
on V. Thus degree-(n+1) restriction from X to every compact open is surjective.

To deduce vanishing in the next degree, first note that every positive cohomology
class vanishes locally: efface its Ext representative by an epimorphism and lift the
universal section locally. Refine by compact basis opens and take a finite subcover.
Induct on finite unions of these opens. Mayer--Vietoris shows that a class zero on
each of two opens is zero on their union whenever the preceding-degree restriction
to their intersection is surjective. The intersection is compact open, and the
surjectivity just proved from X factors through either member of the pair. The
empty union is handled by projectivity of the free sheaf of the empty open.
Finally embed an arbitrary sheaf into an injective and use its cokernel and the Ext
long exact sequence to obtain vanishing in every larger degree. This is the
finite-cover version of the acyclicity argument in Tag 0A3G, and uses no
Noetherian hypothesis or choice of integer-module structure.
-/
theorem subsingleton_H'_top_of_spectralSpace_of_dimension_le
    (T : Type u) [TopologicalSpace T]
    [SpectralSpace T]
    (d : ℕ) (hd : topologicalKrullDim T ≤ (d : WithBot ℕ∞))
    (F : CategoryTheory.Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{u})
    (q : ℕ) (hq : d < q) :
    Subsingleton
      (@CategoryTheory.Sheaf.H'.{u, u, u}
        (Opens T) inferInstance (Opens.grothendieckTopology T) inferInstance
        (@hasExt_of_enoughInjectives _ _ _ inferInstance
          (@IsGrothendieckAbelian.enoughInjectives _ _ _
            (CategoryTheory.Sheaf.isGrothendieckAbelian_of_essentiallySmall'.{u}
              (Opens.grothendieckTopology T) AddCommGrpCat.{u}))) F q ⊤) := by
  have hvan : ∀ (d : ℕ) (T : Type u) [TopologicalSpace T] [SpectralSpace T]
      [HasExt.{u} (CategoryTheory.Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{u})],
      topologicalKrullDim T ≤ (d : WithBot ℕ∞) →
      ∀ (F : CategoryTheory.Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{u})
        (q : ℕ), d < q → Subsingleton (F.H' q ⊤) := by
    intro d
    induction d with
    | zero =>
      intro T _ _ _ hd F q hq
      exact zero_dimension_vanishing T (by simpa using hd) F q hq
    | succ n ih =>
      intro T _ _ _ hd F q hq
      have hres (G : CategoryTheory.Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{u})
          (U : Opens T) (hU : IsCompact (U : Set T)) :
          Function.Surjective ((G.cohomologyPresheaf (n + 1)).map
            (homOfLE (le_top : U ≤ ⊤)).op) := by
        intro x
        obtain ⟨V, hV, hx⟩ := neighborhood_zero n hd ih G U hU x
        obtain ⟨y, hy⟩ := mv_lift G U V (n + 1) x hx
        have htop : U ⊔ V = ⊤ := by
          apply top_unique
          intro t _
          by_cases ht : t ∈ U
          · exact Or.inl ht
          · exact Or.inr (hV ht)
        let e := (G.cohomologyPresheaf (n + 1)).mapIso (eqToIso (congrArg op htop))
        refine ⟨e.hom y, ?_⟩
        dsimp only [e, Functor.mapIso_hom]
        rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
        exact hy
      have hnext (G : CategoryTheory.Sheaf
          (Opens.grothendieckTopology T) AddCommGrpCat.{u}) :
          Subsingleton (Abelian.Ext (freeOpen (X := TopCat.of T) ⊤) G (n + 1 + 1)) :=
        vanishing_of_top_restriction_surjective (T := TopCat.of T) G (n + 1) (hres G)
      exact higher_vanishing (freeOpen (X := TopCat.of T) ⊤) (n + 1) hnext q hq F
  exact hvan d T hd F q hq

end TopCat.Sheaf
