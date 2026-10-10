/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Data.Fintype.Lattice
public import Mathlib.Topology.NoetherianSpace
public import WeilConjectures.Mathlib.Topology.Sheaves.Flasque
public import WeilConjectures.Topology.Sheaves.CechCriterion
public import WeilConjectures.Topology.Sheaves.FilteredColimit
public import WeilConjectures.Topology.Sheaves.Godement

/-!
# Cohomology of filtered colimits of abelian sheaves

Let `X` be a quasi-compact topological space whose quasi-compact opens form a basis and are stable
under finite intersections (`PrespectralSpace X` and `QuasiSeparatedSpace X`), for instance a
noetherian space or the underlying space of a quasi-compact quasi-separated scheme. Let
`D : J ⥤ Sh(X)` be a filtered diagram of abelian sheaves on `X`. Then every cohomology class of
the colimit of `D` comes from a cohomology class of some `D j`.

The sections of the colimit over quasi-compact opens are the filtered colimits of the sections of
the `D j` (`TopCat.Sheaf.exists_app_eq_of_isColimit`). Hence the Čech complexes of the colimit of
the Godement sheaves of the `D j` on finite families of quasi-compact opens are exact in positive
degrees, and by the Čech criterion this colimit has vanishing higher cohomology. Embedding `D`
into the diagram of its Godement sheaves, the statement follows by induction on the degree.

This is the surjectivity half of [Stacks, Cohomology, Lemma 20.19.1][stacks-project] (tag `01FF`),
which is all that is needed for vanishing theorems and for cohomology of direct sums.

## Main statements

- `TopCat.Sheaf.exactAt_cechComplex_colimit`: Čech exactness on finite families of quasi-compact
  opens passes to filtered colimits.
- `TopCat.Sheaf.exists_H_map_colimit_ι_eq`: every class in `H^q(X, colim D)` comes from
  `H^q(X, D j)` for some `j`.
-/

@[expose] public section

universe u

open CategoryTheory Limits TopologicalSpace Opposite TopCat.Presheaf

namespace TopCat.Sheaf

variable {X : TopCat.{u}}

instance (priority := low) [NoetherianSpace X] : QuasiSeparatedSpace X where
  inter_isCompact _ _ _ _ _ _ := NoetherianSpace.isCompact _

/-- A finite intersection of quasi-compact opens of a quasi-separated space is quasi-compact. -/
lemma isCompact_iInf [QuasiSeparatedSpace X] {ι : Type*} [Finite ι] [Nonempty ι]
    (U : ι → Opens X) (hU : ∀ i, IsCompact (U i : Set X)) :
    IsCompact ((⨅ i, U i : Opens X) : Set X) := by
  classical
  have := Fintype.ofFinite ι
  have key (s : Finset ι) (hs : s.Nonempty) : IsCompact ((s.inf U : Opens X) : Set X) := by
    induction hs using Finset.Nonempty.cons_induction with
    | singleton a => simpa using hU a
    | cons a s ha _ ih =>
      rw [Finset.inf_cons, Opens.coe_inf]
      exact QuasiSeparatedSpace.inter_isCompact _ _ (U a).isOpen (hU a) (s.inf U).isOpen ih
  rw [← Finset.inf_univ_eq_iInf]
  exact key _ Finset.univ_nonempty

variable [PrespectralSpace X] [QuasiSeparatedSpace X] {J : Type u} [SmallCategory J]
  [IsFiltered J]

/-- **Čech exactness passes to filtered colimits.** If the Čech complexes of all members of a
filtered diagram of abelian sheaves on finite families of quasi-compact opens are exact in
positive degrees, then so are the Čech complexes of the colimit. -/
theorem exactAt_cechComplex_colimit
    (E : J ⥤ CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
    {n : ℕ} (U : Fin n → Opens X) (hU : ∀ i, IsCompact (U i : Set X))
    (hE : ∀ j q, ((cechComplex U).obj (E.obj j).obj).ExactAt (q + 1)) (q : ℕ) :
    ((cechComplex U).obj (colimit E).obj).ExactAt (q + 1) := by
  classical
  have hcpt {k : ℕ} (y : Fin (k + 1) → Fin n) : IsCompact ((⨅ l, U (y l) : Opens X) : Set X) :=
    isCompact_iInf _ fun l ↦ hU (y l)
  have hsurj {V : Opens X} (hV : IsCompact (V : Set X)) (s : (colimit E).obj.obj (op V)) :
      ∃ (j : J) (t : (E.obj j).obj.obj (op V)), (colimit.ι E j).hom.app (op V) t = s := by
    obtain ⟨j, t, h⟩ := exists_app_eq_of_isColimit (colimit.isColimit E) hV s
    rw [colimit.cocone_ι] at h
    exact ⟨j, t, h⟩
  have hinj {V : Opens X} (hV : IsCompact (V : Set X)) {j : J} (t : (E.obj j).obj.obj (op V))
      (ht : (colimit.ι E j).hom.app (op V) t = 0) :
      ∃ (k : J) (f : j ⟶ k), (E.map f).hom.app (op V) t = 0 :=
    exists_map_app_eq_zero_of_isColimit (colimit.isColimit E) hV t
      (by rw [colimit.cocone_ι]; exact ht)
  have hw {j j' : J} (f : j ⟶ j') (V : (Opens X)ᵒᵖ) (t : (E.obj j).obj.obj V) :
      (colimit.ι E j').hom.app V ((E.map f).hom.app V t) = (colimit.ι E j).hom.app V t := by
    rw [← colimit.w E f]
    rfl
  rw [exactAt_cechComplex_iff]
  intro c hc
  -- lift the cocycle to a common stage `m`
  choose j t ht using fun y : Fin (q + 2) → Fin n ↦ hsurj (hcpt y) (c y)
  let O : Finset J := Finset.univ.image j
  let m := IsFiltered.sup O ∅
  have hj (y : Fin (q + 2) → Fin n) : j y ∈ O := Finset.mem_image_of_mem _ (Finset.mem_univ _)
  let t' : ((cechComplex U).obj (E.obj m).obj).X (q + 1) := fun y ↦
    (E.map (IsFiltered.toSup O ∅ (hj y))).hom.app _ (t y)
  have ht' : ((cechComplex U).map (colimit.ι E m).hom).f (q + 1) t' = c := by
    funext y
    rw [cechComplex_map_f_apply]
    exact (hw _ _ _).trans (ht y)
  -- its coboundary dies at a later stage `m'`
  have hdt' : ((cechComplex U).map (colimit.ι E m).hom).f (q + 2)
      (((cechComplex U).obj (E.obj m).obj).d (q + 1) (q + 2) t') = 0 := by
    have h := cechComplex_map_f_d_apply U (colimit.ι E m).hom (q + 1) t'
    rw [ht'] at h
    exact h.trans hc
  choose j' f hf using fun z : Fin (q + 3) → Fin n ↦
    hinj (hcpt z) (((cechComplex U).obj (E.obj m).obj).d (q + 1) (q + 2) t' z)
      (congrFun hdt' z)
  let O' : Finset J := insert m (Finset.univ.image j')
  have hm : m ∈ O' := Finset.mem_insert_self _ _
  have hj' (z : Fin (q + 3) → Fin n) : j' z ∈ O' :=
    Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ (Finset.mem_univ _))
  let H' : Finset (Σ' (Y Z : J) (_ : Y ∈ O') (_ : Z ∈ O'), Y ⟶ Z) :=
    Finset.univ.image fun z ↦ ⟨m, j' z, hm, hj' z, f z⟩
  let m' := IsFiltered.sup O' H'
  let g : m ⟶ m' := IsFiltered.toSup O' H' hm
  have hg (z : Fin (q + 3) → Fin n) : f z ≫ IsFiltered.toSup O' H' (hj' z) = g :=
    IsFiltered.toSup_commutes O' H' hm (hj' z) (Finset.mem_image_of_mem _ (Finset.mem_univ _))
  let t'' := ((cechComplex U).map (E.map g).hom).f (q + 1) t'
  have hdt'' : ((cechComplex U).obj (E.obj m').obj).d (q + 1) (q + 2) t'' = 0 := by
    refine (cechComplex_map_f_d_apply U (E.map g).hom (q + 1) t').symm.trans ?_
    funext z
    change (E.map g).hom.app _ (((cechComplex U).obj (E.obj m).obj).d (q + 1) (q + 2) t' z) = 0
    rw [← hg z, map_comp_hom_app_apply, hf z, map_zero]
  obtain ⟨b, hb⟩ := (exactAt_cechComplex_iff U _ q).1 (hE m' q) t'' hdt''
  refine ⟨((cechComplex U).map (colimit.ι E m').hom).f q b, ?_⟩
  refine (cechComplex_map_f_d_apply U (colimit.ι E m').hom q b).symm.trans ?_
  rw [hb, ← ht']
  funext y
  exact hw g _ (t' y)

variable [CompactSpace X]

/-- The colimit of the Godement sheaves of a filtered diagram of abelian sheaves has vanishing
higher cohomology. -/
theorem subsingleton_H_colimit_godement
    (D : J ⥤ CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) (q : ℕ) :
    Subsingleton (Sheaf.H (colimit (D ⋙ godement)) (q + 1)) := by
  have hG {n : ℕ} (U : Fin n → Opens X) (j : J) (q : ℕ) :
      ((cechComplex U).obj ((D ⋙ godement).obj j).obj).ExactAt (q + 1) :=
    exactAt_cechComplex_godement U
      (fun x : X ↦ (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) (D.obj j).obj x : Type u)) q
  refine subsingleton_H_succ_of_exactAt_cechComplex _ (fun V ↦ IsCompact (V : Set X))
    (fun {n} U ↦ ∀ i, IsCompact (U i : Set X)) isCompact_univ
    (fun U hU k y ↦ isCompact_iInf _ fun l ↦ hU (y l)) (fun V hV W hW ↦ ?_)
    (fun U hU q ↦ exactAt_cechComplex_colimit _ U hU (hG U) q) q
  -- refine an open covering of a quasi-compact open by finitely many quasi-compact opens
  choose O hO hxO hOW using fun x : V ↦
    PrespectralSpace.isTopologicalBasis.exists_subset_of_mem_open
      (Opens.mem_inf.2 ⟨hW x, x.2⟩) (W x ⊓ V).isOpen
  obtain ⟨s, hs⟩ := hV.elim_finite_subcover (fun x : V ↦ O x) (fun x ↦ (hO x).1)
    fun x hx ↦ Set.mem_iUnion.2 ⟨⟨x, hx⟩, hxO _⟩
  let e := s.equivFin
  refine ⟨s.card, fun i ↦ ⟨O (e.symm i), (hO _).1⟩, fun i ↦ (hO _).2, le_antisymm
    (iSup_le fun i ↦ fun y hy ↦ ((hOW _ hy) : y ∈ (W _ ⊓ V : Opens X)).2) fun y hy ↦ ?_,
    fun i ↦ ⟨e.symm i, fun y hy ↦ ((hOW _ hy) : y ∈ (W _ ⊓ V : Opens X)).1⟩⟩
  obtain ⟨x, hx, hyx⟩ := Set.mem_iUnion₂.1 (hs hy)
  exact Opens.mem_iSup.2 ⟨e ⟨x, hx⟩, by simpa using hyx⟩

/-- The embedding of a diagram of abelian sheaves into the diagram of their Godement sheaves. -/
noncomputable def toGodementDiagram
    (D : J ⥤ CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) :
    D ⟶ D ⋙ godement where
  app j := toGodement.app (D.obj j)
  naturality _ _ f := toGodement.naturality (D.map f)

instance (D : J ⥤ CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) :
    Mono (toGodementDiagram D) :=
  have (j : J) : Mono ((toGodementDiagram D).app j) := mono_toGodement (D.obj j)
  NatTrans.mono_of_mono_app _

/-- **Cohomology of filtered colimits.** On a quasi-compact space whose quasi-compact opens form a
basis stable under finite intersections, every cohomology class of the colimit of a filtered
diagram `D` of abelian sheaves comes from a cohomology class of some `D j`. -/
theorem exists_H_map_colimit_ι_eq (q : ℕ) :
    ∀ (D : J ⥤ CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
      (ξ : Sheaf.H (colimit D) q), ∃ (j : J) (ξ' : Sheaf.H (D.obj j) q),
        Sheaf.H.map (colimit.ι D j) q ξ' = ξ := by
  induction q with
  | zero =>
    intro D ξ
    obtain ⟨j, t, ht⟩ := exists_app_eq_of_isColimit (colimit.isColimit D)
      isCompact_univ (Sheaf.H.equiv₀ _ isTerminalTop ξ)
    refine ⟨j, (Sheaf.H.equiv₀ _ isTerminalTop).symm t, ?_⟩
    rw [Sheaf.H.equiv₀_symm_naturality]
    rw [colimit.cocone_ι] at ht
    exact (Sheaf.H.equiv₀ _ isTerminalTop).symm_apply_eq.2 ht
  | succ q ih =>
    intro D ξ
    let η := toGodementDiagram D
    let S : ShortComplex
        (J ⥤ CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) :=
      ShortComplex.mk η (cokernel.π η) (cokernel.condition η)
    have hS : S.ShortExact :=
      ShortComplex.ShortExact.mk' (ShortComplex.exact_cokernel _) inferInstance inferInstance
    have hSc : (S.map colim).ShortExact := hS.map colim
    have : Subsingleton (Sheaf.H (S.map colim).X₂ (q + 1)) := subsingleton_H_colimit_godement D q
    obtain ⟨y, rfl⟩ := Sheaf.H.δSucc_surjective hSc q ξ
    obtain ⟨j, y', rfl⟩ := ih (cokernel η) y
    have hSj : (S.map ((evaluation J _).obj j)).ShortExact := hS.map _
    let φ : S.map ((evaluation J _).obj j) ⟶ S.map colim :=
      { τ₁ := colimit.ι D j
        τ₂ := colimit.ι (D ⋙ godement) j
        τ₃ := colimit.ι (cokernel η) j
        comm₁₂ := colimit.ι_map η j
        comm₂₃ := colimit.ι_map (cokernel.π η) j }
    exact ⟨j, Sheaf.H.δSucc hSj q y', Sheaf.H.map_δSucc hSj hSc φ q y'⟩

end TopCat.Sheaf
