module

public import Mathlib.CategoryTheory.Sites.Spaces
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Sheaf.CategoryTheory.SiteCechComplex
import Mathlib.CategoryTheory.Sites.Precoverage.Generates
import Sheaf.CategoryTheory.SiteCechVanishingCriterion
import Sheaf.CategoryTheory.SiteInjectiveCechAcyclic
import Sheaf.Topology.CompactCechCoproduct

@[expose] public section

universe u v w

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory.Sheaf

/-! # Filtered colimits of injectives are Čech-acyclic on a quasi-compact basis

Source: literature/stacks-project/cohomology.tex, Lemma 01FF proof and Lemma 01EW
(blueprint: lem-sc-topological-filtered-injective-cech-acyclic).
-/

private theorem compact_cech_intersections
    {X : Type u} [TopologicalSpace X]
    (hpairs : ∀ U V : TopologicalSpace.Opens X,
      IsCompact (U : Set X) → IsCompact (V : Set X) →
      IsCompact ((U ⊓ V : TopologicalSpace.Opens X) : Set X))
    {T : Type u} {U : TopologicalSpace.Opens X}
    {f : T → TopologicalSpace.Opens X} {hom : ∀ t, f t ⟶ U}
    (S : SiteCechComplex f hom)
    (hc : ∀ t, IsCompact ((f t : TopologicalSpace.Opens X) : Set X)) :
    ∀ (p : ℕ) (a : Fin (p + 1) → T),
      IsCompact ((S.W p a : TopologicalSpace.Opens X) : Set X) := by
  intro p
  induction p with
  | zero =>
      intro a
      rw [S.W_zero]
      exact hc _
  | succ p ih =>
      intro a
      have he : S.W (p + 1) a = f (a 0) ⊓ S.W p (a ∘ Fin.succ) := by
        apply le_antisymm
        · exact le_inf (S.pr (p + 1) a 0).le (S.indexMap a Fin.succ).le
        · let Z := f (a 0) ⊓ S.W p (a ∘ Fin.succ)
          let b : ∀ k : Fin (p + 1 + 1), Z ⟶ f (a k) :=
            Fin.cases (homOfLE inf_le_left)
              (fun k ↦ homOfLE inf_le_right ≫ S.pr p (a ∘ Fin.succ) k)
          obtain ⟨g, _, _⟩ := S.universal (p + 1) a Z b (fun _ ↦ Subsingleton.elim _ _)
          exact g.le
      rw [he]
      exact hpairs _ _ (hc _) (ih _)

private theorem compact_basis_cofinal
    {X : Type u} [TopologicalSpace X]
    (hbasis : TopologicalSpace.Opens.IsBasis
      {U : TopologicalSpace.Opens X | IsCompact (U : Set X)})
    (U : TopologicalSpace.Opens X) (hU : IsCompact (U : Set X))
    (T : Type u) (V : T → TopologicalSpace.Opens X) (f : ∀ t, V t ⟶ U)
    (hcover : Presieve.ofArrows V f ∈ (Opens.pretopology X).toPrecoverage U) :
    ∃ (K : Type u) (_ : Finite K) (W : K → TopologicalSpace.Opens X)
      (g : ∀ k, W k ⟶ U),
      (∀ k, IsCompact ((W k : TopologicalSpace.Opens X) : Set X)) ∧
      Presieve.ofArrows W g ∈ (Opens.pretopology X).toPrecoverage U ∧
      ∀ k, ∃ (t : T) (a : W k ⟶ V t), a ≫ f t = g k := by
  classical
  have hlocal : ∀ x : U, ∃ (t : T) (W : TopologicalSpace.Opens X),
      IsCompact (W : Set X) ∧ x.val ∈ W ∧ W ≤ V t := by
    intro x
    obtain ⟨Y, a, ha, hx⟩ := hcover x.val x.property
    cases ha with
    | mk t =>
        obtain ⟨W, hW, hxW, hWV⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp hbasis hx
        exact ⟨t, W, hW, hxW, hWV⟩
  choose t W hc hx hWV using hlocal
  obtain ⟨s, hs⟩ := hU.elim_finite_subcover (fun x : U ↦ (W x : Set X))
    (fun x ↦ (W x).isOpen) (by
      intro x hxU
      exact Set.mem_iUnion.mpr ⟨⟨x, hxU⟩, hx ⟨x, hxU⟩⟩)
  let g : ∀ k : s, W k.val ⟶ U :=
    fun k ↦ homOfLE ((hWV k.val).trans (f (t k.val)).le)
  refine ⟨s, inferInstance, (fun k ↦ W k.val), g, (fun k ↦ hc k.val), ?_, ?_⟩
  · intro x hxU
    obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.mp (hs hxU)
    exact ⟨W y, g ⟨y, hy⟩, Presieve.ofArrows.mk (f := g) ⟨y, hy⟩, hxy⟩
  · intro k
    exact ⟨t k.val, homOfLE (hWV k.val), Subsingleton.elim _ _⟩

set_option linter.unusedVariables false in
/-- A filtered colimit of injective abelian sheaves on a space with a quasi-compact
basis is Čech-acyclic on finite quasi-compact covers, and has no higher cohomology
on quasi-compact opens.
Source: literature/stacks-project/cohomology.tex, Lemma 01FF proof and Lemma 01EW
(blueprint: lem-sc-topological-filtered-injective-cech-acyclic).

Proof: identify sections of the colimit on every quasi-compact finite intersection
with the filtered colimit of the sections of the injectives; finite products commute
with filtered colimits, so the Čech complex is the filtered colimit of the complexes
for the injectives. Each latter complex is acyclic in positive degree by
`lem-weil-pbc-site-injective-cech-acyclic`, and exactness is preserved by filtered
colimits of abelian groups. The Čech vanishing criterion
`lem-weil-pbc-site-cech-vanishing-criterion` then gives vanishing of higher derived
cohomology on every quasi-compact open.
-/
theorem topological_filtered_injective_cech_acyclic
    {X : Type u} [TopologicalSpace X]
    [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
    [HasExt.{v} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})]
    (hbasis : TopologicalSpace.Opens.IsBasis
      {U : TopologicalSpace.Opens X | IsCompact (U : Set X)})
    (hpairs : ∀ U V : TopologicalSpace.Opens X,
      IsCompact (U : Set X) → IsCompact (V : Set X) →
      IsCompact ((U ⊓ V : TopologicalSpace.Opens X) : Set X))
    {I : Type w} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (F : Discrete I ⥤ Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
    [HasColimit F]
    (hI : ∀ i : I, Injective (F.obj (Discrete.mk i))) :
    (∀ (U : TopologicalSpace.Opens X), IsCompact (U : Set X) →
      ∀ (T : Type u) [Finite T] (f : T → TopologicalSpace.Opens X)
        (hom : ∀ t, f t ⟶ U)
        (hcompact : ∀ t, IsCompact ((f t : TopologicalSpace.Opens X) : Set X))
        (hcover : Presieve.ofArrows f hom ∈ (Opens.pretopology X).toPrecoverage U)
        (S : SiteCechComplex f hom),
        ∀ p : ℕ, 0 < p →
          IsZero ((S.cohomologyFunctor p).obj (colimit F).obj)) ∧
      (∀ (U : TopologicalSpace.Opens X), IsCompact (U : Set X) →
        ∀ q : ℕ, 0 < q → IsZero (H' (colimit F) q U)) := by
  classical
  have hJ : (Opens.grothendieckTopology X).toPrecoverage =
      (Opens.pretopology X).toPrecoverage := by
    rw [← Opens.toPretopology_grothendieckTopology]
    rfl
  have : (Opens.pretopology X).toPrecoverage.HasIsos := hJ ▸ inferInstance
  have : (Opens.pretopology X).toPrecoverage.IsStableUnderComposition := hJ ▸ inferInstance
  have : (Opens.pretopology X).toPrecoverage.IsStableUnderBaseChange := hJ ▸ inferInstance
  have htop : (Opens.pretopology X).toPrecoverage.toGrothendieck =
      Opens.grothendieckTopology X := by
    change (Opens.pretopology X).toCoverage.toPrecoverage.toGrothendieck = _
    rw [Coverage.toGrothendieck_toPrecoverage, Pretopology.toGrothendieck_toCoverage,
      Opens.pretopology_toGrothendieck]
  have hcech : ∀ (U : TopologicalSpace.Opens X), IsCompact (U : Set X) →
      ∀ (T : Type u) [Finite T] (f : T → TopologicalSpace.Opens X)
        (hom : ∀ t, f t ⟶ U)
        (hcompact : ∀ t, IsCompact ((f t : TopologicalSpace.Opens X) : Set X))
        (hcover : Presieve.ofArrows f hom ∈ (Opens.pretopology X).toPrecoverage U)
        (S : SiteCechComplex f hom),
        ∀ p : ℕ, 0 < p →
          IsZero ((S.cohomologyFunctor p).obj (colimit F).obj) := by
    intro U _ T _ f hom hcompact hcover S p hp
    let E := sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} ⋙
      S.cohomologyFunctor p
    have : PreservesColimit F E := compact_siteCech_cohomology_preserves_coproduct
      S (compact_cech_intersections hpairs S hcompact) F p
    apply (isColimitOfPreserves E (colimit.isColimit F)).isZero_pt
    apply Functor.isZero
    intro i
    have : Injective (F.obj i) := hI i.as
    have hinj := @site_injective_cech_acyclic
      (TopologicalSpace.Opens X) _ (Opens.pretopology X).toPrecoverage _ _ _ _
      T U f hom hcover S
    rw [htop] at hinj
    exact (hinj (F.obj i)).1 p hp
  refine ⟨hcech, ?_⟩
  let B : Set (TopologicalSpace.Opens X) := {U | IsCompact (U : Set X)}
  let Cov := fun (U : TopologicalSpace.Opens X) (T : Type u)
    (V : T → TopologicalSpace.Opens X) (f : ∀ t, V t ⟶ U) ↦
      Finite T ∧ IsCompact (U : Set X) ∧
      (∀ t, IsCompact ((V t : TopologicalSpace.Opens X) : Set X)) ∧
      Presieve.ofArrows V f ∈ (Opens.pretopology X).toPrecoverage U
  let S := fun U T V f (h : Cov U T V f) ↦
    (SiteCechComplex.exists_of_covering (Opens.pretopology X).toPrecoverage h.2.2.2).some
  have hc := @isZero_H'_of_siteCech_vanishing.{u, v}
    (TopologicalSpace.Opens X) _ (Opens.pretopology X).toPrecoverage _ _ _ _
  rw [htop] at hc
  apply hc B Cov S (colimit F)
  · intro U T V f h
    exact h.2.2.2
  · intro U T V f h
    exact ⟨h.2.1, h.2.2.1, compact_cech_intersections hpairs (S U T V f h) h.2.2.1⟩
  · intro U hU T V f h
    obtain ⟨K, hK, W, g, hW, hcov, href⟩ := compact_basis_cofinal hbasis U hU T V f h
    exact ⟨K, W, g, ⟨hK, hU, hW, hcov⟩, href⟩
  · intro U T V f h p hp
    have : Finite T := h.1
    exact hcech U h.2.1 T V f h.2.2.1 h.2.2.2 (S U T V f h) p hp

end CategoryTheory.Sheaf
