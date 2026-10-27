/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NP
-/
module

public import Sheaf.CategoryTheory.RingedSiteModules
public import WeilConjectures.AlgebraicGeometry.DerivedHomMayerVietoris
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.Topology.Compactness.Compact
import Sheaf.CategoryTheory.ModuleDirectedColimitUnderlyingSets
import Mathlib.Data.Finset.Order
import Mathlib.CategoryTheory.Limits.Constructions.Over.Products
import Mathlib.CategoryTheory.Sites.Limits
import Mathlib.CategoryTheory.Limits.Types.Filtered

/-!
# Eventual equality of maps from a finite-type module on a quasi-compact open

Source: Stacks Project, Sheaves Tag 009F (lemma-directed-colimits-sections), proof of (2),
and Modules Tag 01B5 (definition-finite-type)
(blueprint: lem-weil-pbc-finite-type-hom-colimit-qc-equality).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace AlgebraicGeometry

namespace SheafOfModules

private theorem section_eventual_equality
    {X : Type u} [TopologicalSpace X]
    (R : Sheaf (Opens.grothendieckTopology X) RingCat.{u})
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (F : I ⥤ ringedSiteModules.{u} R)
    (c : Cocone F) (hc : IsColimit c)
    (W : Opens X) (i j : I)
    (s : (F.obj i).val.obj (Opposite.op W))
    (t : (F.obj j).val.obj (Opposite.op W))
    (h : (c.ι.app i).val.app (Opposite.op W) s =
      (c.ι.app j).val.app (Opposite.op W) t)
    (x : X) (hx : x ∈ W) :
    ∃ (V : Opens X) (hVW : V ≤ W) (_hxV : x ∈ V)
      (k : I) (hik : i ≤ k) (hjk : j ≤ k),
      (F.map (homOfLE hik)).val.app (Opposite.op V)
          ((F.obj i).val.map (homOfLE hVW).op s) =
        (F.map (homOfLE hjk)).val.app (Opposite.op V)
          ((F.obj j).val.map (homOfLE hVW).op t) := by
  classical
  let J := Opens.grothendieckTopology X
  let T := toSheaf R ⋙ sheafCompose J (CategoryTheory.forget AddCommGrpCat.{u})
  let D := F ⋙ T
  let P := D ⋙ sheafToPresheaf J (Type u)
  let d := T.mapCocone c
  let hd := (underlying_directed_colimit_isColimit R F c hc).some
  let c' := Sheaf.sheafifyCocone (colimit.cocone P)
  have hc' : IsColimit c' := Sheaf.isColimitSheafifyCocone _ (colimit.isColimit P)
  let e := hc'.coconePointUniqueUpToIso hd
  let b : colimit P ⟶ d.pt.obj := toSheafify J (colimit P) ≫ e.hom.hom
  have hb (a : I) : colimit.ι P a ≫ b = (d.ι.app a).hom := by
    dsimp only [b]
    have hι : (c'.ι.app a).hom = colimit.ι P a ≫ toSheafify J (colimit P) := by
      simpa only [colimit.cocone_ι, colimit.cocone_x] using
        Sheaf.sheafifyCocone_ι_app_val (colimit.cocone P) a
    rw [← Category.assoc, ← hι]
    exact congrArg (fun f ↦ f.hom) (hc'.comp_coconePointUniqueUpToIso_hom hd a)
  let p := (colimit.ι P i).app (Opposite.op W) s
  let q := (colimit.ι P j).app (Opposite.op W) t
  have hpq : b.app (Opposite.op W) p = b.app (Opposite.op W) q := by
    have hi := congrArg (fun f ↦ f.app (Opposite.op W) s) (hb i)
    have hj := congrArg (fun f ↦ f.app (Opposite.op W) t) (hb j)
    exact hi.trans (h.trans hj.symm)
  have : Presheaf.IsLocallyInjective J b := by dsimp only [b]; infer_instance
  obtain ⟨V, f, hf, hxV⟩ :=
    Presheaf.equalizerSieve_mem J b p q hpq x hx
  have hp : (colimit.ι P i).app (Opposite.op V)
      ((F.obj i).val.map f.op s) = (colimit P).map f.op p :=
    CategoryTheory.congr_fun ((colimit.ι P i).naturality f.op) s
  have hq : (colimit.ι P j).app (Opposite.op V)
      ((F.obj j).val.map f.op t) = (colimit P).map f.op q :=
    CategoryTheory.congr_fun ((colimit.ι P j).naturality f.op) t
  let E := P ⋙ (CategoryTheory.evaluation _ (Type u)).obj (Opposite.op V)
  have he := isColimitOfPreserves ((CategoryTheory.evaluation _ (Type u)).obj (Opposite.op V))
    (colimit.isColimit P)
  have hv : (colimit.ι P i).app (Opposite.op V) ((F.obj i).val.map f.op s) =
      (colimit.ι P j).app (Opposite.op V) ((F.obj j).val.map f.op t) :=
    hp.trans (hf.trans hq.symm)
  obtain ⟨k, a, a', haa'⟩ := (Types.FilteredColimit.isColimit_eq_iff E he).mp hv
  exact ⟨V, leOfHom f, hxV, k, leOfHom a, leOfHom a', haa'⟩

private theorem generators_ext_on_object
    {C : Type u} [SmallCategory C] [HasPullbacks C]
    {J : GrothendieckTopology C} (R : Sheaf J RingCat.{u})
    {M N : ringedSiteModules.{u} R} {Q T : C} (q : T ⟶ Q)
    (σ : (M.over Q).GeneratingSections) (f g : M ⟶ N)
    (h : ∀ r : σ.I, f.val.app (Opposite.op T)
        ((σ.s r).val (Opposite.op (Over.mk q))) =
      g.val.app (Opposite.op T) ((σ.s r).val (Opposite.op (Over.mk q)))) :
    ∀ (W : C) (_w : W ⟶ T), f.val.app (Opposite.op W) = g.val.app (Opposite.op W) := by
  have : HasBinaryProducts (Over Q) := Over.ConstructProducts.over_binaryProduct_of_pullback
  let B : Over Q := Over.mk q
  let A := overFunctor (R.over Q) B
  have : A.IsLeftAdjoint := (overPushforwardOverAdj (R := R.over Q) B).isLeftAdjoint
  have he : A.map (f.over Q) = A.map (g.over Q) := by
    apply (cancel_epi (A.map σ.π)).mp
    apply (isColimitOfPreserves A (isColimitFreeCofan σ.I)).hom_ext
    intro r
    change A.map (ιFree r.as) ≫ A.map σ.π ≫ A.map (f.over Q) =
      A.map (ιFree r.as) ≫ A.map σ.π ≫ A.map (g.over Q)
    rw [← A.map_comp_assoc, ← A.map_comp_assoc]
    rw [← unitHomEquiv_symm_freeHomEquiv_apply,
      (M.over Q).freeHomEquiv.apply_symm_apply]
    apply (A.obj (N.over Q)).unitHomEquiv.injective
    apply PresheafOfModules.sections_ext
    intro Z
    let t : M.val.obj (Opposite.op T) := (σ.s r.as).val (Opposite.op B)
    let z : M.val.obj (Opposite.op Z.unop.left.left) :=
      (σ.s r.as).val (Opposite.op Z.unop.left)
    have hs : M.val.map Z.unop.hom.left.op t = z :=
      (σ.s r.as).property Z.unop.hom.op
    have h0 : f.val.app (Opposite.op T) t = g.val.app (Opposite.op T) t := h r.as
    have hn0 := congrArg (fun z ↦ N.val.map Z.unop.hom.left.op z) h0
    have hn : f.val.app (Opposite.op Z.unop.left.left) z =
        g.val.app (Opposite.op Z.unop.left.left) z := by
      rw [← hs]
      exact (PresheafOfModules.naturality_apply f.val Z.unop.hom.left.op t).trans
        (hn0.trans (PresheafOfModules.naturality_apply g.val Z.unop.hom.left.op t).symm)
    let e : R.obj.obj (Opposite.op Z.unop.left.left) := 1
    have hu : ((M.over Q).unitHomEquiv.symm (σ.s r.as)).val.app
        (Opposite.op Z.unop.left) e = z :=
      congrArg (fun s ↦ s.val (Opposite.op Z.unop.left))
        ((M.over Q).unitHomEquiv.apply_symm_apply (σ.s r.as))
    change f.val.app (Opposite.op Z.unop.left.left)
        (((M.over Q).unitHomEquiv.symm (σ.s r.as)).val.app
          (Opposite.op Z.unop.left) e) =
      g.val.app (Opposite.op Z.unop.left.left)
        (((M.over Q).unitHomEquiv.symm (σ.s r.as)).val.app
          (Opposite.op Z.unop.left) e)
    rw [hu]
    exact hn
  intro W w
  let W' : Over B := Over.mk (Over.homMk w : Over.mk (w ≫ q) ⟶ B)
  exact congrArg (fun z ↦ z.val.app (Opposite.op W')) he

/-- Maps from a finite-type module over a quasi-compact open that agree in a directed
colimit agree at some common stage.

Source: Stacks Project, Sheaves Tag 009F (lemma-directed-colimits-sections), proof of (2),
applied to finitely many local generators as in Modules Tag 01B5 (definition-finite-type)
(blueprint: lem-weil-pbc-finite-type-hom-colimit-qc-equality).

Proof:
1. By `lem-weil-pbc-module-directed-colimit-underlying-sets`, forgetting modules gives
   a colimit of sheaves of sets. By `lem-weil-pbc-sheaves-colimit-sheafification`, this
   is canonically the sheafification of the sectionwise presheaf colimit. The unique
   colimit isomorphism identifies its coprojections with the specified cocone legs
   (`def-weil-pbc-category-colimit`).
2. Two stage sections whose colimit images agree are locally equal in that presheaf
   by `lem-weil-pbc-site-sheafification-sections-local`. On each such neighbourhood,
   `lem-weil-pbc-filtered-colimit-sets-elementwise` gives equality at a common stage.
   These neighbourhoods need not be quasi-compact.
3. At each point of U, choose finitely many local generators of G using
   `def-weil-pbc-module-finite-type-presentation`. Apply step 2 to their images under
   the two maps, intersect the finitely many neighbourhoods and bound their stages.
   For zero generators use the original neighbourhood and an upper bound of i and j.
4. The maps agree on the whole restricted module on this neighbourhood:
   `lem-weil-pbc-ringed-space-module-exactness-local-lifting` makes the generating
   epimorphism locally surjective. Locally lift any section to the finite free module;
   linearity gives equality on the lift and sheaf uniqueness gives equality on the
   section. This includes the empty sum and does not require surjectivity on sections.
5. Quasi-compactness gives finitely many such neighbourhoods covering U. Bound their
   stages together with i and j, transport their equalities by the diagram identities,
   and use sheaf uniqueness on the resulting cover of every open contained in U.
   If U is empty, any upper bound of i and j works by uniqueness on the empty open.
   No quasi-compactness of overlaps or injectivity of transitions is used. -/
theorem finite_type_hom_colimit_qc_equality
    (X : RingedSpace.{u})
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (F : I ⥤ ringedSiteModules.{u} (moduleRings X))
    (c : Cocone F) (_hc : IsColimit c)
    (U : Opens X) (_hU : IsCompact (U : Set X))
    (G : ringedSiteModules.{u} ((moduleRings X).over U)) [G.IsFiniteType]
    (i j : I) (g : G ⟶ (F.obj i).over U) (g' : G ⟶ (F.obj j).over U)
    (_h : g ≫ (c.ι.app i).over U = g' ≫ (c.ι.app j).over U) :
    ∃ (k : I) (hik : i ≤ k) (hjk : j ≤ k),
      g ≫ (F.map (homOfLE hik)).over U = g' ≫ (F.map (homOfLE hjk)).over U := by
  classical
  generalize hR : moduleRings X = R at *
  have hlocal (x : U) :
      ∃ (V : Opens X) (_hx : x.val ∈ V) (_hVU : V ≤ U)
        (k : I) (hik : i ≤ k) (hjk : j ≤ k),
        ∀ (W : Over U), W.left ≤ V →
          (g ≫ (F.map (homOfLE hik)).over U).val.app (Opposite.op W) =
            (g' ≫ (F.map (homOfLE hjk)).over U).val.app (Opposite.op W) := by
    obtain ⟨p, hp⟩ := IsFiniteType.exists_localGeneratorsData G
    have hcover := ((Opens.grothendieckTopology X).mem_over_iff _).mp
      (p.coversTop (Over.mk (𝟙 U)))
    obtain ⟨B, b, hb, hxB⟩ := hcover x.val x.property
    rw [Sieve.overEquiv_iff] at hb
    obtain ⟨r, ⟨q⟩⟩ := hb
    let Q := p.X r
    have hxQ : x.val ∈ Q.left := (leOfHom q.left) hxB
    let σ := p.generators r
    have : σ.IsFiniteType := hp.isFiniteType r
    let _ := Fintype.ofFinite σ.I
    let s (a : σ.I) : G.val.obj (Opposite.op Q) :=
      (σ.s a).val (Opposite.op (Over.mk (𝟙 Q)))
    have hs (a : σ.I) :
        (c.ι.app i).val.app (Opposite.op Q.left) (g.val.app (Opposite.op Q) (s a)) =
          (c.ι.app j).val.app (Opposite.op Q.left) (g'.val.app (Opposite.op Q) (s a)) :=
      congrArg (fun f ↦ f.val.app (Opposite.op Q) (s a)) _h
    have H (a : σ.I) := section_eventual_equality R F c _hc Q.left i j
      (g.val.app (Opposite.op Q) (s a)) (g'.val.app (Opposite.op Q) (s a))
      (hs a) x.val hxQ
    choose V hVQ hxV k hik hjk hk using H
    let B := Q.left ⊓ ⨅ a, V a
    have hBQ : B ≤ Q.left := inf_le_left
    have hBV (a : σ.I) : B ≤ V a := le_trans inf_le_right (iInf_le _ a)
    have hxB : x.val ∈ B := ⟨hxQ, by
      rw [Opens.coe_iInf]
      exact Set.mem_iInter.mpr hxV⟩
    obtain ⟨l, hl⟩ := (insert i (insert j (Finset.univ.image k))).exists_le
    have hil : i ≤ l := hl i (Finset.mem_insert_self ..)
    have hjl : j ≤ l := hl j (Finset.mem_insert_of_mem (Finset.mem_insert_self ..))
    refine ⟨B, hxB, le_trans hBQ (leOfHom Q.hom), l, hil, hjl, ?_⟩
    let P : Over U := Over.mk (homOfLE (le_trans hBQ (leOfHom Q.hom)))
    let bQ : P ⟶ Q := Over.homMk (homOfLE hBQ)
    suffices hgen : ∀ a : σ.I,
        (g ≫ (F.map (homOfLE hil)).over U).val.app (Opposite.op P)
            ((σ.s a).val (Opposite.op (Over.mk bQ))) =
          (g' ≫ (F.map (homOfLE hjl)).over U).val.app (Opposite.op P)
            ((σ.s a).val (Opposite.op (Over.mk bQ))) by
      intro W hWB
      exact generators_ext_on_object (R.over U) bQ σ _ _ hgen W
        (Over.homMk (homOfLE hWB))
    intro a
    have hkl : k a ≤ l := hl _ (Finset.mem_insert_of_mem
      (Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨a, Finset.mem_univ _, rfl⟩)))
    have he := congrArg (fun z ↦ (F.map (homOfLE hkl)).val.app (Opposite.op B)
      ((F.obj (k a)).val.map (homOfLE (hBV a)).op z)) (hk a)
    rw [← PresheafOfModules.naturality_apply,
      ← PresheafOfModules.naturality_apply,
      ← PresheafOfModules.map_comp_apply, ← PresheafOfModules.map_comp_apply] at he
    have hres : (homOfLE (hVQ a)).op ≫ (homOfLE (hBV a)).op =
        (homOfLE hBQ).op := Subsingleton.elim _ _
    rw [hres] at he
    change ((F.map (homOfLE (hik a)) ≫ F.map (homOfLE hkl)).val.app (Opposite.op B))
        ((F.obj i).val.map (homOfLE hBQ).op (g.val.app (Opposite.op Q) (s a))) =
      ((F.map (homOfLE (hjk a)) ≫ F.map (homOfLE hkl)).val.app (Opposite.op B))
        ((F.obj j).val.map (homOfLE hBQ).op (g'.val.app (Opposite.op Q) (s a))) at he
    rw [← F.map_comp, ← F.map_comp] at he
    have hi : homOfLE (hik a) ≫ homOfLE hkl = homOfLE hil := Subsingleton.elim _ _
    have hj : homOfLE (hjk a) ≫ homOfLE hkl = homOfLE hjl := Subsingleton.elim _ _
    rw [hi, hj] at he
    have hsB : (σ.s a).val (Opposite.op (Over.mk bQ)) = G.val.map bQ.op (s a) :=
      ((σ.s a).property (Over.homMk bQ : Over.mk bQ ⟶ Over.mk (𝟙 Q)).op).symm
    change (F.map (homOfLE hil)).val.app (Opposite.op B)
        (g.val.app (Opposite.op P) ((σ.s a).val (Opposite.op (Over.mk bQ)))) =
      (F.map (homOfLE hjl)).val.app (Opposite.op B)
        (g'.val.app (Opposite.op P) ((σ.s a).val (Opposite.op (Over.mk bQ))))
    rw [hsB, PresheafOfModules.naturality_apply, PresheafOfModules.naturality_apply]
    exact he
  choose V hx hVU a hia hja ha using hlocal
  obtain ⟨t, ht⟩ := _hU.elim_finite_subcover (fun x : U ↦ (V x : Set X))
    (fun x ↦ (V x).isOpen) (fun x hxu ↦ Set.mem_iUnion.mpr ⟨⟨x, hxu⟩, hx ⟨x, hxu⟩⟩)
  obtain ⟨k, hk⟩ := (insert i (insert j (t.image a))).exists_le
  have hik : i ≤ k := hk i (Finset.mem_insert_self ..)
  have hjk : j ≤ k := hk j (Finset.mem_insert_of_mem (Finset.mem_insert_self ..))
  refine ⟨k, hik, hjk, ?_⟩
  let f := g ≫ (F.map (homOfLE hik)).over U
  let f' := g' ≫ (F.map (homOfLE hjk)).over U
  have heq (x : U) (hxt : x ∈ t) (W : Over U) (hW : W.left ≤ V x) :
      f.val.app (Opposite.op W) = f'.val.app (Opposite.op W) := by
    have hak : a x ≤ k := hk _ (Finset.mem_insert_of_mem
      (Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨x, hxt, rfl⟩)))
    have h := congrArg (fun q ↦ q ≫ ((F.map (homOfLE hak)).over U).val.app
      (Opposite.op W)) (ha x W hW)
    have hi : homOfLE (hia x) ≫ homOfLE hak = homOfLE hik := Subsingleton.elim _ _
    have hj : homOfLE (hja x) ≫ homOfLE hak = homOfLE hjk := Subsingleton.elim _ _
    simpa only [f, f', ← PresheafOfModules.comp_app, ← comp_val,
      Category.assoc, ← Functor.map_comp, hi, hj] using h
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro W
  ext s
  let S : Sieve W.unop.left :=
    { arrows := fun Q _ ↦ ∃ x ∈ t, Q ≤ V x
      downward_closed := by
        rintro Q Q' q ⟨x, hxt, hQ⟩ r
        exact ⟨x, hxt, le_trans (leOfHom r) hQ⟩ }
  have hS : S ∈ Opens.grothendieckTopology X W.unop.left := by
    intro y hy
    obtain ⟨x, hxt, hyV⟩ := Set.mem_iUnion₂.mp (ht (leOfHom W.unop.hom hy))
    exact ⟨W.unop.left ⊓ V x, homOfLE inf_le_left,
      ⟨x, hxt, inf_le_right⟩, ⟨hy, hyV⟩⟩
  apply ((F.obj k).over U).isSheaf.isSeparated _ _
    ((Opens.grothendieckTopology X).overEquiv_symm_mem_over W.unop S hS)
  intro Q q hq
  obtain ⟨x, hxt, hQ⟩ := hq
  have h := congrArg (fun z ↦ z ((G.val.map q.op) s)) (heq x hxt Q hQ)
  change ((F.obj k).over U).val.map q.op (f.val.app W s) =
    ((F.obj k).over U).val.map q.op (f'.val.app W s)
  rw [← PresheafOfModules.naturality_apply, ← PresheafOfModules.naturality_apply]
  exact h

end SheafOfModules
