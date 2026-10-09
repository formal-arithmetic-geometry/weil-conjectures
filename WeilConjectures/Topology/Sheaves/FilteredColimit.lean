/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic
public import Mathlib.CategoryTheory.Sites.Limits
public import Mathlib.CategoryTheory.Sites.LocallyInjective
public import Mathlib.CategoryTheory.Sites.LocallySurjective
public import Mathlib.Topology.QuasiSeparated
public import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing
public import Mathlib.Topology.Spectral.Prespectral

/-!
# Sections of filtered colimits of abelian sheaves over quasi-compact opens

Let `X` be a topological space whose quasi-compact opens form a basis and are stable under finite
intersections (`PrespectralSpace X` and `QuasiSeparatedSpace X`), for instance a noetherian
space or the underlying space of a quasi-separated scheme. Let `D : J ⥤ Sh(X)` be a filtered
diagram of abelian sheaves with colimit `c`. For every quasi-compact open `U`, the sections
`c.pt(U)` are the filtered colimit of the sections `D_j(U)`: every section of `c.pt` over `U`
comes from some `D_j(U)`, and a section of `D_j(U)` which dies in `c.pt(U)` already dies in some
`D_k(U)`.

The colimit of sheaves is the sheafification of the colimit of the underlying presheaves; the
comparison map from the presheaf colimit is locally injective and locally surjective, and
quasi-compactness reduces the local statements to finitely many opens, over which the filtered
category provides a common bound.

This is [Stacks, Sheaves, Lemma 6.29.1][stacks-project] (tag `009F`).

## Main statements

- `TopCat.Sheaf.exists_map_app_eq_zero_of_isColimit`: a section dying in the colimit dies at a
  finite stage.
- `TopCat.Sheaf.exists_app_eq_of_isColimit`: every section of the colimit comes from a finite
  stage.
-/

@[expose] public section

universe u

open CategoryTheory Limits TopologicalSpace Opposite

namespace TopCat.Sheaf

variable {X : TopCat.{u}} {J : Type u} [SmallCategory J]
  {D : J ⥤ CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}}

/-- The comparison map from the colimit of the underlying presheaves of a diagram of abelian
sheaves to the underlying presheaf of a cocone. -/
noncomputable def colimitPresheafToPt (c : Cocone D) :
    colimit (D ⋙ sheafToPresheaf _ _) ⟶ c.pt.obj :=
  colimit.desc _ ((sheafToPresheaf _ _).mapCocone c)

lemma colimitPresheafToPt_eq {c : Cocone D} (hc : IsColimit c) :
    colimitPresheafToPt c = toSheafify _ _ ≫
      ((Sheaf.isColimitSheafifyCocone _ (colimit.isColimit _)).coconePointUniqueUpToIso hc).hom.hom
    := by
  refine colimit.hom_ext fun j ↦ ?_
  rw [colimitPresheafToPt, colimit.ι_desc, ← Category.assoc]
  have h := Sheaf.sheafifyCocone_ι_app_val (colimit.cocone (D ⋙ sheafToPresheaf _ _)) j
  rw [colimit.cocone_ι] at h
  rw [← h, ← ObjectProperty.FullSubcategory.comp_hom, IsColimit.comp_coconePointUniqueUpToIso_hom]
  rfl

instance (c : Cocone D) [Nonempty (IsColimit c)] :
    Presheaf.IsLocallyInjective (Opens.grothendieckTopology X) (colimitPresheafToPt c) := by
  obtain ⟨hc⟩ := ‹Nonempty (IsColimit c)›
  rw [colimitPresheafToPt_eq hc]
  have : IsIso ((Sheaf.isColimitSheafifyCocone _
      (colimit.isColimit _)).coconePointUniqueUpToIso hc).hom.hom :=
    inferInstanceAs (IsIso ((sheafToPresheaf _ _).mapIso
      ((Sheaf.isColimitSheafifyCocone _ (colimit.isColimit _)).coconePointUniqueUpToIso hc)).hom)
  have : Presheaf.IsLocallyInjective (Opens.grothendieckTopology X)
      (toSheafify (Opens.grothendieckTopology X) (colimit.cocone (D ⋙ sheafToPresheaf _ _)).pt) :=
    Presheaf.isLocallyInjective_toSheafify' (J := Opens.grothendieckTopology X) _
  exact Presheaf.isLocallyInjective_comp _ _ _

instance (c : Cocone D) [Nonempty (IsColimit c)] :
    Presheaf.IsLocallySurjective (Opens.grothendieckTopology X) (colimitPresheafToPt c) := by
  obtain ⟨hc⟩ := ‹Nonempty (IsColimit c)›
  rw [colimitPresheafToPt_eq hc]
  have : IsIso ((Sheaf.isColimitSheafifyCocone _
      (colimit.isColimit _)).coconePointUniqueUpToIso hc).hom.hom :=
    inferInstanceAs (IsIso ((sheafToPresheaf _ _).mapIso
      ((Sheaf.isColimitSheafifyCocone _ (colimit.isColimit _)).coconePointUniqueUpToIso hc)).hom)
  have : Presheaf.IsLocallySurjective (Opens.grothendieckTopology X)
      (toSheafify (Opens.grothendieckTopology X) (colimit.cocone (D ⋙ sheafToPresheaf _ _)).pt) :=
    Presheaf.isLocallySurjective_toSheafify' (J := Opens.grothendieckTopology X) _
  exact Presheaf.isLocallySurjective_comp _ _ _

lemma cocone_ι_app_map_apply (c : Cocone D) {j j' : J} (f : j ⟶ j') (V : (Opens X)ᵒᵖ)
    (t : (D.obj j).obj.obj V) :
    (c.ι.app j').hom.app V ((D.map f).hom.app V t) = (c.ι.app j).hom.app V t := by
  rw [← c.w f]
  rfl

lemma map_comp_hom_app_apply {j j' j'' : J} (f : j ⟶ j') (g : j' ⟶ j'') (V : (Opens X)ᵒᵖ)
    (t : (D.obj j).obj.obj V) :
    (D.map (f ≫ g)).hom.app V t = (D.map g).hom.app V ((D.map f).hom.app V t) := by
  rw [D.map_comp]
  rfl

/-- The sections of the colimit of the underlying presheaves over `V` are represented by the
sections of the members of the diagram. -/
lemma exists_colimit_ι_app_eq [IsFiltered J] (V : (Opens X)ᵒᵖ)
    (a : (colimit (D ⋙ sheafToPresheaf _ _)).obj V) :
    ∃ (j : J) (t : (D.obj j).obj.obj V), (colimit.ι (D ⋙ sheafToPresheaf _ _) j).app V t = a :=
  Concrete.isColimit_exists_rep _
    (isColimitOfPreserves ((evaluation _ _).obj V) (colimit.isColimit _)) a

/-- A section of the colimit `c` lifts locally to a section of a member of the diagram. -/
lemma exists_app_eq_map_of_isColimit [IsFiltered J] {c : Cocone D} (hc : IsColimit c)
    {V : Opens X} (s : c.pt.obj.obj (op V)) {x : X} (hx : x ∈ V) :
    ∃ (W : Opens X) (hWV : W ≤ V) (_ : x ∈ W) (j : J) (t : (D.obj j).obj.obj (op W)),
      (c.ι.app j).hom.app (op W) t = c.pt.obj.map (homOfLE hWV).op s := by
  have : Nonempty (IsColimit c) := ⟨hc⟩
  obtain ⟨W, f, ⟨a, ha⟩, hxW⟩ := (Opens.mem_grothendieckTopology X).1
    (Presheaf.imageSieve_mem (Opens.grothendieckTopology X) (colimitPresheafToPt c) s) x hx
  obtain ⟨j, t, rfl⟩ := exists_colimit_ι_app_eq (op W) a
  refine ⟨W, f.le, hxW, j, t, ?_⟩
  have hf : f = homOfLE f.le := Subsingleton.elim _ _
  rw [← hf, ← ha]
  change _ = ((colimit.ι (D ⋙ sheafToPresheaf _ _) j) ≫ colimitPresheafToPt c).app (op W) t
  rw [colimitPresheafToPt, colimit.ι_desc]
  rfl

/-- A section of a member of the diagram which dies in the colimit `c` dies locally at a later
stage. -/
lemma exists_map_app_eq_zero_locally_of_isColimit [IsFiltered J] {c : Cocone D}
    (hc : IsColimit c) {V : Opens X} {j : J} (t : (D.obj j).obj.obj (op V))
    (ht : (c.ι.app j).hom.app (op V) t = 0) {x : X} (hx : x ∈ V) :
    ∃ (W : Opens X) (hWV : W ≤ V) (_ : x ∈ W) (k : J) (f : j ⟶ k),
      (D.map f).hom.app (op W) ((D.obj j).obj.map (homOfLE hWV).op t) = 0 := by
  have : Nonempty (IsColimit c) := ⟨hc⟩
  let a := (colimit.ι (D ⋙ sheafToPresheaf _ _) j).app (op V) t
  have ha : (colimitPresheafToPt c).app (op V) a = (colimitPresheafToPt c).app (op V) 0 := by
    rw [map_zero, ← ht]
    change ((colimit.ι (D ⋙ sheafToPresheaf _ _) j) ≫ colimitPresheafToPt c).app (op V) t = _
    rw [colimitPresheafToPt, colimit.ι_desc]
    rfl
  obtain ⟨W, f, hf, hxW⟩ := (Opens.mem_grothendieckTopology X).1
    (Presheaf.IsLocallyInjective.equalizerSieve_mem (J := Opens.grothendieckTopology X) _ _ ha)
    x hx
  change (colimit (D ⋙ sheafToPresheaf _ _)).map f.op a =
    (colimit (D ⋙ sheafToPresheaf _ _)).map f.op 0 at hf
  rw [map_zero, ← NatTrans.naturality_apply] at hf
  have hW := (Concrete.isColimit_rep_eq_iff_exists
    ((D ⋙ sheafToPresheaf _ _) ⋙ (evaluation _ _).obj (op W))
    (isColimitOfPreserves ((evaluation _ _).obj (op W)) (colimit.isColimit _)) (i := j) (j := j)
    ((D.obj j).obj.map f.op t) (0 : (D.obj j).obj.obj (op W))).1 (by
      refine hf.trans ?_
      exact (map_zero _).symm)
  obtain ⟨k, g, g', hg⟩ := hW
  refine ⟨W, f.le, hxW, k, g, ?_⟩
  refine hg.trans ?_
  exact map_zero _

/-- **Sections of filtered colimits over quasi-compact opens, injectivity.** A section over a
quasi-compact open `U` of a member `D_j` of a filtered diagram of abelian sheaves which dies in
the colimit already dies in some `D_k`. -/
theorem exists_map_app_eq_zero_of_isColimit [IsFiltered J] {c : Cocone D} (hc : IsColimit c)
    {U : Opens X} (hU : IsCompact (U : Set X)) {j : J} (t : (D.obj j).obj.obj (op U))
    (ht : (c.ι.app j).hom.app (op U) t = 0) :
    ∃ (k : J) (f : j ⟶ k), (D.map f).hom.app (op U) t = 0 := by
  classical
  choose W hWU hxW k f hf using fun x : U ↦
    exists_map_app_eq_zero_locally_of_isColimit hc t ht x.2
  obtain ⟨s, hs⟩ := hU.elim_finite_subcover (fun x : U ↦ (W x : Set X)) (fun x ↦ (W x).isOpen)
    fun x hx ↦ Set.mem_iUnion.2 ⟨⟨x, hx⟩, hxW _⟩
  let O : Finset J := insert j (s.image k)
  let H : Finset (Σ' (Y Z : J) (_ : Y ∈ O) (_ : Z ∈ O), Y ⟶ Z) :=
    s.attach.image fun x ↦ ⟨j, k x.1, Finset.mem_insert_self _ _,
      Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ x.2), f x.1⟩
  have hj : j ∈ O := Finset.mem_insert_self _ _
  refine ⟨IsFiltered.sup O H, IsFiltered.toSup O H hj, ?_⟩
  refine TopCat.Sheaf.eq_of_locally_eq' (D.obj _) (fun x : s ↦ W x.1) U
    (fun x ↦ homOfLE (hWU x.1)) (fun y hy ↦ ?_) _ _ fun x ↦ ?_
  · obtain ⟨x, hx, hyx⟩ := Set.mem_iUnion₂.1 (hs hy)
    exact Opens.mem_iSup.2 ⟨⟨x, hx⟩, hyx⟩
  · have hk : k x.1 ∈ O := Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ x.2)
    have hcomm := IsFiltered.toSup_commutes O H (f := f x.1) hj hk
      (Finset.mem_image.2 ⟨⟨x.1, x.2⟩, Finset.mem_attach _ _, rfl⟩)
    rw [map_zero, ← NatTrans.naturality_apply, ← hcomm, map_comp_hom_app_apply, hf, map_zero]

variable [PrespectralSpace X] [QuasiSeparatedSpace X]

/-- **Sections of filtered colimits over quasi-compact opens, surjectivity.** Every section over
a quasi-compact open `U` of the colimit of a filtered diagram of abelian sheaves comes from a
section of some member of the diagram. -/
theorem exists_app_eq_of_isColimit [IsFiltered J] {c : Cocone D} (hc : IsColimit c)
    {U : Opens X} (hU : IsCompact (U : Set X)) (s : c.pt.obj.obj (op U)) :
    ∃ (j : J) (t : (D.obj j).obj.obj (op U)), (c.ι.app j).hom.app (op U) t = s := by
  classical
  -- local lifts over quasi-compact opens
  have hloc (x : U) : ∃ (W : Opens X) (hWU : W ≤ U) (_ : x.1 ∈ W) (_ : IsCompact (W : Set X))
      (j : J) (t : (D.obj j).obj.obj (op W)),
        (c.ι.app j).hom.app (op W) t = c.pt.obj.map (homOfLE hWU).op s := by
    obtain ⟨W, hWU, hxW, j, t, ht⟩ := exists_app_eq_map_of_isColimit hc s x.2
    obtain ⟨W', ⟨hW'o, hW'c⟩, hxW', hW'W⟩ :=
      PrespectralSpace.isTopologicalBasis.exists_subset_of_mem_open (a := x.1) hxW W.isOpen
    refine ⟨⟨W', hW'o⟩, (show (⟨W', hW'o⟩ : Opens X) ≤ W from hW'W).trans hWU, hxW', hW'c, j,
      (D.obj j).obj.map (homOfLE (show (⟨W', hW'o⟩ : Opens X) ≤ W from hW'W)).op t, ?_⟩
    rw [NatTrans.naturality_apply, ht]
    change c.pt.obj.map _ (c.pt.obj.map _ s) = _
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
    rfl
  choose W hWU hxW hWc j t ht using hloc
  obtain ⟨s₀, hs₀⟩ := hU.elim_finite_subcover (fun x : U ↦ (W x : Set X)) (fun x ↦ (W x).isOpen)
    fun x hx ↦ Set.mem_iUnion.2 ⟨⟨x, hx⟩, hxW _⟩
  have hcov : U ≤ iSup fun x : s₀ ↦ W x.1 := fun y hy ↦ by
    obtain ⟨x, hx, hyx⟩ := Set.mem_iUnion₂.1 (hs₀ hy)
    exact Opens.mem_iSup.2 ⟨⟨x, hx⟩, hyx⟩
  -- a common stage for the local lifts
  let O₁ : Finset J := s₀.image j
  let m₁ := IsFiltered.sup O₁ ∅
  have hj₁ (x : s₀) : j x.1 ∈ O₁ := Finset.mem_image_of_mem _ x.2
  let g₁ (x : s₀) : j x.1 ⟶ m₁ := IsFiltered.toSup O₁ ∅ (hj₁ x)
  let t₁ (x : s₀) : (D.obj m₁).obj.obj (op (W x.1)) := (D.map (g₁ x)).hom.app _ (t x.1)
  have ht₁ (x : s₀) : (c.ι.app m₁).hom.app _ (t₁ x) = c.pt.obj.map (homOfLE (hWU x.1)).op s := by
    rw [cocone_ι_app_map_apply, ht]
  -- the differences on the overlaps die at a later stage
  have hdiff (x y : s₀) : ∃ (k : J) (f : m₁ ⟶ k), (D.map f).hom.app _
      ((D.obj m₁).obj.map (homOfLE (inf_le_left : W x.1 ⊓ W y.1 ≤ W x.1)).op (t₁ x) -
        (D.obj m₁).obj.map (homOfLE (inf_le_right : W x.1 ⊓ W y.1 ≤ W y.1)).op (t₁ y)) = 0 := by
    refine exists_map_app_eq_zero_of_isColimit hc
      (QuasiSeparatedSpace.inter_isCompact _ _ (W x.1).isOpen (hWc x.1) (W y.1).isOpen (hWc y.1))
      _ ?_
    rw [map_sub, NatTrans.naturality_apply, NatTrans.naturality_apply, ht₁, ht₁]
    change c.pt.obj.map _ (c.pt.obj.map _ s) - c.pt.obj.map _ (c.pt.obj.map _ s) = 0
    rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, ← Functor.map_comp,
      ← Functor.map_comp, sub_eq_zero]
    rfl
  choose k f hf using hdiff
  let O₂ : Finset J := insert m₁ ((s₀.attach ×ˢ s₀.attach).image fun p ↦ k p.1 p.2)
  have hm₁ : m₁ ∈ O₂ := Finset.mem_insert_self _ _
  have hk (x y : s₀) : k x y ∈ O₂ := Finset.mem_insert_of_mem (Finset.mem_image.2
    ⟨(⟨x, x.2⟩, ⟨y, y.2⟩), Finset.mem_product.2 ⟨Finset.mem_attach _ _, Finset.mem_attach _ _⟩,
      rfl⟩)
  let H₂ : Finset (Σ' (Y Z : J) (_ : Y ∈ O₂) (_ : Z ∈ O₂), Y ⟶ Z) :=
    (s₀.attach ×ˢ s₀.attach).image fun p ↦ ⟨m₁, k p.1 p.2, hm₁, hk p.1 p.2, f p.1 p.2⟩
  let m₂ := IsFiltered.sup O₂ H₂
  let g₂ : m₁ ⟶ m₂ := IsFiltered.toSup O₂ H₂ hm₁
  have hg₂ (x y : s₀) : f x y ≫ IsFiltered.toSup O₂ H₂ (hk x y) = g₂ :=
    IsFiltered.toSup_commutes O₂ H₂ hm₁ (hk x y) (Finset.mem_image.2
      ⟨(⟨x, x.2⟩, ⟨y, y.2⟩), Finset.mem_product.2 ⟨Finset.mem_attach _ _, Finset.mem_attach _ _⟩,
        rfl⟩)
  let t₂ (x : s₀) : (D.obj m₂).obj.obj (op (W x.1)) := (D.map g₂).hom.app _ (t₁ x)
  -- glue the lifts at the stage `m₂`
  obtain ⟨σ, hσ, -⟩ := TopCat.Sheaf.existsUnique_gluing' (D.obj m₂) (fun x : s₀ ↦ W x.1) U
    (fun x ↦ homOfLE (hWU x.1)) hcov t₂ fun x y ↦ by
      have h := congrArg ((D.map (IsFiltered.toSup O₂ H₂ (hk x y))).hom.app _) (hf x y)
      rw [map_zero, ← map_comp_hom_app_apply, hg₂ x y, map_sub, sub_eq_zero,
        NatTrans.naturality_apply, NatTrans.naturality_apply] at h
      exact h
  refine ⟨m₂, σ, TopCat.Sheaf.eq_of_locally_eq' c.pt (fun x : s₀ ↦ W x.1) U
    (fun x ↦ homOfLE (hWU x.1)) hcov _ _ fun x ↦ ?_⟩
  refine (NatTrans.naturality_apply (c.ι.app m₂).hom (homOfLE (hWU x.1)).op σ).symm.trans ?_
  change (c.ι.app m₂).hom.app _ ((D.obj m₂).obj.map _ σ) = _
  rw [hσ x]
  exact (cocone_ι_app_map_apply c g₂ _ _).trans (ht₁ x)

end TopCat.Sheaf
