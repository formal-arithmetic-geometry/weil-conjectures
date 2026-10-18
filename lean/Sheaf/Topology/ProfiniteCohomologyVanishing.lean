/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NR
-/
module

public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.Topology.Sheaves.Sheaf
public import Mathlib.Topology.Separation.Profinite
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.Algebra.Category.Grp.AB
public import WeilConjectures.Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Topology.Sheaves.LocallySurjective
import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughProjectives

/-!
# Abelian sheaf cohomology on a profinite topological space

Source: Stacks Project, Cohomology of Sheaves, Tag 0A3F,
`lemma-vanishing-for-profinite`
(blueprint: lem-cbc-profinite-topological-cohomology-vanishing).
-/

@[expose] public section

universe u

open CategoryTheory TopologicalSpace

namespace TopCat.Sheaf

private lemma surjective_app_top_of_profinite
    (X : TopCat.{u}) [CompactSpace X] [T2Space X] [TotallyDisconnectedSpace X]
    {F E : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}}
    (f : F ⟶ E) [Epi f] : Function.Surjective (f.hom.app (Opposite.op ⊤)) := by
  classical
  intro e
  have hlocal := (TopCat.Presheaf.isLocallySurjective_iff f.hom).mp
    ((TopCat.Sheaf.isLocallySurjective_iff_epi f).mpr inferInstance)
  have hlift (x : X) : ∃ (V : Opens X) (s : F.obj.obj (Opposite.op V)),
      x ∈ V ∧ f.hom.app (Opposite.op V) s = E.obj.map (homOfLE (show V ≤ ⊤ from le_top)).op e := by
    obtain ⟨V, hV, ⟨s, hs⟩, hx⟩ := hlocal ⊤ e x (by trivial)
    exact ⟨V, s, hx, hs⟩
  choose V s hx hs using hlift
  choose C hC hxC hCV using fun x ↦
    compact_exists_isClopen_in_isOpen (V x).isOpen (hx x)
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover C (fun x ↦ (hC x).isOpen)
    (fun x _ ↦ Set.mem_iUnion.mpr ⟨x, hxC x⟩)
  obtain ⟨D, hD, _, hDC, hcover, hdisj⟩ :=
    exists_clopen_partition_of_clopen_cover
      (Z := fun _ : t ↦ (∅ : Set X)) (D := fun i : t ↦ C i)
      (fun _ ↦ isClosed_empty) (fun i ↦ hC i) (by simp) (by
        intro i _ j _ hij
        exact disjoint_bot_left)
  let W : t → Opens X := fun i ↦ ⟨D i, (hD i).isOpen⟩
  have hWV (i : t) : W i ≤ V i := fun x hx ↦ hCV i (hDC i hx)
  let a : ∀ i : t, F.obj.obj (Opposite.op (W i)) := fun i ↦
    F.obj.map (homOfLE (hWV i)).op (s i)
  have hW : (⊤ : Opens X) ≤ iSup W := by
    intro x _
    obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ x))
    have hxD := hcover (Set.mem_iUnion.mpr ⟨⟨i, hi⟩, hxi⟩)
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hxD
    exact Opens.mem_iSup.mpr ⟨j, hj⟩
  have hcompat : TopCat.Presheaf.IsCompatible F.obj W a := by
    intro i j
    by_cases hij : i = j
    · subst j
      rfl
    · have hempty : W i ⊓ W j = ⊥ := by
        apply Opens.ext
        exact Set.disjoint_iff_inter_eq_empty.mp
          (hdisj (Set.mem_univ i) (Set.mem_univ j) hij)
      have : Subsingleton (F.obj.obj (Opposite.op (W i ⊓ W j))) :=
        AddCommGrpCat.subsingleton_of_isZero
          (TopCat.Sheaf.isTerminalOfEqEmpty F hempty).isZero
      exact Subsingleton.elim _ _
  obtain ⟨b, hb, _⟩ :=
    TopCat.Sheaf.existsUnique_gluing' F W ⊤ (fun _ ↦ homOfLE le_top) hW a hcompat
  refine ⟨b, ?_⟩
  apply TopCat.Sheaf.eq_of_locally_eq' E W ⊤ (fun _ ↦ homOfLE le_top) hW
  intro i
  rw [← NatTrans.naturality_apply, hb]
  dsimp [a]
  rw [NatTrans.naturality_apply, hs]
  rw [← ConcreteCategory.comp_apply, ← E.obj.map_comp]
  rfl

private noncomputable def sectionsEquiv
    (X : TopCat.{u})
    (F : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) :
    ((presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
      (yoneda.obj (⊤ : Opens X) ⋙ AddCommGrpCat.free) ⟶ F) ≃ F.obj.obj (Opposite.op ⊤) :=
  ((sheafificationAdjunction _ AddCommGrpCat.{u}).homEquiv _ F).trans
    (((AddCommGrpCat.adj.whiskerRight (C := (Opens X)ᵒᵖ)).homEquiv
      (yoneda.obj ⊤) F.obj).trans yonedaEquiv)

private lemma sectionsEquiv_naturality
    (X : TopCat.{u})
    {F E : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}}
    (f : F ⟶ E)
    (a : (presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
      (yoneda.obj (⊤ : Opens X) ⋙ AddCommGrpCat.free) ⟶ F) :
    sectionsEquiv X E (a ≫ f) = f.hom.app (Opposite.op ⊤) (sectionsEquiv X F a) := by
  unfold sectionsEquiv
  dsimp only [Equiv.trans_apply]
  rw [Adjunction.homEquiv_naturality_right]
  rfl

private lemma projective_freeSheaf_top_of_profinite
    (X : TopCat.{u}) [CompactSpace X] [T2Space X] [TotallyDisconnectedSpace X] :
    Projective ((presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
      (yoneda.obj (⊤ : Opens X) ⋙ AddCommGrpCat.free)) := by
  constructor
  intro F E a f hf
  obtain ⟨b, hb⟩ := surjective_app_top_of_profinite X f (sectionsEquiv X E a)
  refine ⟨(sectionsEquiv X F).symm b, (sectionsEquiv X E).injective ?_⟩
  rw [sectionsEquiv_naturality, Equiv.apply_symm_apply, hb]

/-- Every abelian sheaf on a compact Hausdorff totally disconnected space has zero
cohomology in positive degree. The cohomology is the recorded `Sheaf.H'` at the top open.

Source: Stacks Project, Cohomology of Sheaves, Tag 0A3F
(blueprint: lem-cbc-profinite-topological-cohomology-vanishing).

Proof:
1. An epimorphism is locally surjective, by
   lem-sc-abelian-sheaf-epi-iff-stalk-epi. Thus a global section of the target
   lifts on an open neighbourhood of every point.
2. Refine these neighbourhoods by clopens using lem-weil-pbc-profinite-clopen-basis.
   Choose a finite subcover by compactness and apply Mathlib's
   exists_clopen_partition_of_clopen_cover, with all prescribed closed sets empty,
   to obtain pairwise disjoint clopen pieces subordinate to the subcover.
3. Restrict the lifts to the pieces and glue. On distinct pieces their restrictions
   agree because the sheaf has a zero group of sections over the empty intersection.
   Uniqueness of gluing shows that the image is the prescribed global section.
   This also works for the empty space, with the empty cover.
4. Sheafification adjunction, the free abelian group adjunction, and Yoneda identify
   maps from the free abelian sheaf on the representable of the top open with global
   sections, naturally in the sheaf. Step 3 therefore proves that this free sheaf
   is projective, directly by the lifting definition of projectivity.
5. By def-sc-topological-abelian-cohomology, H' is Ext from that free sheaf.
   Positive Ext from a projective object vanishes (def-pc-ext, current blueprint;
   Mathlib's Abelian.Ext.subsingleton_of_projective), proving the result directly.
-/
theorem subsingleton_H'_top_of_profinite
    (X : TopCat.{u}) [CompactSpace X] [T2Space X] [TotallyDisconnectedSpace X]
    (G : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
    (q : ℕ) (hq : 0 < q) :
    Subsingleton
      (@CategoryTheory.Sheaf.H'.{u, u, u}
        (Opens X) inferInstance (Opens.grothendieckTopology X) inferInstance
        (@hasExt_of_enoughInjectives _ _ _ inferInstance
          (@IsGrothendieckAbelian.enoughInjectives _ _ _
            (CategoryTheory.Sheaf.isGrothendieckAbelian_of_essentiallySmall'.{u}
              (Opens.grothendieckTopology X) AddCommGrpCat.{u}))) G q ⊤) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hq)
  let : HasExt.{u}
      (CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) :=
    @hasExt_of_enoughInjectives _ _ _ inferInstance
      (@IsGrothendieckAbelian.enoughInjectives _ _ _
        (CategoryTheory.Sheaf.isGrothendieckAbelian_of_essentiallySmall'.{u}
          (Opens.grothendieckTopology X) AddCommGrpCat.{u}))
  let := projective_freeSheaf_top_of_profinite X
  change Subsingleton (Abelian.Ext
    ((presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
      (yoneda.obj (⊤ : Opens X) ⋙ AddCommGrpCat.free)) G (n + 1))
  exact Abelian.Ext.subsingleton_of_projective _ G n

end TopCat.Sheaf
