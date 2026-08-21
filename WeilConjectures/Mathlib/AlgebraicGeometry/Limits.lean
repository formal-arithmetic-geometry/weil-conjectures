/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Properties

/-!

# Finite affine open covers with dense total intersection

A scheme with finitely many irreducible components has, around every point, an affine open
neighbourhood containing the generic points of *all* the irreducible components
(`AlgebraicGeometry.exists_isAffineOpen_mem_and_genericPoints_subset`). This is the special
case of Stacks Project Tag 01ZX in which the selected points are the generic points of all
the (finitely many) components; since the components cover the scheme, the auxiliary affine
opens can be chosen pairwise disjoint outright and no quasi-separatedness is needed.

Consequently, a quasi-compact scheme with finitely many irreducible components has a finite
affine open cover whose total intersection is dense
(`AlgebraicGeometry.exists_isAffineOpen_iSup_eq_top_and_dense_iInter`, blueprint:
`lemma:nagata-dense-affine-cover-exists`): the intersection of the neighbourhoods above
contains every generic point, and the generic points are dense. This is the affine cover
over which the Noetherian case of Nagata's compactification theorem performs its induction
(blueprint: `def:nagata-noetherian-compactification`).

## Main results

- `AlgebraicGeometry.exists_isAffineOpen_mem_and_genericPoints_subset`: on a scheme with
  finitely many irreducible components, every point has an affine open neighbourhood
  containing all generic points (blueprint:
  `lemma:nagata-affine-neighbourhood-generic-points-exists`);
- `AlgebraicGeometry.exists_isAffineOpen_iSup_eq_top_and_dense_iInter`: a quasi-compact
  scheme with finitely many irreducible components has a finite affine open cover with
  dense total intersection (blueprint: `lemma:nagata-dense-affine-cover-exists`).

-/

@[expose] public section

universe u

open TopologicalSpace

namespace AlgebraicGeometry

variable {X : Scheme.{u}}

/-- On a scheme with finitely many irreducible components, every point has an affine open
neighbourhood containing the generic points of all the irreducible components.

This is Stacks Project Tag 01ZX in the case where the selected points are the generic
points of all the components: an affine open `W` through `x` avoiding the components not
through `x` lies in the union of the components through `x`, hence so does its closure; the
remaining generic points therefore admit affine opens avoiding `closure W` and every other
component, and these are pairwise disjoint because the components cover `X`, so the union
of all these opens is affine. In this case quasi-separatedness of `X` is not needed
(blueprint: `lemma:nagata-affine-neighbourhood-generic-points-exists`). -/
@[stacks 01ZX "The case where the selected points are the generic points of all the
irreducible components; quasi-separatedness is not needed then."]
theorem exists_isAffineOpen_mem_and_genericPoints_subset
    (hX : (irreducibleComponents X).Finite) (x : X) :
    ∃ U : X.Opens, IsAffineOpen U ∧ x ∈ U ∧ genericPoints X ⊆ (U : Set X) := by
  classical
  -- Distinct irreducible components are incomparable.
  have hanti : ∀ {Z Z' : Set X}, Z ∈ irreducibleComponents X →
      Z' ∈ irreducibleComponents X → Z ⊆ Z' → Z = Z' := fun hZ hZ' h ↦ hZ.eq_of_le hZ'.1 h
  -- A generic point lies in no irreducible component other than the closure of itself.
  have hnotMem : ∀ y ∈ genericPoints X, ∀ Z ∈ irreducibleComponents X,
      Z ≠ closure {y} → y ∉ Z := fun y hy Z hZ hne hyZ ↦
    hne (hanti (show closure {y} ∈ irreducibleComponents X from hy) hZ
      (closure_minimal (Set.singleton_subset_iff.mpr hyZ)
        (isClosed_of_mem_irreducibleComponents Z hZ))).symm
  -- The components not through `x` respectively through `x`.
  set T : Set (Set X) := {Z ∈ irreducibleComponents X | x ∉ Z} with hT_def
  set S : Set (Set X) := {Z ∈ irreducibleComponents X | x ∈ Z} with hS_def
  have hTfin : T.Finite := hX.subset fun Z hZ ↦ hZ.1
  have hSfin : S.Finite := hX.subset fun Z hZ ↦ hZ.1
  -- An affine open neighbourhood `W` of `x` avoiding every component not through `x`.
  have hTclosed : IsClosed (⋃ Z ∈ T, Z) :=
    hTfin.isClosed_biUnion fun Z hZ ↦ isClosed_of_mem_irreducibleComponents Z hZ.1
  have hx : x ∈ (⟨_, hTclosed.isOpen_compl⟩ : X.Opens) := by
    change x ∉ ⋃ Z ∈ T, Z
    intro h
    obtain ⟨Z, hZ, hxZ⟩ := Set.mem_iUnion₂.mp h
    exact hZ.2 hxZ
  obtain ⟨W, hWaff, hxW, hWsub⟩ :=
    exists_isAffineOpen_mem_and_subset (U := ⟨_, hTclosed.isOpen_compl⟩) hx
  -- `W` lies in the union of the components through `x`, hence so does its closure.
  have hWS : closure (W : Set X) ⊆ ⋃ Z ∈ S, Z := by
    refine closure_minimal (fun y hy ↦ ?_)
      (hSfin.isClosed_biUnion fun Z hZ ↦ isClosed_of_mem_irreducibleComponents Z hZ.1)
    have hyc : irreducibleComponent y ∈ irreducibleComponents X :=
      irreducibleComponent_mem_irreducibleComponents y
    by_cases hxc : x ∈ irreducibleComponent y
    · exact Set.mem_biUnion (show irreducibleComponent y ∈ S from ⟨hyc, hxc⟩)
        mem_irreducibleComponent
    · exact absurd (show y ∈ ⋃ Z ∈ T, Z from Set.mem_biUnion
        (show irreducibleComponent y ∈ T from ⟨hyc, hxc⟩) mem_irreducibleComponent)
        (hWsub hy)
  -- Around each generic point not through `x`, an affine open disjoint from `closure W`
  -- and from every other component.
  have key : ∀ y : X, y ∈ genericPoints X → x ∉ closure {y} →
      ∃ V : X.Opens, IsAffineOpen V ∧ y ∈ V ∧
        (V : Set X) ⊆ (closure (W : Set X))ᶜ ∧
        ∀ Z ∈ irreducibleComponents X, Z ≠ closure {y} → (V : Set X) ⊆ Zᶜ := by
    intro y hy hxy
    have hRfin : {Z ∈ irreducibleComponents X | Z ≠ closure {y}}.Finite :=
      hX.subset fun Z hZ ↦ hZ.1
    have hclosed : IsClosed (closure (W : Set X) ∪
        ⋃ Z ∈ {Z ∈ irreducibleComponents X | Z ≠ closure {y}}, Z) :=
      isClosed_closure.union
        (hRfin.isClosed_biUnion fun Z hZ ↦ isClosed_of_mem_irreducibleComponents Z hZ.1)
    have hymem : y ∈ (⟨_, hclosed.isOpen_compl⟩ : X.Opens) := by
      change y ∉ closure (W : Set X) ∪
        ⋃ Z ∈ {Z ∈ irreducibleComponents X | Z ≠ closure {y}}, Z
      intro hmem
      rcases (Set.mem_union _ _ _).mp hmem with hyW | hyU
      · obtain ⟨Z, hZS, hyZ⟩ := Set.mem_iUnion₂.mp (hWS hyW)
        have : closure {y} = Z := hanti (show closure {y} ∈ irreducibleComponents X from hy)
          hZS.1 (closure_minimal (Set.singleton_subset_iff.mpr hyZ)
            (isClosed_of_mem_irreducibleComponents Z hZS.1))
        exact hxy (this ▸ hZS.2)
      · obtain ⟨Z, hZ, hyZ⟩ := Set.mem_iUnion₂.mp hyU
        exact hnotMem y hy Z hZ.1 hZ.2 hyZ
    obtain ⟨V, hVaff, hyV, hVsub⟩ :=
      exists_isAffineOpen_mem_and_subset (U := ⟨_, hclosed.isOpen_compl⟩) hymem
    refine ⟨V, hVaff, hyV, fun z hz hzW ↦ hVsub hz (Or.inl hzW),
      fun Z hZ hne z hz hzZ ↦ hVsub hz (Or.inr (Set.mem_biUnion ⟨hZ, hne⟩ hzZ))⟩
  choose! V hVaff hVmem hVW hVcomp using key
  -- The generic points not through `x`.
  set G : Set X := {y ∈ genericPoints X | x ∉ closure {y}} with hG_def
  have hGfin : G.Finite := (genericPoints.finite hX).subset fun y hy ↦ hy.1
  -- The chosen affine opens are pairwise disjoint since the components cover `X`.
  have hpair : G.Pairwise (Function.onFun Disjoint V) := by
    intro y hy z hz hyz
    have hyz' : closure {y} ≠ closure {z} :=
      fun h ↦ hyz ((show IsGenericPoint y _ from h).eq rfl)
    rw [Function.onFun, ← Opens.coe_disjoint, Set.disjoint_left]
    intro a hay haz
    have hac := irreducibleComponent_mem_irreducibleComponents a
    rcases eq_or_ne (irreducibleComponent a) (closure {y}) with h | h
    · exact absurd mem_irreducibleComponent
        (hVcomp z hz.1 hz.2 _ hac (by rw [h]; exact hyz') haz)
    · exact absurd mem_irreducibleComponent (hVcomp y hy.1 hy.2 _ hac h hay)
  refine ⟨W ⊔ ⨆ y ∈ G, V y, ?_, ?_, ?_⟩
  · -- `W` is disjoint from each of the chosen affine opens, so the union is affine.
    refine hWaff.sup_of_disjoint
      (.biSup_of_disjoint hGfin (fun y hy ↦ hVaff y hy.1 hy.2) hpair) ?_
    simp only [disjoint_iSup_iff]
    intro y hy
    rw [← Opens.coe_disjoint, Set.disjoint_left]
    exact fun a haW haV ↦ hVW y hy.1 hy.2 haV (subset_closure haW)
  · exact Opens.mem_sup.mpr (Or.inl hxW)
  · intro y hy
    by_cases hxy : x ∈ closure {y}
    · refine Opens.mem_sup.mpr (Or.inl ?_)
      by_contra hyW
      exact (closure_minimal (Set.singleton_subset_iff.mpr hyW)
        (isClosed_compl_iff.mpr W.isOpen) hxy) hxW
    · exact Opens.mem_sup.mpr (Or.inr (Opens.mem_iSup.mpr
        ⟨y, Opens.mem_iSup.mpr ⟨⟨hy, hxy⟩, hVmem y hy hxy⟩⟩))

/-- A quasi-compact scheme with finitely many irreducible components has a finite affine
open cover whose total intersection is dense: around every point choose an affine open
containing all generic points and pass to a finite subcover; the total intersection then
still contains all generic points, whose closure is everything (blueprint:
`lemma:nagata-dense-affine-cover-exists`). -/
theorem exists_isAffineOpen_iSup_eq_top_and_dense_iInter
    (X : Scheme.{u}) [CompactSpace X] (hX : (irreducibleComponents X).Finite) :
    ∃ (n : ℕ) (U : Fin n → X.Opens), (∀ i, IsAffineOpen (U i)) ∧ (⨆ i, U i) = ⊤ ∧
      Dense (⋂ i, (U i : Set X)) := by
  choose U hUaff hUmem hUgen using exists_isAffineOpen_mem_and_genericPoints_subset hX
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun x ↦ (U x : Set X))
    (fun x ↦ (U x).isOpen) (fun x _ ↦ Set.mem_iUnion.mpr ⟨x, hUmem x⟩)
  refine ⟨t.card, fun i ↦ U (t.equivFin.symm i), fun i ↦ hUaff _, ?_, ?_⟩
  · rw [eq_top_iff]
    intro x _
    obtain ⟨y, hyt, hxy⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ x))
    exact Opens.mem_iSup.mpr ⟨t.equivFin ⟨y, hyt⟩, by simpa using hxy⟩
  · refine Dense.mono ?_ (dense_iff_closure_eq.mpr genericPoints.closure)
    exact Set.subset_iInter fun i ↦ hUgen _

end AlgebraicGeometry
