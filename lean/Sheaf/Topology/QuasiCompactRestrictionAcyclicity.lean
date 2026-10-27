/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NO
-/
module

public import Mathlib.Topology.Sheaves.Functors
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.Algebra.Category.Grp.AB
public import WeilConjectures.Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf

import Mathlib.Data.Fintype.Powerset
import Sheaf.Topology.CechVanishingSurjectiveUnions
import Sheaf.Topology.FilteredInjectiveCechAcyclic
import WeilConjectures.CategoryTheory.SiteCechVanishingCriterion

/-! # Acyclicity from surjective restrictions on quasi-compact opens

Source: Stacks Project, Cohomology of Sheaves, Tags 0A36 and 01EW, as used in
Tag 0A3G, proof of (1) from (2); Cohomology on Sites, Tag 03F9.
(blueprint: lem-sfb-quasi-compact-restriction-acyclicity)

The restriction in the conclusion is the ordinary restriction to the open subspace,
implemented by Mathlib's naive pullback along the open embedding. No compactness of
the ambient space, separation axiom, or Noetherian assumption is imposed.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory TopologicalSpace

namespace TopCat.Sheaf

private theorem isZero_H'_of_compact_restrictions
    {Y : Type u} [TopologicalSpace Y]
    [HasExt.{u} (CategoryTheory.Sheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u})]
    (hbasis : Opens.IsBasis {W : Opens Y | IsCompact (W : Set Y)})
    (hpairs : ∀ U V : Opens Y, IsCompact (U : Set Y) → IsCompact (V : Set Y) →
      IsCompact ((U ⊓ V : Opens Y) : Set Y))
    (F : CategoryTheory.Sheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u})
    (hres : ∀ (U V : Opens Y) (hUV : U ≤ V),
      IsCompact (U : Set Y) → IsCompact (V : Set Y) →
      Function.Surjective (F.obj.map (homOfLE hUV).op)) :
    ∀ (U : Opens Y), IsCompact (U : Set Y) → ∀ (p : ℕ), 0 < p →
      Limits.IsZero (CategoryTheory.Sheaf.H' F p U) := by
  classical
  have hJ : (Opens.grothendieckTopology Y).toPrecoverage =
      (Opens.pretopology Y).toPrecoverage := by
    rw [← Opens.toPretopology_grothendieckTopology]
    rfl
  have : (Opens.pretopology Y).toPrecoverage.HasIsos := hJ ▸ inferInstance
  have : (Opens.pretopology Y).toPrecoverage.IsStableUnderComposition := hJ ▸ inferInstance
  have : (Opens.pretopology Y).toPrecoverage.IsStableUnderBaseChange := hJ ▸ inferInstance
  have htop : (Opens.pretopology Y).toPrecoverage.toGrothendieck =
      Opens.grothendieckTopology Y := by
    change (Opens.pretopology Y).toCoverage.toPrecoverage.toGrothendieck = _
    rw [Coverage.toGrothendieck_toPrecoverage, Pretopology.toGrothendieck_toCoverage,
      Opens.pretopology_toGrothendieck]
  let B : Set (Opens Y) := {U | IsCompact (U : Set Y)}
  let Cov := fun (U : Opens Y) (T : Type u) (V : T → Opens Y) (f : ∀ t, V t ⟶ U) ↦
    Finite T ∧ IsCompact (U : Set Y) ∧ (∀ t, IsCompact (V t : Set Y)) ∧
      Presieve.ofArrows V f ∈ (Opens.pretopology Y).toPrecoverage U
  let S := fun U T V f (h : Cov U T V f) ↦
    (SiteCechComplex.exists_of_covering (Opens.pretopology Y).toPrecoverage h.2.2.2).some
  have hc := @CategoryTheory.Sheaf.isZero_H'_of_siteCech_vanishing.{u, u}
    (Opens Y) _ (Opens.pretopology Y).toPrecoverage _ _ _ _
  rw [htop] at hc
  apply hc B Cov S F
  · intro U T V f h
    exact h.2.2.2
  · intro U T V f h
    exact ⟨h.2.1, h.2.2.1,
      CategoryTheory.Sheaf.compact_cech_intersections hpairs (S U T V f h) h.2.2.1⟩
  · intro U hU T V f h
    obtain ⟨K, hK, W, g, hW, hcov, href⟩ :=
      CategoryTheory.Sheaf.compact_basis_cofinal hbasis U hU T V f h
    exact ⟨K, W, g, ⟨hK, hU, hW, hcov⟩, href⟩
  · intro U T V f h p hp
    have : Finite T := h.1
    let : Fintype T := Fintype.ofFinite T
    have hU : (⨆ t, V t) = U := by
      apply le_antisymm (iSup_le (fun t ↦ (f t).le))
      intro x hx
      obtain ⟨W, a, ha, hxW⟩ := h.2.2.2 x hx
      cases ha with
      | mk t => exact (le_iSup V t) hxW
    apply isZero_siteCech_of_surjective_unions Y F V U hU ?_ (S U T V f h) p hp
    intro A W hW hWU
    apply hres W U hWU ?_ h.2.1
    rw [hW]
    simp only [Opens.coe_iSup]
    apply isCompact_iUnion
    intro J
    exact Finset.inf'_induction J.val.property V (fun A hA B hB ↦ hpairs A B hA hB)
      (fun t _ ↦ h.2.2.1 t)

/-- Surjective restrictions between quasi-compact opens imply vanishing of positive
cohomology on every quasi-compact open subspace.

Source: Stacks Project, Cohomology of Sheaves, Tags 0A36 and 01EW, applied as in
Tag 0A3G, proof of (1) from (2); Cohomology on Sites, Tag 03F9.
(blueprint: lem-sfb-quasi-compact-restriction-acyclicity)

Proof:
1. Fix a quasi-compact open V and restrict G to V. The quasi-compact opens of X
   contained in V form a basis of V. Their finite covers, indexed by finite ordinals
   (including the empty ordinal), are cofinal among all covers of each basis open:
   refine pointwise by the basis and extract a finite subcover. This includes the
   empty open. Use the open site of def-weil-pbc-sites-and-cohomology.
2. By the intersection hypothesis every nonempty finite intersection in such a cover
   is quasi-compact. There are finitely many distinct intersections, so every union
   of these intersections is also quasi-compact, including the empty union. The
   restriction from the covered open to each such union is surjective by hres.
3. Apply lem-sfb-cech-vanishing-surjective-unions (Tag 0A36) to obtain positive
   ordered-tuple Cech vanishing for each finite cover. Tuples may have repetitions;
   their intersections are among the same finitely many intersections.
4. Apply lem-weil-pbc-site-cech-vanishing-criterion (Tag 03F9, the abelian-site form
   of 01EW): step 2 verifies intersection stability, step 1 gives cofinality, and
   step 3 gives Cech vanishing. Take the terminal open of V. By
   def-sc-topological-abelian-cohomology, its H' is the right-derived global sections
   of the ordinary restriction G|V. This gives the conclusion for every positive q
   and every quasi-compact V, including V empty. Compactness of X is never used.
-/
theorem subsingleton_H'_of_quasiCompact_restriction_surjective
    (X : Type u) [TopologicalSpace X]
    (hBasis : IsTopologicalBasis {U : Set X | IsOpen U ∧ IsCompact U})
    (hInter : ∀ (U V : Opens X), IsCompact (U : Set X) → IsCompact (V : Set X) →
      IsCompact ((U ⊓ V : Opens X) : Set X))
    (G : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
    (hres : ∀ (U V : Opens X) (hUV : U ≤ V),
      IsCompact (U : Set X) → IsCompact (V : Set X) →
      Function.Surjective (G.obj.map (homOfLE hUV).op))
    (V : Opens X) (hV : IsCompact (V : Set X)) (q : ℕ) (hq : 0 < q) :
    Subsingleton
      (@CategoryTheory.Sheaf.H'.{u, u, u}
        (Opens V) inferInstance (Opens.grothendieckTopology V) inferInstance
        (@hasExt_of_enoughInjectives _ _ _ inferInstance
          (@IsGrothendieckAbelian.enoughInjectives _ _ _
            (CategoryTheory.Sheaf.isGrothendieckAbelian_of_essentiallySmall'.{u}
              (Opens.grothendieckTopology V) AddCommGrpCat.{u})))
        ((Topology.IsOpenEmbedding.sheafPullback AddCommGrpCat.{u}
          (f := TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩)
          V.isOpenEmbedding').obj G) q ⊤) := by
  classical
  let : HasExt.{u}
      (CategoryTheory.Sheaf (Opens.grothendieckTopology V) AddCommGrpCat.{u}) :=
    @hasExt_of_enoughInjectives _ _ _ inferInstance
      (@IsGrothendieckAbelian.enoughInjectives _ _ _
        (CategoryTheory.Sheaf.isGrothendieckAbelian_of_essentiallySmall'.{u}
          (Opens.grothendieckTopology V) AddCommGrpCat.{u}))
  let i : TopCat.of V ⟶ TopCat.of X :=
    TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩
  let e : Topology.IsOpenEmbedding i := V.isOpenEmbedding'
  let R : Opens V ⥤ Opens X := e.functor
  let F := (e.sheafPullback AddCommGrpCat.{u}).obj G
  have hcompact (W : Opens V) : IsCompact (W : Set V) ↔ IsCompact (R.obj W : Set X) :=
    e.isEmbedding.isCompact_iff
  have hbasis : Opens.IsBasis {W : Opens V | IsCompact (W : Set V)} := by
    rw [Opens.isBasis_iff_nbhd]
    intro W x hx
    have hxR : x.val ∈ R.obj W := ⟨x, hx, rfl⟩
    obtain ⟨A, ⟨hAo, hAc⟩, hxA, hAW⟩ :=
      hBasis.mem_nhds_iff.mp ((R.obj W).isOpen.mem_nhds hxR)
    let B : Opens V := ⟨Subtype.val ⁻¹' A, hAo.preimage continuous_subtype_val⟩
    have hB : R.obj B = (⟨A, hAo⟩ : Opens X) := by
      apply Opens.ext
      change Subtype.val '' (Subtype.val ⁻¹' A) = A
      apply Set.image_preimage_eq_of_subset
      intro y hy
      obtain ⟨z, _, rfl⟩ := hAW hy
      exact ⟨z, rfl⟩
    refine ⟨B, (hcompact B).mpr (hB.symm ▸ hAc), hxA, ?_⟩
    intro y hy
    obtain ⟨z, hz, heq⟩ := hAW hy
    exact Subtype.val_injective heq ▸ hz
  have hpairs (A B : Opens V) (hA : IsCompact (A : Set V))
      (hB : IsCompact (B : Set V)) : IsCompact ((A ⊓ B : Opens V) : Set V) := by
    apply (hcompact _).mpr
    have heq : R.obj (A ⊓ B) = R.obj A ⊓ R.obj B := by
      apply Opens.ext
      exact Set.image_inter Subtype.val_injective
    rw [heq]
    exact hInter _ _ ((hcompact A).mp hA) ((hcompact B).mp hB)
  have hrestr (A B : Opens V) (hAB : A ≤ B) (hA : IsCompact (A : Set V))
      (hB : IsCompact (B : Set V)) :
      Function.Surjective (F.obj.map (homOfLE hAB).op) := by
    exact hres (R.obj A) (R.obj B) (R.map (homOfLE hAB)).le
      ((hcompact A).mp hA) ((hcompact B).mp hB)
  exact AddCommGrpCat.subsingleton_of_isZero
    (isZero_H'_of_compact_restrictions hbasis hpairs F hrestr ⊤
      (isCompact_iff_isCompact_univ.mp hV) q hq)

end TopCat.Sheaf
