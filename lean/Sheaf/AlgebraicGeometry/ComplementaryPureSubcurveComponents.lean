/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NG
-/
module

public import WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.Topology.Irreducible
public import Mathlib.Topology.KrullDimension
import WeilConjectures.Topology.IrreducibleOpenComplementDimension

/-!
# Complementary components of a reduced pure subcurve

Source: Stacks Project, Curves, Tag 0E38, first paragraph of the proof of
`lemma-closed-subscheme-nodal-curve`; Schemes, Tags 01J3 and 01J4
(blueprint: lem-trf-complementary-pure-subcurve-components).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry

-- A proper closed subspace cannot have the same dimension as an irreducible curve.
private theorem closed_embedding_surjective_dim_one
    {A B : Type*} [TopologicalSpace A] [TopologicalSpace B] [IrreducibleSpace B]
    (f : A → B) (hf : Topology.IsClosedEmbedding f)
    (hA : topologicalKrullDim A = 1) (hB : topologicalKrullDim B = 1) :
    Function.Surjective f := by
  classical
  by_contra h
  let U : Opens B := ⟨(Set.range f)ᶜ, hf.isClosed_range.isOpen_compl⟩
  have hU : U ≠ ⊥ := by
    intro he
    apply h
    apply Set.range_eq_univ.mp
    have : (Set.range f)ᶜ = ∅ := congrArg (fun V : Opens B ↦ (V : Set B)) he
    exact Set.eq_univ_of_forall fun b ↦ by
      by_contra hb
      exact Set.notMem_empty b (this ▸ hb)
  have he : topologicalKrullDim A = topologicalKrullDim ↥((U : Set B)ᶜ) := by
    have hset : (U : Set B)ᶜ = Set.range f := compl_compl _
    rw [hset]
    exact IsHomeomorph.topologicalKrullDim_eq _ hf.isEmbedding.toHomeomorph.isHomeomorph
  rcases irreducible_open_complement_dimension B 1 hB.le U hU with hempty | ⟨e, he', hd⟩
  · have : IsEmpty A := ⟨fun a ↦ hempty.false ⟨f a, by simp [U]⟩⟩
    have : topologicalKrullDim A = ⊥ := by
      apply Order.krullDim_eq_bot_iff.mpr
      exact ⟨fun C ↦ let ⟨a, _⟩ := C.2.nonempty; isEmptyElim a⟩
    rw [hA] at this
    simp at this
  · have he0 : e = 0 := by omega
    rw [he0, ← he, hA] at hd
    norm_num at hd

private theorem image_component_of_pure_dim_one
    {A B : Type*} [TopologicalSpace A] [TopologicalSpace B]
    (f : A → B) (hf : Topology.IsClosedEmbedding f)
    (hA : ∀ C ∈ irreducibleComponents A, topologicalKrullDim C = 1)
    (hB : ∀ D ∈ irreducibleComponents B, topologicalKrullDim D = 1)
    (C : Set A) (hC : C ∈ irreducibleComponents A) :
    f '' C ∈ irreducibleComponents B := by
  classical
  obtain ⟨D, hD, hCD⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible
    (f '' C) (hC.1.image f hf.continuous.continuousOn)
  let g : C → D := fun c ↦ ⟨f c, hCD (Set.mem_image_of_mem f c.2)⟩
  have hg : Topology.IsClosedEmbedding g :=
    Topology.IsClosedEmbedding.of_comp Topology.IsEmbedding.subtypeVal
      (hf.comp (isClosed_of_mem_irreducibleComponents C hC).isClosedEmbedding_subtypeVal)
  let : IrreducibleSpace D := Subtype.irreducibleSpace hD.1
  have hs := closed_embedding_surjective_dim_one g hg (hA C hC) (hB D hD)
  have heq : f '' C = D := by
    apply Set.Subset.antisymm hCD
    intro d hd
    obtain ⟨c, hc⟩ := hs ⟨d, hd⟩
    exact ⟨c, c.2, congrArg Subtype.val hc⟩
  rwa [heq]

-- Each remaining component contains its exclusive open part densely.
private theorem closure_complement_component_union
    {A : Type*} [TopologicalSpace A]
    (hfin : (irreducibleComponents A).Finite)
    {I : Set (Set A)} (hI : I ⊆ irreducibleComponents A) :
    closure (⋃₀ I)ᶜ = ⋃₀ (irreducibleComponents A \ I) := by
  classical
  have hclosed : IsClosed (⋃₀ (irreducibleComponents A \ I)) := by
    rw [Set.sUnion_eq_biUnion]
    exact hfin.sdiff.isClosed_biUnion fun C hC ↦
      isClosed_of_mem_irreducibleComponents C hC.1
  apply Set.Subset.antisymm
  · apply closure_minimal _ hclosed
    intro a ha
    have hc := irreducibleComponent_mem_irreducibleComponents a
    refine Set.mem_sUnion_of_mem mem_irreducibleComponent ⟨hc, ?_⟩
    intro hi
    exact ha (Set.mem_sUnion_of_mem mem_irreducibleComponent hi)
  · rintro a ⟨C, ⟨hC, hn⟩, ha⟩
    rw [← closure_sUnion_irreducibleComponents_sdiff_singleton hfin C hC] at ha
    apply closure_mono _ ha
    apply Set.compl_subset_compl.mpr
    apply Set.sUnion_mono
    intro D hD
    exact ⟨hI hD, fun he ↦ hn (he ▸ hD)⟩

-- An embedding onto a finite union of components preserves those components.
private theorem component_image_of_union
    {A B : Type*} [TopologicalSpace A] [TopologicalSpace B]
    (f : A → B) (hf : Topology.IsEmbedding f)
    {J : Set (Set B)} (hfin : J.Finite) (hJ : J ⊆ irreducibleComponents B)
    (hrange : Set.range f = ⋃₀ J)
    {C : Set A} (hC : C ∈ irreducibleComponents A) :
    ∃ D ∈ J, f '' C = D := by
  classical
  have hc : f '' C ⊆ ⋃₀ J := hrange ▸ Set.image_subset_range f C
  obtain ⟨D, hD, hCD⟩ := isIrreducible_iff_sUnion_isClosed.mp
    (hC.1.image f hf.continuous.continuousOn) hfin.toFinset
    (fun D hD ↦ isClosed_of_mem_irreducibleComponents D (hJ (hfin.mem_toFinset.mp hD)))
    (hfin.coe_toFinset.symm ▸ hc)
  have hD' : D ∈ J := hfin.mem_toFinset.mp hD
  have hDr : D ⊆ Set.range f := by
    rw [hrange]
    exact Set.subset_sUnion_of_mem hD'
  let e := hf.homeomorphOfSubsetRange hDr
  have hirr : IsIrreducible (f ⁻¹' D) := by
    let : IrreducibleSpace D := Subtype.irreducibleSpace (hJ hD').1
    let : IrreducibleSpace (f ⁻¹' D) := e.irreducibleSpace_iff.mpr inferInstance
    exact IsIrreducible.of_subtype
  have hpre : f ⁻¹' D ⊆ C := hC.2 hirr (fun c hc ↦ hCD ⟨c, hc, rfl⟩)
  refine ⟨D, hD', Set.Subset.antisymm hCD ?_⟩
  rw [← Set.image_preimage_eq_of_subset hDr]
  exact Set.image_mono hpre

/-- A reduced pure one-dimensional closed subcurve is a union of components, and its
complementary reduced closure consists of the remaining components. Taking the complementary
reduced closure twice recovers the subcurve as a closed subscheme of the ambient scheme.
Source: Stacks Project, Curves, Tag 0E38, first proof paragraph; Schemes, Tags 01J3 and 01J4
(blueprint: lem-trf-complementary-pure-subcurve-components).

Here `j` represents the reduced induced structure on the complementary closure: it is a
reduced closed immersion with that image, hence is the unique such closed subscheme by
`Scheme.IdealSheafData.reduced_induced_closed_subscheme`. For the same reason, the two range
identities express equality with the reduced closed unions, including their scheme structures.
The set `irreducibleComponents X` is finite by
`finite_irreducibleComponents_of_isNoetherian`.

Proof plan, following the six steps of the node:
1. Noetherianity gives finitely many components
   (lem-weil-pbc-noetherian-finitely-many-components). If X is empty, all schemes are empty.
   Every point belongs to a component (lem-sc-irreducible-components-cover).
2. Each component C of Y is a closed irreducible subset of a component D of X. If C is
   proper in D, new-node-irreducible-open-complement-dimension applied to D minus C bounds
   its dimension by zero, contradicting the dimension-one hypothesis. Thus C equals D.
3. Take I to be the components of X arising from Y. Component coverage gives range i equal
   to their union; reduced-induced uniqueness identifies the scheme structure
   (lem-weil-pbc-reduced-induced-closed-subscheme).
4. The union W of the remaining components is closed. It contains X minus range i.
   Conversely the generic point of each remaining component lies outside range i:
   otherwise irreducibility and the finite closed cover force that component into a
   selected component, contradicting maximality. Its closure is therefore in the closure
   of X minus range i. This proves W equals range j, using lem-sc-scheme-sober.
5. The maximal irreducible subsets of W are exactly the remaining components: a finite
   closed cover contains any irreducible subset in one member, and distinct components
   do not contain one another. Hence all components of Z have dimension one; reducedness
   supplies the asserted reduced union (lem-weil-pbc-reduced-induced-closed-subscheme).
6. X minus W lies in range i. Each selected component has its generic point outside W,
   since otherwise it would equal a remaining component. Thus the closure of X minus W
   is range i. Reduced-induced uniqueness gives the displayed isomorphism over X.
   The same argument includes I empty and I equal to the entire component set. -/
theorem complementary_pure_subcurve_components
    {X Y Z : Scheme.{u}} [IsReduced X] [IsNoetherian X]
    (hX : ∀ C ∈ irreducibleComponents X, topologicalKrullDim C = 1)
    (i : Y ⟶ X) [IsClosedImmersion i] [IsReduced Y]
    (hY : ∀ C ∈ irreducibleComponents Y, topologicalKrullDim C = 1)
    (j : Z ⟶ X) [IsClosedImmersion j] [IsReduced Z]
    (hZ : Set.range j = closure ((Set.range i)ᶜ)) :
    ∃ I : Set (Set X), I ⊆ irreducibleComponents X ∧
      Set.range i = ⋃₀ I ∧
      Set.range j = ⋃₀ (irreducibleComponents X \ I) ∧
      (∀ C ∈ irreducibleComponents Z, topologicalKrullDim C = 1) ∧
      ∃ e : Y ≅
          (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ((Set.range j)ᶜ))).subscheme,
        e.hom ≫
          (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ((Set.range j)ᶜ))).subschemeι =
            i := by
  classical
  let I : Set (Set X) := (fun C : Set Y ↦ i '' C) '' irreducibleComponents Y
  have hI : I ⊆ irreducibleComponents X := by
    rintro _ ⟨C, hC, rfl⟩
    exact image_component_of_pure_dim_one i i.isClosedEmbedding hY hX C hC
  have hi : Set.range i = ⋃₀ I := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact Set.mem_sUnion_of_mem (Set.mem_image_of_mem i mem_irreducibleComponent)
        ⟨irreducibleComponent y, irreducibleComponent_mem_irreducibleComponents y, rfl⟩
    · rintro ⟨C, ⟨D, hD, rfl⟩, y, hy, rfl⟩
      exact Set.mem_range_self y
  have hfin := finite_irreducibleComponents_of_isNoetherian (X := X)
  have hj : Set.range j = ⋃₀ (irreducibleComponents X \ I) := by
    rw [hZ, hi]
    exact closure_complement_component_union hfin hI
  have hdim : ∀ C ∈ irreducibleComponents Z, topologicalKrullDim C = 1 := by
    intro C hC
    obtain ⟨D, hD, heq⟩ := component_image_of_union j j.isClosedEmbedding.isEmbedding
      hfin.sdiff Set.sdiff_subset hj hC
    have he := IsHomeomorph.topologicalKrullDim_eq _
      (j.isClosedEmbedding.isEmbedding.homeomorphImage C).isHomeomorph
    exact he.trans (heq ▸ hX D hD.1)
  have hdouble : closure (Set.range j)ᶜ = Set.range i := by
    rw [hj, closure_complement_component_union hfin Set.sdiff_subset,
      Set.sdiff_sdiff_cancel_left hI, ← hi]
  refine ⟨I, hI, hi, hj, hdim, ?_⟩
  have hu := (Scheme.IdealSheafData.reduced_induced_closed_subscheme X
    (Closeds.closure ((Set.range j)ᶜ))).2.2.2.2.2.2.2 Y i
    (by exact hdouble.symm)
  obtain ⟨e, he, -⟩ := hu.2
  exact ⟨e, he⟩

end AlgebraicGeometry
