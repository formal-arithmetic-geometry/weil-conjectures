/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NH
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.Topology.Irreducible
public import Mathlib.Topology.NoetherianSpace
import Mathlib.AlgebraicGeometry.Stalk
import Mathlib.AlgebraicGeometry.OpenImmersion

/-!
# Components of a normal, topologically Noetherian scheme

Source: Stacks Project, Properties, Tag 0357, lemma-normal-locally-finite-nr-irreducibles;
Topology, Tag 0052, lemma-Noetherian
(blueprint: lem-trf-normal-topologically-noetherian-components).
-/

@[expose] public section

universe u

namespace AlgebraicGeometry

/-- A normal scheme with Noetherian underlying space has finitely many pairwise disjoint
clopen irreducible components, and their open subschemes are normal and integral.
No Noetherian hypothesis on rings is imposed, and the empty scheme is allowed.
Source: Stacks Project, Properties, Tag 0357; Topology, Tag 0052
(blueprint: lem-trf-normal-topologically-noetherian-components).

Proof:
1. Every open subspace is Noetherian: lift a descending chain of relatively closed
   subsets to finite intersections of closed subsets of the ambient space and apply DCC.
2. By lem-sc-noetherian-finite-irreducible-components, the ambient space and each affine
   open have finitely many components. Present an affine open as Spec of its section ring
   by lem-weil-pbc-affine-open-spec-points. The correspondence in
   lem-weil-pbc-spec-irreducible-components-minimal-primes gives finitely many minimal
   primes; distinct minimal primes have distinct vanishing sets.
3. Domain stalks are reduced, so def-pc-reduced-scheme gives reduced section rings.
   By lem-weil-pbc-affine-open-stalk-localization, the prime localizations of an affine
   section ring are precisely the ambient stalks. Thus this ring is normal in the sense
   of def-weil-pbc-normal-ring.
4. Apply lem-weil-pbc-reduced-normal-iff-integrally-closed-total-fractions, Tag 030C:
   a reduced normal ring with finitely many minimal primes is a finite product of normal
   domains. The zero ring is the empty product.
5. For this product, its coordinate idempotents sum to one and are orthogonal. Every
   prime omits exactly one idempotent and contains the corresponding projection kernel.
   Those kernels are exactly the minimal primes. Their vanishing sets equal the basic
   opens of the idempotents (def-weil-affine-spectrum), so the affine components are
   pairwise disjoint and clopen, and cover the affine open. This includes the empty product.
6. By lem-weil-pbc-open-subspace-irreducible-closed-correspondence, intersection with an
   open and closure are inverse order bijections on irreducible closed subsets meeting
   that open. Maximality identifies the ambient components meeting it with its components.
7. Intersect an ambient component with each affine open. Each intersection is empty or
   an open affine component, so the component is open; it is closed by
   def-weil-irreducible-components. Distinct components cannot meet, since their traces
   in an affine neighbourhood would coincide and taking closures would identify them.
   Every point lies on an affine component and hence on its ambient closure.
8. On each component, take the open subscheme structure of def-weil-open-immersion.
   Restricting the structure sheaf preserves its stalks, so this subscheme is normal
   and reduced. It is nonempty and irreducible by def-weil-irreducible-components, hence
   integral by def-pc-integral-scheme. The empty scheme has no irreducible components. -/
theorem normal_topologicallyNoetherian_components
    (Z : Scheme.{u}) [TopologicalSpace.NoetherianSpace Z]
    (hnormal : ∀ z : Z, IsDomain (Z.presheaf.stalk z) ∧
      IsIntegrallyClosed (Z.presheaf.stalk z)) :
    (irreducibleComponents Z).Finite ∧
    (irreducibleComponents Z).Pairwise Disjoint ∧
    ∀ C ∈ irreducibleComponents Z, ∃ hC : IsOpen C,
      IsClosed C ∧ IsIntegral (Scheme.Opens.toScheme (⟨C, hC⟩ : Z.Opens)) ∧
      ∀ z : (Scheme.Opens.toScheme (⟨C, hC⟩ : Z.Opens)),
        IsDomain ((Scheme.Opens.toScheme (⟨C, hC⟩ : Z.Opens)).presheaf.stalk z) ∧
        IsIntegrallyClosed ((Scheme.Opens.toScheme (⟨C, hC⟩ : Z.Opens)).presheaf.stalk z) := by
  classical
  have hfinite : (irreducibleComponents Z).Finite :=
    TopologicalSpace.NoetherianSpace.finite_irreducibleComponents
  -- Every component through x is the closure of the generizations of x.
  have hcomponent (x : Z) (C : Set Z) (hC : C ∈ irreducibleComponents Z) (hx : x ∈ C) :
      C = closure {y : Z | y ⤳ x} := by
    let : IsDomain (Z.presheaf.stalk x) := (hnormal x).1
    have hS : IsIrreducible {y : Z | y ⤳ x} := by
      rw [← Z.range_fromSpecStalk, ← Set.image_univ]
      exact (IrreducibleSpace.isIrreducible_univ _).image _
        (Z.fromSpecStalk x).continuous.continuousOn
    obtain ⟨η, hη⟩ := QuasiSober.sober hC.1 (isClosed_of_mem_irreducibleComponents _ hC)
    have hCS : C ⊆ closure {y : Z | y ⤳ x} :=
      hη.symm.trans_subset (closure_mono (Set.singleton_subset_iff.mpr (hη.specializes hx)))
    exact hCS.antisymm (hC.2 hS.closure hCS)
  have hdisjoint : (irreducibleComponents Z).Pairwise Disjoint := by
    intro C hC D hD hne
    apply Set.disjoint_left.mpr
    intro x hxC hxD
    exact hne ((hcomponent x C hC hxC).trans (hcomponent x D hD hxD).symm)
  refine ⟨hfinite, hdisjoint, ?_⟩
  intro C hC
  have hclosed := isClosed_of_mem_irreducibleComponents C hC
  have hopen : IsOpen C := by
    have hcompl : C = (⋃₀ (irreducibleComponents Z \ {C}))ᶜ := by
      ext x
      constructor
      · intro hx hothers
        obtain ⟨D, hD, hxD⟩ := hothers
        exact Set.disjoint_left.mp (hdisjoint hC hD.1
          (fun h ↦ hD.2 (Set.mem_singleton_iff.mpr h.symm))) hx hxD
      · intro hx
        by_contra hxC
        apply hx
        refine ⟨irreducibleComponent x, ⟨irreducibleComponent_mem_irreducibleComponents x,
          ?_⟩, mem_irreducibleComponent⟩
        intro heq
        exact hxC ((Set.mem_singleton_iff.mp heq) ▸ mem_irreducibleComponent)
    rw [hcompl]
    simpa only [Set.sUnion_eq_biUnion] using
      ((hfinite.sdiff (t := {C})).isClosed_biUnion
        fun D hD ↦ isClosed_of_mem_irreducibleComponents D hD.1).isOpen_compl
  let U : Z.Opens := ⟨C, hopen⟩
  have hnormalU (z : U.toScheme) : IsDomain (U.toScheme.presheaf.stalk z) ∧
      IsIntegrallyClosed (U.toScheme.presheaf.stalk z) := by
    obtain ⟨hd, hi⟩ := hnormal (U.ι z)
    let : IsDomain (Z.presheaf.stalk (U.ι z)) := hd
    let : IsIntegrallyClosed (Z.presheaf.stalk (U.ι z)) := hi
    let e := (CategoryTheory.asIso (U.ι.stalkMap z)).commRingCatIsoToRingEquiv
    exact ⟨e.symm.toMulEquiv.isDomain, IsIntegrallyClosed.of_equiv e⟩
  let (z : U.toScheme) : IsDomain (U.toScheme.presheaf.stalk z) := (hnormalU z).1
  let : IsReduced U.toScheme := isReduced_of_isReduced_stalk _
  let : IrreducibleSpace U.toScheme := isIrreducible_iff_irreducibleSpace.mp hC.1
  exact ⟨hopen, hclosed, isIntegral_of_irreducibleSpace_of_isReduced _, hnormalU⟩

end AlgebraicGeometry
