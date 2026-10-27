/-
Copyright (c) 2026 NJ. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NJ
-/

module

public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme
import Mathlib.AlgebraicGeometry.Gluing
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.Topology.Sets.Closeds
import WeilConjectures.RingTheory.ReducedNormalIffIntegrallyClosedTotalFractions

/-!
# Normal schemes with locally finitely many irreducible components

Source: Stacks Project, Properties, Tag 0357, implication (1) to (2), and Schemes,
Tags 01J3 and 01J4 for the reduced induced structure
(blueprint: lem-sfb-normal-locally-finite-components).

The index type is the actual set of irreducible components. It need not be finite
or inhabited. The open subschemes are identified over the ambient scheme with
the canonical reduced induced closed subschemes.
-/

@[expose] public section

universe u

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- A normal scheme with locally finitely many irreducible components is their
clopen disjoint union, with coinciding open and reduced induced closed structures.
Source: Stacks Project, Properties, Tag 0357, and Schemes, Tags 01J3 and 01J4
(blueprint: lem-sfb-normal-locally-finite-components).

Proof (the eight steps of the node):
1. Choose an affine open cover (lem-weil-pbc-affine-opens-basis). Its members are
   quasi-compact (lem-weil-pbc-affine-scheme-qcqs), so have finitely many components.
   By lem-weil-pbc-spec-irreducible-components-minimal-primes, their rings have finitely
   many minimal primes. Domain stalks imply reducedness (def-pc-reduced-scheme), and
   lem-weil-pbc-affine-open-stalk-localization identifies their prime localizations
   with the given normal domain stalks (def-weil-pbc-normal-ring).
2. Apply lem-weil-pbc-reduced-normal-iff-integrally-closed-total-fractions to each
   affine ring: it is a finite product of normal domains, allowing the empty product.
3. For the coordinate idempotents e_a, every prime omits exactly one e_a. Thus the
   kernels of the projections are exactly the minimal primes, and their zero loci
   are D(e_a). The affine components are consequently disjoint and clopen
   (lem-weil-pbc-spec-irreducible-components-minimal-primes, def-weil-affine-spectrum).
4. By lem-weil-pbc-open-subspace-irreducible-closed-correspondence, intersecting with
   an open and taking closure are inverse on components meeting that open. For the
   converse, put the closure inside a component using lem-sc-irreducible-components-cover
   and apply maximality (def-weil-irreducible-components).
5. A global component therefore has clopen trace on each affine of the cover, so is
   open and closed. Two components meeting at a point have the same trace on an affine
   neighbourhood and hence the same closure. Components cover by
   lem-sc-irreducible-components-cover; they form a set of subsets of X.
6. The open structure on a component has the ambient stalks (def-weil-open-immersion),
   so its stalks are normal domains. It is reduced and nonempty irreducible, hence
   integral (def-pc-reduced-scheme, def-weil-irreducible-components,
   def-pc-integral-scheme).
7. A clopen inclusion is also a closed immersion: extend sections by zero on its
   open complement (def-weil-closed-immersion). The uniqueness clause of
   lem-weil-pbc-reduced-induced-closed-subscheme identifies the two structures over X.
8. Form the coproduct (lem-weil-pbc-scheme-coproduct-family). Glue its injections
   along the disjoint open cover to obtain the inverse of the canonical map
   (lem-weil-pbc-scheme-morphism-gluing). The two composites are identities by open
   gluing uniqueness and the coproduct universal property. The empty scheme has no
   irreducible components and gives the empty coproduct. No finiteness of the global
   component set, local Noetherianity, or global quasi-compactness is used. -/
theorem normal_locally_finite_components (X : Scheme.{u})
    (hfinite : ∀ U : X.Opens, CompactSpace U → (irreducibleComponents U).Finite)
    (hnormal : ∀ x : X,
      IsDomain (X.presheaf.stalk x) ∧ IsIntegrallyClosed (X.presheaf.stalk x)) :
    ∃ U : irreducibleComponents X → X.Opens,
      (∀ i, (U i : Set X) = i.val) ∧
      (∀ i, IsClopen (U i : Set X)) ∧
      Pairwise (fun i j ↦ Disjoint (U i) (U j)) ∧
      (⨆ i, U i) = ⊤ ∧
      (∀ i, IsIntegral (U i).toScheme ∧
        ∀ x : (U i).toScheme,
          IsDomain ((U i).toScheme.presheaf.stalk x) ∧
            IsIntegrallyClosed ((U i).toScheme.presheaf.stalk x)) ∧
      (∀ i, ∃ e : (U i).toScheme ≅
          (IdealSheafData.vanishingIdeal
            ⟨i.val, isClosed_of_mem_irreducibleComponents i.val i.property⟩).subscheme,
        e.hom ≫ (IdealSheafData.vanishingIdeal
          ⟨i.val, isClosed_of_mem_irreducibleComponents i.val i.property⟩).subschemeι =
            (U i).ι) ∧
      IsIso (Sigma.desc (fun i ↦ (U i).ι)) := by
  sorry

end AlgebraicGeometry.Scheme
