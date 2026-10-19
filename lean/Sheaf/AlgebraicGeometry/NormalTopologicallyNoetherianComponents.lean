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
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.Topology.Sets.Closeds
import WeilConjectures.RingTheory.ReducedNormalIffIntegrallyClosedTotalFractions

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
  sorry

end AlgebraicGeometry
