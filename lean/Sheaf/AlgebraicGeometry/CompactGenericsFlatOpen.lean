module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.Topology.Sober

import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.RingTheory.KrullDimension.Zero
import WeilConjectures.AlgebraicGeometry.SpecStalkLimitAffineNeighbourhoods
import WeilConjectures.AlgebraicGeometry.DescendFlatFinitePresentation

/-! # A flat open neighbourhood of a compact generic-point subspace

Source: David Rydh, Submersions and effective descent of étale morphisms,
Lemma (3.5), printed page 12, including the generic-point containment in its proof
(blueprint: lem-sfb-compact-generics-flat-open).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- A finitely presented morphism over a reduced qcqs scheme whose component generic points
form a quasi-compact subspace is flat over a quasi-compact dense open containing them all.
No Noetherianity, irreducibility or nonemptiness hypothesis is imposed.

Source: Rydh, Submersions and effective descent of étale morphisms,
Lemma (3.5), printed page 12, and its proof
(blueprint: lem-sfb-compact-generics-flat-open).

Proof plan:
1. At a component generic point η, choose an affine neighbourhood W₀ = Spec R by
   lem-weil-pbc-affine-opens-basis. The component through η intersects W₀ in an irreducible
   component: maximality follows by taking closures in C. Thus η corresponds to a minimal
   prime of R by lem-weil-pbc-spec-irreducible-components-minimal-primes. Reducedness of C
   makes R reduced (def-pc-reduced-scheme), so lem-weil-pbc-minimal-prime-reduced-localization-field
   makes its localization a field. The stalk is that localization by
   lem-weil-pbc-affine-open-stalk-localization.
2. Apply lem-weil-pbc-local-ring-spec-limit-affine-neighbourhoods inside W₀ at η.
   The affine neighbourhoods form a nonempty directed inverse system with affine transitions,
   qcqs stages and limit Spec O_{C,η}, with distinguished initial stage W₀.
   By lem-weil-pbc-qcqs-morphism-permanence, X₀ = h⁻¹(W₀) and W₀ are qcqs and the restricted
   map is finitely presented. Its base change to the field spectrum is flat by lem-pc-flat-field.
3. Apply lem-weil-pbc-descend-flat-finite-presentation with S₀ = Y₀ = W₀ to obtain an affine
   neighbourhood Wη of η on which h is flat. Base change along its open inclusion is exactly
   restriction to the inverse-image open subscheme.
4. The Wη cover the generic-point subspace. Its quasi-compactness gives a finite subcover.
   Their union U is open and quasi-compact, since each affine Wη is quasi-compact by
   lem-weil-pbc-affine-scheme-qcqs. It contains every component generic point. The local rings
   of restrictions to opens are the ambient local rings, so flatness on the Wη gives flatness
   over U by def-weil-flat-morphism. For an empty generic-point set take the empty union.
5. Every point of C lies in an irreducible component by lem-sc-irreducible-components-cover.
   By lem-sc-scheme-sober this component is the closure of its generic point, which belongs
   to U. Thus every point is in the closure of U. If the generic-point set is empty, C is
   empty as well, and the empty open has all the required properties.
-/
theorem exists_compact_dense_open_flat_of_compact_genericPoints
    {C Z : Scheme.{u}} [IsReduced C] [CompactSpace C] [QuasiSeparatedSpace C]
    [CompactSpace (genericPoints C)] (h : Z ⟶ C)
    [LocallyOfFinitePresentation h] [QuasiCompact h] [QuasiSeparated h] :
    ∃ U : C.Opens, IsCompact (U : Set C) ∧ genericPoints C ⊆ (U : Set C) ∧
      Dense (U : Set C) ∧ Flat (h ∣_ U) := by
  sorry

end AlgebraicGeometry
