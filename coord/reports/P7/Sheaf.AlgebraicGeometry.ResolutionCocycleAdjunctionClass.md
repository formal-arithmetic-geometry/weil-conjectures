## What changed

`Sheaf.AlgebraicGeometry.ResolutionCocycleAdjunctionClass` keeps its public statement and
public import. Its proof constructs the ordinary termwise adjunct and proves that its
localization followed by the right-derived unit is the derived adjunct. It uses the proved
single-object unit calculation in `Sheaf.CategoryTheory.DerivedAdjunctionSingleZero` through
a private proof import. A proof visibility import of `Mathlib.Logic.Small.Defs` keeps the
localization calculation within the compile budget. It then applies homology, transports
the single-object homology
comparison, substitutes the shifted-unit comparison, and evaluates the resulting equality
at the identity generator.

Two independent calculations are stated in new modules:
`ResolutionSectionCocycleSheafification` and `ResolutionShiftedUnitHomology`.
Two further modules construct the actual data used in their statements:
`Sheaf.CategoryTheory.OrdinaryComplexAdjunct` defines the three-map ordinary adjunct, and
`Sheaf.AlgebraicGeometry.ResolutionCocycleHomologyTail` defines the four-map shift and inverse
resolution comparison. Both definitions are explicit composites with zero holes. Their
irreducible interfaces retain declared sources and targets during homology calculations.
The ordinary-adjunct formula is a proved private API lemma used by the main proof.
All source-library declarations and existing definitions remain unchanged.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.Etale.resolutionCocycle_adjunction_class` by decomposition. Its combining
proof is complete Lean. The generic localization, single-object homology, and ordinary versus
derived adjunct identities are proved in the item module. No hole remains there or in either
new construction module. All five modules compile cleanly with `lcompile.py --all`; the
main module takes 43.7 seconds.

Added two holes, each in its own module:

- `AlgebraicGeometry.Etale.resolution_section_cocycle_sheafification`, node
  `lem-weil-pbc-resolution-section-cocycle-sheafification`.
- `AlgebraicGeometry.Etale.resolution_shifted_unit_homology`, node
  `lem-weil-pbc-resolution-shifted-unit-homology`.

This is a decomposition: one upper hole closed and two lower holes added. The first new
statement contains no derived adjunction or shifted augmentation. It computes the ordinary
section class and postcomposes with the prescribed inverse resolution comparisons. The
second contains no chart, generator, chain map, or sheafification. Neither is the original
statement under another name. The combining proof establishes the missing relation between
the actual derived adjunct and the ordinary chain-level adjunct. For q=0, zero maps and
empty charts, the same functorial identities apply; no cancellation of noninvertible maps
or arbitrary choice of data is used.

## No longer needed

No existing Lean import or module is removed. The main proof does not need the full derived
adjunction shift-compatibility theorem
`lem-weil-pbc-derived-adjunction-commshift` or its module
`WeilConjectures.AlgebraicGeometry.DerivedAdjunctionCommShift`: it moves the augmentation by
ordinary naturality and uses the separate right-derived-unit homology comparison. This
removes a dependency of this node, not the source module or any of its declarations.
All normalization-data, chain-cocycle, and derived-adjunction dependencies remain necessary.
No unit route is bypassed.

## Where the brief, the DAG or earlier work was wrong

The previous one-step prose proof omitted explicit declarations for the independent
section/sheafification and shifted-unit calculations. The generic unit and localization
homology identities supply the relation between ordinary and derived adjuncts; they do not
directly state either remaining normalization identity. Searches in Mathlib and the source
library preceded the new statements. No statement was found false, and no existing signature
or definition is changed. The additional instance and irreducibility attributes in the main
module are local proof settings; they do not change its exported interface. The initial
preflight found attributes and modifiers included in the two definition-node signatures;
those records now start at the `def` keyword, as required by the signature format.

The concrete comparison benefits from declared interfaces for the complex adjunct and the
shifted homology composite. The two new definitions provide those interfaces using the
existing maps. Generic private lemmas carry out the localization, homology, associativity and
evaluation arguments before specializing to sheaves.

## New nodes

`def-weil-pbc-ordinary-complex-adjunct` is the directly constructed single of the unit,
inverse single-functor comparison, and image of the chain map. Its formula API is proved.
It adds no hole.

`def-weil-pbc-resolution-cocycle-homology-tail` is the directly constructed homology of the
termwise shift map, the homology shift, and the two inverse classical resolution comparisons.
Its declared source uses the specified shifted resolution. It adds no hole.

`lem-weil-pbc-resolution-section-cocycle-sheafification` is the ordinary adjunct/sections
calculation followed by exact sheafification, its counit, and the prescribed inverse
resolution comparisons. Its docstring gives the cycles-projection and triangle-identity
proof, with source Tag 072W.

`lem-weil-pbc-resolution-shifted-unit-homology` compares the right-derived unit on I[q], the
shifted augmentation, and the prescribed shifted resolution homology composite. Its docstring
gives unshifted resolution transport followed by unit, quotient and homology shift
compatibility, with sources Tags 072W and 0DVC.

No change record is required: existing signatures and definitions are unchanged.

## Second reading by P7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
