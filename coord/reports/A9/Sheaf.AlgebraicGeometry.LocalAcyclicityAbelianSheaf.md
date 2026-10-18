## What changed

Proved `AlgebraicGeometry.Etale.existsUnique_localAcyclicityStrictMap` in
`Sheaf.AlgebraicGeometry.LocalAcyclicityAbelianSheaf`. Canonical residue structures
and the existing `strictHenselizationFunctoriality` give existence. The limit
property identifies its residue lift with the explicit evaluation map; étale
pointed-map rigidity and limit extensionality prove uniqueness for arbitrary
scheme morphisms satisfying the two equations.

Added proof imports of `Sheaf.Paper.StrictHenselizationPointEvaluationPointed`
and `WeilConjectures.AlgebraicGeometry.EtalePointedMapRigidity`. Updated the
existing node's proof, proof dependencies and proof origin to record this argument.
No declaration signature, visibility, definition body or target changed.
The item is not itself a realized unit statement or proof step; the unit route stays.

Validation: the original proof compiled, then the final proof compiled without
warnings after removing unused imports and fixing local-instance style. All
compilations used `lcompile.py`, within the single-file time limit.

## Proved and sorry left

Closed 1 of 1 holes:
`AlgebraicGeometry.Etale.existsUnique_localAcyclicityStrictMap`
(node `def-weil-pbc-local-acyclicity-abelian-sheaf`).

Remaining holes in the item: none. Added holes: none. Split off: none.
Existing imported theorems are used as stated; this delivery does not claim to
close holes in their transitive dependencies.

## No longer needed

Removed the unused proof imports:

- `WeilConjectures.AlgebraicGeometry.InverseImageStalkGerm`.
- `WeilConjectures.AlgebraicGeometry.StrictlyHenselianSectionsStalk`.

The unique-map argument needs neither `inverseImage_stalk_germ` nor
`strictlyHenselianSections_geometricStalk_isIso`. Their nodes
`lem-weil-pbc-inverse-image-stalk-germ` and
`lem-weil-pbc-strictly-henselian-sections-stalk` remain statement dependencies
of the local-acyclicity definition's mathematical interpretation; no global
unreachability is claimed. No other planned proof dependencies were discarded:
the existing node had an empty proof and proof-dependency list.

## Where the brief, the DAG or earlier work was wrong

The definition node had no numbered proof steps, although the module contained
one unique-existence theorem with a documented proof. The existing functoriality
statement suffices; no new statement or definition repair was necessary.

## Second reading by A9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
