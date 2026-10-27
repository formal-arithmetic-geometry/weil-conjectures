## What changed

Proved all three theorems in `Sheaf.Topology.SubspaceRingRestrictionUnitCoherence`.
Private helpers establish the exact open-embedding unit formula, naturality of the
section map, a homeomorphism equivalence on sheaves, and the common coefficient-category
argument specialized to rings and sets. The homeomorphism comparison is the inverse
mate of the commuting direct-image square, composed with the pullback of theta.

Added private proof imports of `WeilConjectures.CategoryTheory.InverseMateEquivalence`
and `WeilConjectures.Mathlib.CategoryTheory.Sites.Pullback`. Updated the item's existing
DAG proof, dependencies and origin to this route. The import/command change is recorded in
`coord/changes/D8-subspace-restriction-proof-imports.md`. The downstream consumer
check found zero importers and requires no adaptations. Existing public declaration
signatures and definitions are unchanged; no other module is adapted. The unit route is preserved.

## Proved and sorry left

Closed the three original holes:

- `TopCat.Sheaf.subspace_ring_restriction_unit_coherence`.
- `TopCat.Sheaf.subspace_sets_restriction_unit_coherence`.
- `TopCat.Sheaf.subspace_ring_homeomorphism_unit_coherence`.

Zero holes remain and zero are added or split off. All private helpers are proved.
The file compiles through the required server compiler after import pruning.
`#print axioms` for each of the three theorems reports exactly `propext`,
`Classical.choice`, and `Quot.sound`. The two original statements bind an unused lambda variable; the unused-variable
linter is disabled only for those declarations to preserve their signatures verbatim.
All ten existing public declaration signatures were compared against the source and are unchanged. The argument handles empty
subspaces and opens without any nonemptiness assumption or choice of sections.

## No longer needed

Removed `Sheaf.Topology.SetsInverseImageComposition`: the set case is a specialization
of the common coefficient-category proof. Its unit characterization agrees with the
canonical set comparison, so no application of `exists_sets_inverseImage_comp` is needed.
Removed `lem-weil-pbc-sets-inverse-image-composition` from proof-step uses and proof_deps,
and withdrew its obsolete top-level tool_uses entry. Its statement dependency is retained,
as the unchanged mathematical statement mentions the canonical comparison. The module
is still used elsewhere and is not withdrawn.

Removed redundant private imports `Mathlib.CategoryTheory.Adjunction.Mates`,
`Mathlib.CategoryTheory.Adjunction.Basic`, `Mathlib.CategoryTheory.Sites.Sheafification`
and `Mathlib.CategoryTheory.Limits.HasLimits`; their used declarations are already
available through the imports needed by this proof. No modules or declarations are deleted.
No other declared dependencies are pruned.

## Where the brief, the DAG or earlier work was wrong

No statement or definition was wrong. The plan's informal identification of opens
under an open inclusion requires the opens-adjunction unit and counit in the formal
unit calculation. The proof uses their naturality and triangle identity explicitly.
The homeomorphism argument is implemented using the existing proved inverse-mate
isomorphism theorem rather than rebuilding a transported adjunction. The original
set-composition proof dependency is unnecessary for the generic argument.

## Second reading by D8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
