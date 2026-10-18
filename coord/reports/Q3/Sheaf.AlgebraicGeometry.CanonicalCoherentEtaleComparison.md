## What changed

Repaired reviewer C-3269d's H9 return at head 3269d5537: deleted the unused
`import Mathlib.CategoryTheory.Sites.LocallyInjective` from
`Sheaf.AlgebraicGeometry.CoherentEtaleEffacingSequence`, with no replacement.
No declaration, signature, definition, proof or DAG route changes in this repair.
The retained sandbox differs from current library sources by the original
comparison construction and its support modules, which remain part of this delivery.

Repaired the return at b134590b6: added
`Sheaf.AlgebraicGeometry.PrimeCurveArtinSchreierKernel` to `## Users` in
`coord/changes/Q3-canonical-coherent-etale-cached-groups.md`. Its two uses of
`AlgebraicGeometry.Scheme.Modules.liftedCoherentEtaleSheaf` still denote the
identical lifted tensor-section sheaf, including the ULift component formula.
Refreshed the full consumer audit against current sources: 17 transitive
importers, nine direct importers. Added the current comparison-pullback consumer
and every transitive importer, and removed the obsolete raw-direct-image row.
No consumer source or target signature is changed by this repair.

The retained delivery caches the concrete cohomology groups, proves simultaneous
effacement and dimension shifting, and reduces the normalized-comparison theorem
to construction of a normalized additive map. Its previous duplicate-helper
repair is preserved: the proof uses the existing public terminal-hom isomorphism
and proves the tensor-section isomorphism locally. All four delivery modules
compile. All nine direct consumers compile unchanged against these modules,
including `PrimeCurveArtinSchreierKernel` (7.3 seconds). Every direct consumer
check finished within the 60-second file limit, with no errors or warnings.
The retained normalization interface check also compiles, proving definitional
equivalence with the original three-clause normalization formula. The delivery
dry run passes and classifies the set as CODEX for independent review.

## Proved and sorry left

The item originally had one hole:
`AlgebraicGeometry.Scheme.Modules.exists_unique_normalizedCoherentEtaleComparison`.
Its proof is complete from the declared support theorems; the item now has zero
`sorry`. The retained delivery adds one hole, and only one:
`AlgebraicGeometry.Scheme.Modules.CoherentEtale.exists_normalized_map`, in
`Sheaf.AlgebraicGeometry.CoherentEtaleComparisonMorphismExists`, node
`lem-pbc-coherent-etale-normalized-additive-map`. Thus the original reduction is
a decomposition (one hole closed, one added; net zero), not a completed proof of
all its dependencies. This repair introduces no further holes.

The support modules `CoherentEtaleComparisonMorphism` and
`CoherentEtaleEffacingSequence` contain zero holes. In particular,
`CoherentEtale.normalized_unique`, `CoherentEtale.normalized_bijective`,
`CoherentEtale.normalized_zero_bijective`, and
`CoherentEtale.exists_effacing_sequence` are proved. The remaining additive-map
construction needs the category of quasi-coherent modules, its effaceable
cohomology delta functor and the universal extension of its degree-zero section
map, as detailed in the theorem docstring and its node. Neither uniqueness nor
bijectivity is postponed there; both are proved by the retained delivery.

## No longer needed

Removed the unused proof import `Mathlib.CategoryTheory.Sites.LocallyInjective`
from `Sheaf.AlgebraicGeometry.CoherentEtaleEffacingSequence`, as requested in H9.
No dependency node or library module is pruned by this repair. The retained
duplicate-helper repair removed the private declarations
`CoherentEtale.terminal_structure_isIso`, `CoherentEtale.sectionsUnitOf_isIso`,
and `CoherentEtale.sectionsUnit_isIso`, and their node declaration entries.
The first duplicated the existing public terminal-hom theorem; the latter two
duplicated tensor-unit isomorphism statements. The required local argument and
all dependencies used by the retained proof remain.

## Where the brief, the DAG or earlier work was wrong

The returned effacement module retained an unused Mathlib import. H9 is repaired
by deleting exactly that line; the node's proof dependencies already match the
proof and need no change.

The returned change record omitted a real user:
`PrimeCurveArtinSchreierKernel` mentions `liftedCoherentEtaleSheaf` twice in its
public theorem. Its consumer list also predated the current comparison-pullback
module and included a module no longer present. The refreshed `## Users` table
fixes these omissions and records the actual current downstream closure.
The earlier duplicate-helper defect and its repair are retained as described
above. These repairs require no change to Lean declarations or their meaning.

## New nodes

No node is added by this repair relative to the returned sandbox. The retained
delivery contains three nodes that are new relative to the current library:
`lem-pbc-coherent-etale-comparison-morphism` records the proved normalization,
exact-sequence and dimension-shifting API;
`lem-pbc-coherent-etale-effacing-sequence` records the proved simultaneous acyclic
embedding construction; and
`lem-pbc-coherent-etale-normalized-additive-map` records the single remaining
construction theorem in `CoherentEtaleComparisonMorphismExists`.
The existing `def-pbc-canonical-coherent-etale-comparison` node follows this route.
The definition change and all consumer effects are recorded in
`coord/changes/Q3-canonical-coherent-etale-cached-groups.md`.

## Second reading by Q3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
