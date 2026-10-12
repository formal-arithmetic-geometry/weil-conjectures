## What changed

Proved `LinearMap.exists_leftInverse_of_split_mod_pow` with its signature and
visibility unchanged. Added two fully proved modules:
`Sheaf.RingTheory.FiniteRelationSplittingData` and
`Sheaf.RingTheory.RelationFactorsOfApproximation`.

The main proof first establishes injectivity by Krull intersection. It chooses a finite
free surjection onto `M` and generators for the preimage of `u(N)`. Quotient retractions
lift through this free module and approximate the relation map. A second application
of Krull intersection, in the finite Hom cokernel, supplies an exact factorization.
The presentation lemma constructs the retraction by quotient descent.
All proof imports are non-public. The main module's public imports are unchanged.

Updated the original node's proof, proof dependencies and proof origin to match this
route. No existing statement, definition or interface was changed.

## Proved and sorry left

Closed the original hole `LinearMap.exists_leftInverse_of_split_mod_pow`, node
`lem-weil-pbc-split-injection-after-completion` (1 of 1 original sorries).
Also proved the two new declarations:

- `LinearMap.exists_finite_relation_splitting_data`, node
  `lem-weil-pbc-finite-relation-splitting-data`.
- `LinearMap.exists_relation_factor_of_approximation`, node
  `lem-weil-pbc-relation-factors-of-approximation`.

No sorries remain in any delivered module; no holes were added. This is a complete
proof, not a decomposition into unproved intermediate statements. All three modules
compile through `lcompile.py --all`. The delivery dry run also performs axiom probes.

Edge cases: the arguments use finite free ranks without positivity assumptions;
empty ranks, zero modules, the zero ideal and the zero ring require no separate
exceptions. All original universe parameters remain unchanged, and the presentation
lemma allows different universes for the ring and both modules.

## No longer needed

Removed the original proof import `Sheaf.LinearAlgebra.SplitExtensionFreePresentation`.
The proof no longer uses node `lem-weil-pbc-split-extension-free-presentation`, nor its
unproved declaration `LinearMap.exists_retraction_iff_relation_factors`.
The finite presentation and quotient descent are proved directly from Mathlib.

The saved attempt's `Sheaf.RingTheory.SplitInjectionAfterCompletionAux` and node
`lem-weil-pbc-split-injection-after-completion-aux` were never landed and are omitted.
Its import `WeilConjectures.Mathlib.RingTheory.Filtration` is replaced by
`Mathlib.RingTheory.Filtration`, which directly provides the required Krull theorem.
No source-library module is needed by the delivered proofs.
Redundant proof imports of Cardinality, Isomorphisms and BilinearMap were removed
from the new modules after checking their remaining Mathlib imports supply them.

The original Noetherian-submodule-finiteness and Krull-intersection nodes remain
needed, through their Mathlib implementations. No blueprint unit statement or step
was bypassed: the item is below the unit's realized nodes, and retains the finite
presentation, approximation, Hom cokernel and Krull-intersection argument.

## Where the brief, the DAG or earlier work was wrong

The earlier tool ImportError is no longer reproducible: `deliver3.py --no-push` now
runs. No tooling was edited or worked around.

The saved auxiliary theorem essentially repackaged the original conclusion under
an additional injectivity assumption. It has been replaced by two distinct argument
steps, both proved completely. The saved report also contained a second-reading
section authored by the first worker; that section was removed for the independent
reader to write.

The original categorical splitting criterion imposes a single universe for its
module types. No change to it is needed: the direct quotient-descent proof works
with the item's original independent universes.

The local Stacks source checkout is absent. Read the full statement and proof at
https://stacks.math.columbia.edu/tag/02HO. The presentation of `M` and the preimage
of `u(N)` is an explicit adaptation of its finite-presentation argument; the node's
proof origin records the adaptation. LeanSearch returned HTTP 500 and is recorded
as unavailable, not as a negative search result. LeanFinder and source searches
found ingredients but no exact theorem. The new names and corresponding statements
were checked against the DAG and whole blueprint before their nodes were created.

## New nodes

`lem-weil-pbc-finite-relation-splitting-data` records finite presentation data and
its descent property, proved in
`lean/Sheaf/RingTheory/FiniteRelationSplittingData.lean`. It needs no ideal or
approximation assumptions and only assumes `M` finite.

`lem-weil-pbc-relation-factors-of-approximation` records the finite Hom-cokernel
argument, proved in `lean/Sheaf/RingTheory/RelationFactorsOfApproximation.lean`.
It has no injection `u`, ambient module `M` or retraction conclusion.

Neither node leaves a sorry. No change records or forced adaptations are needed.

## Second reading by M1

1. Compared the delivered target module with the repository version. The target
   theorem signature is byte-for-byte unchanged; only its proof and proof-only
   imports changed. The two added modules and node statements match their Lean
   declarations.

2. Compiled all three delivered modules with `lcompile.py --all`. The target and
   both split-off declarations contain no `sorry`, `axiom`, `unsafe`, `opaque`,
   `extern`, or `implemented_by`. Axiom probes show only `propext`,
   `Classical.choice`, and `Quot.sound`.

3. Checked the split-off statements against the finite-presentation and
   Hom-cokernel arguments. They are true, strictly simpler than the target, and
   introduce no arbitrary data from an existence theorem. Searches recorded in
   the node files found no existing Mathlib or library declaration duplicating
   either result.

4. Reviewed the proof from the target downward. It uses the direct finite
   presentation, quotient descent, approximation, and Krull-intersection route;
   the old categorical splitting criterion is unnecessary. The removed import
   and old proof dependency are listed above, and no additional unused imports
   remain.

5. The unit route is preserved: the finite relation and approximation steps are
   realized by the two new nodes, while the target retains the stated
   Krull-intersection and splitting argument. Edge cases of zero ranks, zero
   modules, and the zero ideal are covered by the same finite-coordinate proofs.

Changed after review: no Lean statements or definitions; only this independent
second-reading record was added.
