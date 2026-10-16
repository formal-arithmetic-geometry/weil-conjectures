## What changed

Proved `AlgebraicGeometry.exists_affineOpen_closed_stratum` in the item module. The proof
chooses an affine neighborhood inside the open factor of the selected locally closed stratum,
identifies its preimage with the closed factor, restricts local closedness and constructibility
along the open subtype embedding, and obtains compactness of the complement from constructible
retrocompactness and `Scheme.compactSpace_of_isAffine`.

Removed the unused proof-only import `Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated`.
Updated the DAG proof description and proof origin to match the implemented route.

## Proved and sorry left

Closed the sole hole, `AlgebraicGeometry.exists_affineOpen_closed_stratum`.
No hole remains in the delivered module and no new hole was added. The scratch `#print axioms`
check reports exactly `propext`, `Classical.choice`, and `Quot.sound`; thus the theorem is fully
proved, not a decomposition onto unresolved statements.

## No longer needed

Removed the proof-only import `Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated`.
No DAG dependency or Sheaf module is pruned. In particular, `lem-weil-pbc-affine-scheme-qcqs`
remains: the proof uses its compactness clause via its recorded Mathlib instance
`Scheme.compactSpace_of_isAffine`. The quasi separatedness clause is unnecessary.

## Where the brief, the DAG or earlier work was wrong

The first worker's report and DAG copy incorrectly removed
`lem-weil-pbc-affine-scheme-qcqs`: using its recorded Mathlib compactness instance still uses
that dependency. The second reading restored it. The obsolete quasi separatedness import
was also retained unnecessarily; it is now removed. No mathematical statement was changed.

## New nodes

None.

## Second reading by D4

1. Compared the only delivered module with the repository version. The existing theorem
   signature is byte for byte unchanged, and no declaration or definition was added or
   removed. Only its proof, whitespace, and one proof-only import differ. Verdict: pass.
2. Compiled the item with `lcompile.py`, including the sandbox import-order check, and compiled
   a scratch copy with `#print axioms AlgebraicGeometry.exists_affineOpen_closed_stratum`.
   It reports exactly `propext`, `Classical.choice`, and `Quot.sound`. No sorry, forbidden
   declaration, or hollow definition is present. Verdict: pass.
3. No statement was split off. Checked each conclusion: containment in the open factor makes
   the selected stratum closed; continuous and open-embedding preimages preserve the stated
   properties; retrocompactness and affine compactness give compact complement. The empty
   partition case is vacuous because `k : Fin 0` cannot exist; a singleton partition and the
   full selected stratum give empty compact complement. Cover and disjointness are legitimately
   unused: the local argument holds for any such family. Verdict: pass.
4. Searched the library and Mathlib for compact constructible sets and local closed strata.
   The current proof combines existing declarations without introducing any new statement.
   Both public imports supply signature vocabulary; the remaining private import supplies
   retrocompactness. Removed the unused quasi separatedness import. The unit record
   `sk-prop-sf-comparison` has no realized steps; the node remains the local closed-stratum
   ingredient in step 5 of `lem-sf-proetale-constructible-origin`, so no unit route is bypassed.
   Verdict: pass.
5. Read the node and the Mathlib records of all its dependencies. Restored the affine compactness
   dependency because it records precisely the instance used in the proof; the remaining
   dependencies describe the local-closed presentation, affine basis, restriction, Boolean
   complement, and retrocompactness. The proof-dependency list equals the union of step uses,
   and the proof origin matches the implemented route. Verdict: pass.

Second reading changed: removed one unused proof-only import, restored the erroneously pruned
DAG dependency, clarified proof origin, and replaced the superseded review with this audit.
