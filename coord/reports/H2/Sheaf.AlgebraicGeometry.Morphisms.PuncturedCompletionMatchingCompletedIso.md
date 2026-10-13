## What changed

Replaced completedMap_isIso's hole with a proof from injectivity and surjectivity
of an explicit ring pushout map. Original signature and public import unchanged.
Added proof-only imports CompletedMatchingRingMapInjective and
CompletedMatchingRingMapSurjective. CompletedMatchingRingMap constructs the map
and proves its compatibility equation. The main proof checks both pullback
projections and uses affineness of finite s. No arbitrary witness is chosen.

## Proved and sorry left

Closed AlgebraicGeometry.Scheme.CompletionGluingData.completedMap_isIso,
node lem-sbc-punctured-completion-matching-completed-iso. No direct hole remains
in the assigned module. Added two holes:

- AlgebraicGeometry.Scheme.CompletionGluingData.completedRingMap_injective,
  node lem-sbc-completed-matching-ring-map-injective.
- AlgebraicGeometry.Scheme.CompletionGluingData.completedRingMap_surjective,
  node lem-sbc-completed-matching-ring-map-surjective.

This is a decomposition: one upper hole closed, two partial algebra assertions
added, net -1. Compatibility and the complete geometric conversion are proved.
The holes isolate the kernel and cokernel parts of 05ER. Their docstrings give
the source proof and address empty punctures and zero algebras.

## No longer needed

None. The existing matching-sections public import is necessary for the statement.
No original planned node or module was bypassed; the unit route is preserved.
Finiteness of the candidate and the punctured comparison are not needed here,
as already specified by the original plan.

## Where the brief, the DAG or earlier work was wrong

The sole DAG proof step cited only constructions and conventions, with no stated
Lean kernel or cokernel lemma for 05ER. The two new statements expose these
obligations. The statement is not disputed. Initially the shared build lacked
PuncturedCompletionMatchingSections.olean; its refresh resolved the failure.
LeanFinder and local rg found no shorter algebra comparison. Loogle did not
recognize Scheme.Spec and LeanSearch returned Internal Server Error. Mathlib's
isPullback_SpecMap_pushout supplies the geometric conversion.

## New nodes

- def-sbc-completed-matching-ring-map: explicit completed ring pushout map in
  CompletedMatchingRingMap, with compatibility proved and no hole.
- lem-sbc-completed-matching-ring-map-injective: kernel part of 05ER in
  CompletedMatchingRingMapInjective; one hole.
- lem-sbc-completed-matching-ring-map-surjective: cokernel part of 05ER in
  CompletedMatchingRingMapSurjective; one hole.

No interface changes, forced adaptations, or change records.

## Second reading by H2

1. The existing target statement and signature were compared byte for byte with
the repository version; they are unchanged. The completedMap proof uses the
declared ring comparison and the affine pullback API, so it proves exactly the
target statement.

2. The two split-off statements are the injectivity and surjectivity halves of
the explicit ring comparison. Each is strictly simpler than the target, has a
source and a complete proof description, and handles the empty and zero cases.
No duplicate declaration was found in the library or Mathlib.

3. All delivered modules compile individually with the local compiler. There
are no axioms, unsafe declarations, or sorry terms in definitions; the only
remaining sorry terms are the two named split-off theorems.

4. The proof follows the unit route through the completed matching-ring map,
then uses the existing finite-affine and Spec pushout results. The imports are
minimal for the declarations used; no old proof dependency was bypassed.

5. The DAG node proof, proof dependencies, and proof origin agree with the
Lean proof. The new definition and two lemma nodes record the corresponding
public declarations and their sources.

Changed: added the explicit completed ring map and its compatibility theorem,
split injectivity and surjectivity into named theorems, and used them to prove
completedMap_isIso. No target statement or existing interface was changed.
