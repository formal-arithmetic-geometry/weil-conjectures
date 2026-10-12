## What changed
Added `Sheaf.RingTheory.RegularLocalFibreFinrank` with the named dimension-comparison
intermediate theorem, and replaced the hole in `Algebra.regularLocal_iff_smoothAtPrime`
with the reduction to that comparison and the two existing smoothness dimension criteria.
All existing signatures and definitions are unchanged. New proof dependencies use plain imports.
The parent DAG now records the actual reduction. The comparison node records its full
cotangent-sequence/dimension argument and all ingredients.

## Proved and sorry left
Hole closed: `Algebra.regularLocal_iff_smoothAtPrime` (the item's sole original hole).
Hole added and left: `Algebra.regularLocal_iff_fibre_finrank_eq_dimension`, node
`lem-weil-pbc-regular-local-fibre-finrank`, in the new module.
This is one-for-one decomposition, not an axiom-free proof or positive net hole reduction.
The parent additionally uses the existing open
`Algebra.isSmoothAtPrime_of_finrank_kaehlerDifferential_le`; no hole was added there.
The comparison needs the nontrivial exact-sequence/localization construction and cannot
be closed in a few minutes from a single existing declaration.

## No longer needed
Removed direct proof imports from the parent:
`Sheaf.FieldTheory.SeparablyGeneratedDifferentialsDimension`,
`Sheaf.Paper.SeparableResidueCotangentInjective`,
`Sheaf.RingTheory.DimensionAtPointLocalRingTrdeg`, and
`WeilConjectures.Mathlib.Topology.KrullDimension`.
The first three now belong to the comparison module's proof route; the fourth is available
through the two dimension-criterion imports. No module is asserted to leave the target
import closure, since these dependencies remain in the lower argument or other routes.

Old parent proof dependencies no longer used directly (some remain under the comparison):
- `def-weil-pbc-localization-at-prime`
- `def-weil-pbc-noetherian-ring`
- `lem-weil-pbc-finite-type-algebra-noetherian`
- `lem-weil-pbc-localization-noetherian`
- `def-weil-pbc-separable-field-extension`
- `lem-weil-pbc-jacobi-zariski-differential-maps`
- `lem-weil-pbc-separable-residue-cotangent-injective`
- `lem-weil-pbc-regular-local-cotangent-dimension`
- `def-weil-regular-scheme`
- `lem-weil-pbc-separably-generated-differentials-dimension`
- `def-kun-transcendence-degree`
- `lem-weil-pbc-kahler-differentials-localization`
- `def-weil-pbc-module-localization`
- `lem-weil-pbc-dimension-at-point-local-ring-trdeg`
- `def-kun-topological-dimension-at-point`
- `def-weil-pbc-singular-ideal`

## Where the brief, the DAG or earlier work was wrong
The first report incorrectly called a one-for-one decomposition a proof without stating
its net count, claimed an import of `SmoothOverFieldRegularLocal` that did not exist,
and did not update the parent DAG to the actual Lean proof. The new node omitted the
separably-generated differentials ingredient and carried copied review and split-history
fields from another node. These have been repaired. No statement was weakened.
The source checkout of Stacks is absent on this machine, so the second reader checked
the cited proof directly at https://stacks.math.columbia.edu/tag/00TV.

## New nodes
`lem-weil-pbc-regular-local-fibre-finrank`:
`dag/nodes/sec-proper-base-change/lem-weil-pbc-regular-local-fibre-finrank.json`;
Lean module `Sheaf.RingTheory.RegularLocalFibreFinrank`, declaration
`Algebra.regularLocal_iff_fibre_finrank_eq_dimension`. This separates the cotangent
comparison from the final smoothness criteria, with strictly less conclusion than the
original theorem: it makes no assertion of smoothness. No change record is needed.

## Second reading by V1
1. Compared the existing module with the repository version using diff. The complete
   existing theorem signature is byte for byte unchanged. No definition or public import
   changed. The added module introduces only the documented intermediate theorem.
2. Compiled both modules locally through lcompile.py, without errors or warnings.
   Scanned both modules: the only sorry is the comparison's named public theorem;
   no definition, axiom, unsafe, opaque, implemented_by or extern is introduced.
   Scratch #print axioms checks report only propext, Classical.choice, Quot.sound,
   and sorryAx, as expected for the declared open dependencies.
3. Read the comparison against Tag 00TV and the exact-sequence, separable-residue,
   differential-dimension, localization and point-dimension ingredients. It is true:
   finite dimensions e+t and d+t are equal exactly when e=d. Checked edge cases:
   a field at its zero prime has e=d=0; a polynomial algebra at its generic prime
   has local dimension zero and fibre dimension equal to transcendence degree;
   at a rational origin both dimensions count variables; dual numbers at their
   maximal ideal have e=1 and d=0, so both regularity and the equality fail.
   The zero ring has no prime satisfying the hypotheses. Fresh LeanFinder, Loogle
   and source grep searches found ingredients, not an existing comparison theorem.
   The intermediate has a complete proof docstring and a matching node, and its
   conclusion is a dimension comparison, not a renamed smoothness assertion.
4. Kept the valid final reduction; removed unused direct proof imports and moved
   the comparison ingredients to its own module. Retained all statement imports.
   Listed every removed old parent proof dependency above. Read sk-thm-p1.json:
   none of its realized statement/step nodes is bypassed or changed; this is below
   the unit level. No global module pruning is claimed.
5. Updated the parent proof/proof_deps/proof_origin to the Lean reduction. Rebuilt
   the new node's argument into setup, exact sequence, dimension computation and
   cancellation, added missing dependencies and all statement notions, recorded
   actual fresh searches, and removed copied review metadata. Its lean statement
   agrees with the declaration and its new-node fields satisfy the stage-3 brief.

Changes by this second reader: import pruning/relocation, expanded lower-hole proof
text, corrected both DAG routes and new-node metadata, and corrected this report.
No mathematical signature or valid proof term was changed.
