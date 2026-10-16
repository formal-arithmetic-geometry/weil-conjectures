## What changed

Proved `AlgebraicGeometry.closedPoint_iff_residueField_trdeg_zero_and_finite` in
`lean/Sheaf/AlgebraicGeometry/ClosedPointField.lean`, preserving its entire signature and
all original public imports. Added the proof-only import `WeilConjectures.PointCount`.
The proof reuses `Scheme.Hom.finite_residueField_of_isClosed` for closed points. Its
converse uses Mathlib's Jacobson criterion and cancellation of locally finite type.
The transcendence-degree equivalence follows from algebraicity and essential finite type;
the last two clauses use Mathlib's algebraic-extension results over separably closed fields.
Updated the item's DAG proof, proof dependencies, and proof origin to match this route.

## Proved and sorry left

Closed the sole original hole:
`AlgebraicGeometry.closedPoint_iff_residueField_trdeg_zero_and_finite`
(node `lem-kun-closed-point-field`). Holes closed: 1. Holes added: 0. No `sorry` remains
in the delivered Lean module; no intermediate obligations were split off.

The single-file compile passed without warnings in approximately four seconds.
`#print axioms` reported exactly `propext`, `Classical.choice`, and `Quot.sound`.
The diagnostic command was removed after checking.

## No longer needed

Removed the proof dependency
`lem-weil-pbc-finitely-generated-field-finite-transcendence-basis` from this node's route:
Mathlib `trdeg_eq_zero_iff` and `Algebra.finite_of_essFiniteType_of_isAlgebraic` replace
choosing and analyzing a finite transcendence basis. This node is a Mathlib leaf and has
no project module to withdraw. No original import was removed, and no project module is
claimed to become globally unreachable. The explicit affine-cover/maximal-ideal proof
and its residue-field transport helpers are unnecessary here. The Zariski-lemma node
remains recorded because the reused source-library theorem implements that argument.

The candidate additional proof imports
`Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra`,
`Mathlib.RingTheory.AlgebraicIndependent.Transcendental`, and
`Mathlib.RingTheory.LocalRing.ResidueField.Ideal` were tested and removed as redundant:
the existing imports plus `WeilConjectures.PointCount` already supply them.

## Where the brief, the DAG or earlier work was wrong

No false statement or interface defect was found. The DAG's affine-chart proof is valid
but longer than the already proved source-library/Jacobson route. The unit
`sk-prop-sf-kunneth-ordinary` has empty `realized.statement` and `realized.steps`; no
unit statement or unit proof step is bypassed. No signature, visibility, definition,
other module, or target was changed.

Searches were run with `msearch.py` (LeanFinder, Loogle, grep), and direct `rg` against
Mathlib and both library roots. The existing source-library theorem and Mathlib
transcendence-degree, essential-finiteness, and separably-closed declarations were
read and used. The original declaration docstring is preserved.

## Second reading by F2

1. Compared the entire delivered module with the shared repository using `diff -u` and
   checked the theorem signature byte for byte with a separate assertion. PASS: only the
   proof and the proof-only `import WeilConjectures.PointCount` changed. There are no
   definitions, new declarations, adapted modules, changed signatures, or change records.
   Existing public imports provide notions used in the signature; the added import is private.
2. Independently compiled the delivered file with `lcompile.py` (3.5 seconds, no warnings).
   Compiled a scratch copy with `#print axioms` (4.4 seconds): exactly `propext`,
   `Classical.choice`, and `Quot.sound`. PASS: no remaining `sorry`, forbidden declaration,
   hidden data construction, or extra axiom. The delivered theorem closes one original
   hole and adds zero holes; this is a proof, not a decomposition.
3. PASS: there are no split-off statements or new nodes. Read the actual source of
   `Scheme.Hom.finite_residueField_of_isClosed`, the Jacobson closed-point criterion,
   `trdeg_eq_zero_iff`, `Algebra.finite_of_essFiniteType_of_isAlgebraic`, and both
   separably closed extension results. Their hypotheses match this proof. Checked the
   empty-scheme case (there is no point to supply), rational points (degree one), generic
   points with transcendental residue fields, and positive-characteristic inseparable
   closed residue extensions; no exceptional case is lost.
4. PASS: independently searched Mathlib and both library roots for essential finite type
   residue-field shortcuts, including `msearch.py` with a different query. No shorter
   existing composite theorem was found. The proof reuses the source theorem and Mathlib
   directly, and its explicit three-map essential-finiteness argument follows the actual
   definition of `residueFieldAlgebraMap`. Every import supplies signature vocabulary or
   proof declarations. The only old proof dependency omitted is the finite transcendence
   basis node already listed above; it has no project module to prune. Read the unit's
   `realized` record (both arrays empty); no prescribed unit step is bypassed.
5. PASS after one metadata correction: checked the complete node diff, its three retained
   proof dependencies and their Mathlib/source implementations, and the proof origin.
   The union of step `uses` equals `proof_deps`. Changed the final step's `elementary`
   field from `true` to `false`, since it explicitly invokes the two non-elementary field
   extension lemmas. All other node fields, especially the statement and Lean signature,
   are preserved. There are no new nodes requiring additional fields.

Second-reading changes: corrected the final DAG step's elementary flag and appended this
review. The Lean proof was left intact because no mathematical or implementation fault
was found. Scratch diagnostics live outside `lean/` and are not part of the delivery.
