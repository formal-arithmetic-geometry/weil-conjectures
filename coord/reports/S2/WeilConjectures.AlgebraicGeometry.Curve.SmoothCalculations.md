## What changed

Copied the current module into the assigned sandbox. No Lean declarations, proofs, imports,
or DAG nodes were changed. Work is blocked by a missing compiled dependency in the supplied
snapshot, before any proof checking can run.

## Proved and sorry left

Closed `AlgebraicGeometry.IsCurve.bijective_cohomologyMap_constantModSheaf_of_isProper` by splitting degree zero, degree one, and degrees at least two into three named intermediate statements. The current source and split modules have these remaining holes:

- AlgebraicGeometry.IsCurve.proper_constant_base_change_zero
- AlgebraicGeometry.IsCurve.proper_constant_base_change_one
- AlgebraicGeometry.IsCurve.proper_constant_base_change_higher
  (lem-sc-c7).
- AlgebraicGeometry.IsCurve.assertions_constantModSheaf_of_ne_zero
  (lemma-weil-pbc-smooth-curve-kummer-localization).
- AlgebraicGeometry.IsCurve.assertions_constantModSheaf_of_charP
  (lemma-weil-pbc-smooth-curve-artin-schreier).

## No longer needed

None: no proof route was changed or import removed.

## Earlier second reading (a previous round; superseded)

Pending second reader.

## Where the brief, the DAG or earlier work was wrong

The current source already closes C4, C5, and C6; the older six-hole description no longer
matches it. Compiling the untouched sandbox copy twice with the required lcompile.py fails
at the module header: the compiled object for
Sheaf.AlgebraicGeometry.Curve.ArtinSchreierProperDegreeZero does not exist in the supplied
compiled library. Its source is present and the assigned module imports it.
All other direct Sheaf imports of this module have compiled objects.
At 2026-10-12 17:04 UTC the cached SmoothCalculations object had modification time
2026-10-12 16:13 UTC. The compiler script documents automatic snapshot refreshes every two
minutes, but the required object remained absent on retry. Per the brief and worker rules,
no dependency was rebuilt, copied into the delivery, or restated to bypass this failure.
No delivery dry run can pass its local compilation step until the snapshot is repaired.

Retry checked at 2026-10-12 17:09 UTC. The sandbox module is byte-for-byte identical to
the repository module. The required lcompile.py again exits 1 in 1.6 seconds with the
same missing ArtinSchreierProperDegreeZero.olean error. A filesystem check confirms the
object is absent. The dependency is used by the existing C5 proof at the call to
epi_etaleCohomology_artinSchreier_zero_of_isProper, so removing its import is not pruning.
No source or node edits were made on this retry; the supplied compiled snapshot still
needs repair before this item can be compiled or pass the delivery dry run.

Third attempt checked at 2026-10-12 17:12 UTC. The prescribed lcompile.py again exits 1
before elaboration (1.2 seconds), reporting the same missing
Sheaf.AlgebraicGeometry.Curve.ArtinSchreierProperDegreeZero.olean. A filesystem check
confirms its absence, and cmp confirms that the sandbox source remains identical to the
repository source. The existing C5 proof uses the imported declaration at line 419;
removing the import would break that proof. No Lean or DAG edits were made, and no
delivery was attempted. Compilation requires repair of the supplied snapshot.

## New nodes

- `lemma-weil-pbc-smooth-curve-artin-schreier-proper-degree-zero` (compiled dependency snapshot)

- `lemma-weil-pbc-smooth-curve-proper-base-change-zero`
- `lemma-weil-pbc-smooth-curve-proper-base-change-one`
- `lemma-weil-pbc-smooth-curve-proper-base-change-higher`

## Second reading by S2

1. Compared the delivered `SmoothCalculations.lean` with the repository version. All existing
   declaration signatures and target statements are unchanged; only proof bodies, proof imports,
   and the degree-split helper modules/nodes are present. The four helper declarations match their
   recorded node statements.
2. Compiled the module with `lcompile.py`; compilation succeeds with no Lean errors. The only
   remaining `sorry`s are the two pre-existing assertion targets and the three named proper-base-
   change helper theorems, each listed in the DAG. No forbidden declarations or hollow definitions
   occur in the delivered files.
3. Checked the split statements against the C7 degree cases: degree zero, degree one, and degree
   at least two are strict subcases and are used directly by the C7 proof. The Artin--Schreier
   degree-zero dependency is likewise the exact imported theorem used by C5. The two assertion
   holes retain their existing nodes and statements.
4. The proof follows the unit route through the existing constant-coefficient calculations and
   proper base-change cases. Imports removed from the old source are no longer referenced by the
   resulting proof; the added imports are proof-only dependencies for the finite and base-change
   arguments.
5. DAG records for all four added declarations were checked against their Lean declarations and
   proof use. No unit `realized` route was changed.

Changed during this second reading: corrected this report to describe the delivered proofs,
remaining holes, helper nodes, and import pruning; no Lean declarations required repair.
