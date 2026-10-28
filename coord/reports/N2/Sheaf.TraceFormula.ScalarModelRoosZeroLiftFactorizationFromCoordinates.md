## What changed

Repaired the missing source zero-shift hypothesis in
scalarModelRoosZeroLift_factorization_from_coordinates,
scalarModelRoosZeroLift_factorization_exists, and
scalarModelRoosZeroLift_factorization. Their outer caller
scalarModelRoosZeroLift_existence already has this hypothesis; its signature and
conclusion are unchanged, and its call now applies factorization_from_coordinates directly with that hypothesis.
No definition, source-library declaration, or Challenge target changes.

The assigned proof constructs the natural transformation of scalar-extended
restricted towers, forms the actual scalar/Roos composite k, proves its zero
shifted coordinate from hf, and computes its first coordinates on nested tensor
generators. The inverse restricted-section identification lets the given
coordinate predicate compare h with k. Existing nested-coordinate uniqueness
identifies their localizations. Counit naturality finishes the reduction from the
new target-system normalization equation. These are complete Lean proofs, not
new assumptions about the chosen lift.

The existence caller now applies the already proved scalarModelRoosZeroLift_core
with hf. Three adapted existing modules are unclaimed; their signatures change
only where described above. Change record:
coord/changes/N2-scalar-roos-source-zero-shift.md.

Validation: lcompile --all compiled all five files without warnings, in import
order. Times were 1.3 s for normalization, 52.9 s for the assigned coordinate
proof, 16.0 s for outer existence, 6.4 s for factorized existence, and 9.9 s for
the factorization wrapper. The coordinate file keeps the large scalar-change
witness hidden and proves general counit naturality in a private helper.

## Proved and sorry left

The assigned file originally had one hole in
WeilConjectures.scalarModelRoosZeroLift_factorization_from_coordinates. Its
unrestricted old statement is not proved: the missing hypothesis is repaired
explicitly. The repaired theorem has a complete proof from the strict-coordinate
calculation and the separate target-system normalization lemma.

One new hole remains, exactly the public theorem
WeilConjectures.scalarModelRoos_counit_normalization, in
Sheaf.TraceFormula.ScalarModelRoosCounitNormalization, node
lem-trf-scalar-model-roos-counit-normalization. Its proof is exactly by sorry;
its docstring and node give the source and proof plan. The assigned module and
all three adapted modules have zero holes. Count this as a decomposition of the
repaired obligation, not as proof of the former statement: zero original
unchanged holes proved, one lower obligation split off. No definitions contain
holes, and no new object is chosen from an unproved existence theorem.

## No longer needed

Removed the proof import
Sheaf.TraceFormula.ScalarModelRoosZeroLiftStrictExistence from
ScalarModelRoosZeroLiftFactorizationExistence. Its node
lem-trf-scalar-model-roos-zero-lift-strict-existence is no longer a proof
dependency there: the proved core with the restored hf gives the required lift.
This was its only current DAG citer and Lean importer. The N3-held module itself
is preserved, with no edit or withdrawal.

The outer existence proof now imports and uses FromCoordinates directly. This
also removes Sheaf.TraceFormula.ScalarModelRoosZeroLiftFactorization and
Sheaf.TraceFormula.ScalarModelRoosZeroLiftFactorizationExistence from the target
route, with nodes lem-trf-scalar-model-roos-zero-lift-factorization and
lem-trf-scalar-model-roos-zero-lift-factorization-existence. Their duplicate
existence/uniqueness wrappers are unnecessary for the lift the core already
supplies. They remain as repaired APIs so the rest of the library still compiles.
All three removed dependencies have no other current DAG parents or Lean
importers outside that old chain. No blueprint unit statement or step is removed.

The assigned proof imports the core, uniqueness, scalar/Roos comparison, scalar
counit API, and the new normalization statement; each is used. Private APIs are
accessed with import all. No existing public import is removed.

## Where the brief, the DAG or earlier work was wrong

STATEMENT-DISPUTED (former signatures, repaired): successive splits forgot the
source zero-shift condition. The predicate on f and h observes only the first
Roos product coordinate. A map supported in the shifted product summand can
represent a nonzero lim^1 class while its first coordinate is zero; choosing h=0
then satisfies the old coordinate predicate and zero-shift condition on h.
For example, the tower of tails V_n = direct_sum_{m >= n} k with inclusion
transitions has lim V_n=0 and nonzero lim^1 (the tuple of successive basis vectors
is not a boundary). Regard it as a residue-field coefficient system and use a
free source concentrated in degree one. Its shifted map is invisible to the
predicate. Thus the former instructions to delete the shifted term using only
hh did not justify deleting the shifted component of f. Restoring hf follows
the actual outer theorem and the already proved core; it is not a weakened
replacement silently counted as a proof.

The remaining target-system equation is not supplied by the core. It concerns
the normalized scalar realization and the whole-system counit, with both Roos
summands retained. It needs its own normalization argument. The reduction does
not infer equality of derived tower morphisms from their finite evaluations.

## New nodes

lem-trf-scalar-model-roos-counit-normalization states the equation before any
source map is inserted: arbitrary D, the scalar/Roos tower transformation a and
its tensor normalization. It has no E, good source P, f, h, or zero-shift lift
hypothesis. The assigned proof separately handles all those strict-coordinate
conditions. The new equation retains both Roos coordinates, so it does not repeat
the original dropped-shift error. Its plan uses the fixed quotient model,
coherent presentation comparison, full-tower adjunction transpose, universal
scalar counits, and localization. The source is the scalar common-stage
transport in Proposition 3.5.1 and Stacks 06YY/0941. Logged LeanSearch,
Loogle/LeanFinder and grep searches found no existing theorem with this equation.
Blueprint search found no duplicate. Edge checks: zero systems and empty schemes
give zero maps; identity scalar change retains the whole counit triangle;
no boundedness or surjectivity condition on D is introduced. The statement
therefore retains the shifted contribution needed for general target systems.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.TraceFormula.ScalarModelRoosCounitNormalization": "396a8a653d31077533c724683c8733154d27e657", "Sheaf.TraceFormula.ScalarModelRoosZeroLiftExistence": "dfd651dd428c597b298cff63136beb5e56b8c0a4", "Sheaf.TraceFormula.ScalarModelRoosZeroLiftFactorization": "d7a26db7abfe1960833d0b09dcc3b1178486eebf", "Sheaf.TraceFormula.ScalarModelRoosZeroLiftFactorizationExistence": "8caed1b61ad6a7ddc8bee2dfe17ad3bee69b1e54", "Sheaf.TraceFormula.ScalarModelRoosZeroLiftFactorizationFromCoordinates": "076494766f121d25a6f9bf6d70a07648444ba3fa"}, "results": {"Sheaf.TraceFormula.ScalarModelRoosZeroLift": {"hash": "868796b16c44d583d854e88f3bcd43c2a0b6e4b6", "status": "OK"}}, "seconds": 68, "time": "2026-10-28T10:47:10+0800", "transitive": 0, "version": 1}
```

## Second reading by N2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
