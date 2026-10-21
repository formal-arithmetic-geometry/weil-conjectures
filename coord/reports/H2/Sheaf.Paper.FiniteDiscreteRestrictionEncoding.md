## What changed

Restored lean/Sheaf/Paper/FiniteDiscreteRestrictionEncoding.lean from its
quarantine archive and named its local smallness instance explicitly and privately. This is the rework.tsv assignment: the live file was missing
after the cluster restore, although its DAG node still attaches the public theorem.
The complete implementation is restored, including the private helpers consumed
through import all by FiniteDiscreteCoefficientRestriction.

The proof compares encoded pushforward module actions using
finiteDiscreteCoefficient_coefficientUnit_pushforward and the existing monoidal
pushforward identity. It constructs the natural pushforward isomorphism, conjugates
by the fixed coefficient equivalences, and applies uniqueness of left adjoints.
Finally extendScalarsIsoComapInv identifies the normalized internal pullback.
All source signatures and the unit route are preserved; no dependency is replaced.

Validation: the archive compiled plainly in 11.2 seconds, but the delivery probe
and a standalone compile failed with unknown constant
instEssentiallySmallProfinite_sheaf_2 in the naturality constructions. Replacing the
anonymous local smallness instance by an explicitly named private local instance
fixes the collision. The repaired standalone compile succeeds in 9.4 seconds and
#print axioms of the public theorem reports only propext, Classical.choice, Quot.sound.
All remaining Lean text agrees exactly with the archive. Read the existing
DAG node and its coefficient-sections dependency, the current coefficient encoding,
and the signatures of the pushforward tensor identity and scalar-extension comparison.
Searched with leanfinder, loogle and grep; the semantic hits concern sheaves of modules,
not a shorter replacement for this existing internal-module encoding proof.

Change record: coord/changes/H2-finite-discrete-restriction-encoding-restore.md.
It lists all direct and transitive consumers, including quarantined consumers.
No second reader was started; independent review is performed by the delivery process.

## Proved and sorry left

This is a zero-hole restoration, not a new hole closure: 0 holes closed, 0 holes added,
0 split off, and 0 holes remaining in the delivered module.
The existing complete proof of
AlgebraicGeometry.ProEtale.CondensedRing.finiteDiscreteCoefficient_restrictionEncoding
is restored with its proved private helpers. There is no declaration left with sorry.
Its node remains lem-weil-pbc-finite-discrete-restriction-encoding.

## No longer needed

None. No import, declaration, node, or module is pruned. Both existing proof steps
and the dependency lem-weil-pbc-finite-discrete-coefficient-sections remain necessary.
All three proof-only imports and both public imports of the archive are retained.

## Where the brief, the DAG or earlier work was wrong

The item currently has no live source and its preserved implementation already has
zero holes. coord/rework.tsv identifies the missing implementation as quarantined
following a cluster restore; absence is not withdrawal. Restoring the full module
repairs that defect. The anonymous-instance collision also required an explicit
private local instance name; the instance type and value are unchanged.
No mathematical statement, definition, source-library interface,
DAG dependency, or blueprint unit route needed correction.

## Second reading by H2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
