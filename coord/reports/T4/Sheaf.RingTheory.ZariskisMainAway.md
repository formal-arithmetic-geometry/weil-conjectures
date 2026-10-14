## What changed

Verified the already-landed conversion theorem
`Algebra.zariskisMainProperty_of_isQuasiFiniteAtPrime` and simplified its proof:
rewrite the open singleton along the fibre homeomorphism, then use `hq` directly.
The signature, visibility and imports remain identical. No new statements or nodes.
The original and revised modules both compile through lcompile.py.

## Proved and sorry left

The only theorem, `Algebra.zariskisMainProperty_of_isQuasiFiniteAtPrime`, is proved
without sorry. It was already proved in the supplied repository by the landed K2
interface repair (20261013T215607-L-899022). This delivery closes zero holes out of
zero existing holes and adds zero holes; it claims no new proof progress.
The underlying Zariski-main node is
`lem-weil-pbc-integral-closure-zariski-main-away`; its recorded declaration is now
Mathlib's `Algebra.ZariskisMainProperty.of_finiteType`.
No sorry remains in the delivered module.

## No longer needed

None newly pruned. Both public imports supply the statement and its defining
hypothesis; the private Mathlib.RingTheory.ZariskisMainTheorem import supplies
QuasiFiniteAt.of_isOpen_singleton_fiber. No additional dependencies are imported.
The existing two-step DAG route and the unit's realized steps remain unchanged.

## Where the brief, the DAG or earlier work was wrong

The assignment says this module still contains sorry, but the supplied module
already contains a complete proof. coord/repairs.txt still lists upstream review
#1428 for this module although coord/changes/zariskisMainProperty-wrapper-removal.md
records the landed repair. The node's lean record points at Mathlib, so searching
nodes by this Sheaf module in the lean.module field returns none; its docstring
identifies the correct node and the node's first proof step names the helper.
The replacement proof is a small simplification and verification of that repair,
not a new reduction or an additional proof of the old duplicate conclusion.

## Second reading by T4

1. Compared the delivered module with the repository version. The theorem
   signature, visibility, statement, and imports are byte-for-byte unchanged;
   only the proof term was simplified.
2. Compiled the delivered module with `lcompile.py`; it has no `sorry`, `axiom`,
   `unsafe`, `opaque`, `extern`, or `implemented_by`. A scratch `#print axioms`
   check reports only `propext`, `Classical.choice`, and `Quot.sound`.
3. The proof uses the existing Mathlib conversion theorem and the existing
   fibre homeomorphism. No statement was split off, and no new node is needed;
   the recorded node and its proof dependencies remain consistent.
4. The route still realizes both steps of the unit: convert the fibre singleton
   hypothesis, then apply Mathlib's Zariski-main theorem. No import or node was
   pruned because both imports remain used by the public statement/proof.
5. The DAG record, source references, and Lean declaration agree with the
   delivered proof and unchanged target meaning. Verdict: pass.

Changed only the proof's final openness transport from an `exact` with a
`simpa` subproof to a direct rewrite followed by `exact hq`.
