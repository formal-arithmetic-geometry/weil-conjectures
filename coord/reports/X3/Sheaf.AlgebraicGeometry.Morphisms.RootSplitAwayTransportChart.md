## What changed
Proved `AlgebraicGeometry.Scheme.root_split_away_transport_chart` without changing its signature or imports. Two proved private helpers perform the pullback transport and identify the degree-one root product chart. The latter uses evaluation, a finite coproduct indexed via a universe lift, and the fact that the basic open of a unit is the whole spectrum.

## Proved and sorry left
Closed the sole hole: `AlgebraicGeometry.Scheme.root_split_away_transport_chart` (node `lem-sbc-root-split-away-transport-chart`). No holes added; no `sorry` remains in the delivered module. Both private helpers are fully proved.

## No longer needed
None. No proof-dependency imports were present or added; the existing Mathlib imports suffice.

## Where the brief, the DAG or earlier work was wrong
No mathematical error found. Mathlib's finite `sigmaSpec` isomorphism requires its indexing type to share the ring universe, so the proof uses `ULift (Fin d)` and transports the coproduct and product back to `Fin d`. The proof covers d=0 and d=1 without additional hypotheses.

## Second reading by X3
1. **Interface and accidental changes.** Compared the delivered module with the repository
version. The theorem name, binders, lets, hypotheses, conclusion, imports, and visibility are
byte-for-byte unchanged; only its proof and two private proof helpers were added.
2. **Proof and axioms.** Compiled the module with `lcompile.py` and a scratch axiom probe.
There are no `sorry`, `axiom`, `unsafe`, `opaque`, `extern`, or hollow definitions. Each
declaration depends only on `propext`, `Classical.choice`, and `Quot.sound`.
3. **Statements and searches.** No statement was split off. The private pullback helper is
exactly the transport calculation in the node proof. The degree-one helper is the evaluation
isomorphism for `AdjoinRoot (X - C a)`, its finite product, and `sigmaSpec`; these are the
Mathlib declarations used by the proof. The node's recorded searches were checked, and no
duplicate library declaration was introduced.
4. **Route and edge cases.** The supplied affine chart is transported through `pullback.map`,
then each summand through its inverse; evaluation identifies the degree-one root algebra with
the base. `ULift (Fin d)` handles the universe required by `sigmaSpec`, and the unit argument
makes the basic open top. The construction remains valid for `d = 0` and `d = 1`.
5. **DAG agreement and pruning.** The item node's existing proof sketch records this same
route and its `proof_deps` remains empty because all nontrivial ingredients are Mathlib
declarations. The unit route is unchanged and no imports or nodes became unnecessary.

**Changes made:** added this second-reading record. No Lean statement or import was changed.
