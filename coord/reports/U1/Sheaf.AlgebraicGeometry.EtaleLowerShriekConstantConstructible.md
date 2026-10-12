## What changed

Proved `AlgebraicGeometry.Scheme.isConstructibleSheaf_etaleLowerShriek_constant_core` in
`Sheaf.AlgebraicGeometry.EtaleLowerShriekConstantConstructible`. The proof constructs a
`Scheme.Stratification` from `exists_etale_stratified_finite`, proves finite local constancy
of the finite constant module sheaf using the identity cover and constant stalk isomorphism,
pulls it back to each base-changed source, applies finite etale pushforward, then transports
through the finite etale comparison and lower shriek base change isomorphisms. A proved
private helper contains the constant-module argument. Existing public signatures are unchanged.
The wrapper theorem retains its existing proof via the constructibility comparison.

Added proof-only imports `WeilConjectures.ConstructibleSheaf.Pullback` and
`WeilConjectures.Mathlib.CategoryTheory.Sites.Point.ConstantSheaf`. Updated both existing
DAG nodes' proof routes and dependencies. There are no new nodes or statements with sorry.

## Proved and sorry left

Closed the module's one existing sorry:
`AlgebraicGeometry.Scheme.isConstructibleSheaf_etaleLowerShriek_constant_core`
(node `lem-weil-pbc-etale-free-sheaf-constructible-core`). The existing wrapper
`AlgebraicGeometry.Scheme.isConstructibleEtaleModuleSheaf_etaleLowerShriek_constant`
(node `lem-weil-pbc-etale-free-sheaf-constructible`) remains proved.
There are no sorries in the delivered module and none added elsewhere. This is a stage-3
proof from named dependencies; it still depends on the imported finite etale pushforward
theorem `AlgebraicGeometry.Scheme.finiteLocallyConstant_lowerStar_of_finite_etale`, whose
proof is sorry in the current library. No claim of transitive axiom closure is made.

## No longer needed

Removed proof-only import `Sheaf.AlgebraicGeometry.EtaleSheaves`.
The main node no longer needs direct proof-dependency edges to
`def-weil-pbc-etale-site`, `def-weil-pbc-etale-constructible-sheaf`, or
`def-weil-pbc-etale-sheaves`: the predicates are already provided by the public imports.
The four original geometric dependencies remain needed by the core, and are not pruned.
No geometric node or module is bypassed, and no unit statement or realized step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The earlier sandbox was identical to the current library and had proved none of the item's
remaining sorries. Its report described the already proved wrapper as new progress.
The stratification citation in the old proof text said Tag 03S9; the actual stratification
lemma and its current node use Tag 03S0. Corrected the proof docstring and core proof record.
The two pullback conventions differ: stratification supplies `pullback.snd j g`, while
base change uses `pullback.fst g j`. The proof transfers finiteness by pullback symmetry.
The shared topological stratification already contains constructibility, including for an
empty scheme or empty strata; no nonemptiness or noetherian hypothesis was introduced.

## Second reading by U1

1. Compared the delivered module with the repository version. The two public theorem signatures are byte-for-byte unchanged; only the proof of the core theorem and proof-only imports changed. Verdict: pass.

2. Compiled the module with lcompile.py; it compiles without errors or warnings and contains no sorry, axiom, unsafe, opaque, extern, or implemented_by. The proof uses the existing finite etale pushforward theorem, whose own proof remains open in the library; no new split-off theorem was added. Verdict: pass.

3. Checked the private finite-local-constancy helper and both existing target statements against their DAG statements. The helper is a genuine stalk finiteness argument via the constant-sheaf stalk isomorphism, and no statement was weakened or given extra hypotheses. Verdict: pass.

4. Checked the proof route and imports. The route keeps the unit's stratification, pullback, finite etale comparison, pushforward, and base-change steps; the removed EtaleSheaves import is unused, while the two added imports are proof-only. Verdict: pass.

5. Compared both delivered DAG nodes with the Lean proof. Their proof steps and proof_deps record the actual stratification/comparison/pushforward route, and no new node is needed. Verdict: pass.

Changed the report only by recording this second reading. No Lean declarations or DAG statements were changed during review.
