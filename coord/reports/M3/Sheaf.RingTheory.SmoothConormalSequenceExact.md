## What changed

Proved `Algebra.Extension.smooth_conormal_sequence_exact` in
`lean/Sheaf/RingTheory/SmoothConormalSequenceExact.lean`, preserving its full signature,
public import, and docstring. No other module, statement, or definition changes.

The proof follows the five steps of node
`lem-weil-pbc-smooth-conormal-sequence-exact` (Stacks 06A9 via 06A7).
The extension homomorphism induced by A → B supplies the generator equation.
`Algebra.FormallySmooth.liftOfSurjective` gives B → A/I² using
`Ideal.cotangentIdeal_square`. Its conormal map is a left inverse after the
isomorphism `Cotangent.map_toInfinitesimal_bijective`, proving injectivity.
For middle exactness, the two extension maps B → B/J² differ by a derivation;
`Cotangent.map_sub_map` factors that difference through the cotangent complex.
Consequently a kernel element comes from I/I². The composite is zero because
universal differentials kill scalars. Finally,
`exact_cotangentComplex_toKaehler` and
`KaehlerDifferential.subsingleton_of_surjective` prove surjectivity.
These are Mathlib implementations of the existing node's steps, so the route
and its three proof dependencies are unchanged; no node copy is necessary.

Local launcher compilation passes without warnings. The proof is uniform in
all three universes and uses no nontriviality, locality, or characteristic
assumption; zero rings and identity maps are included.

Searches: launcher LeanFinder for the smooth conormal exact sequence;
launcher Loogle for `Algebra.Extension.Cotangent.map_sub_map`; launcher grep
for the homotopy, infinitesimal bijection, and differential vanishing lemmas;
read the Mathlib definitions and proofs in Extension/Basic,
Extension/Cotangent/Basic, Smooth/Kaehler, Smooth/Basic, and Kaehler/Basic.
No source-library proof of this theorem was found.

## Proved and sorry left

Closed: `Algebra.Extension.smooth_conormal_sequence_exact`, node
`lem-weil-pbc-smooth-conormal-sequence-exact` (1 of 1 original holes).
No holes remain in the module. No holes added; no statements split off.
This is a complete proof from Mathlib, not a decomposition into holed lemmas.

## No longer needed

None. No imports removed or added. All three planned proof dependencies remain
used through their existing Mathlib declarations: Kähler differentials,
smoothness, and square-zero lifting. No DAG nodes or modules are claimed pruned.
The unit `sk-thm-p1` and all of its realized statements and steps are preserved.

## Where the brief, the DAG or earlier work was wrong

No mathematical defect found. The detailed argument already has enough Mathlib
API to close it without any new intermediate statement. The recorded node
searches did not highlight `Cotangent.map_sub_map`, which supplies exactly the
derivation factorization needed in step 4.

## Second reading by M3

1. Interface preservation: PASS. Compared the delivered module with the repository
   using `diff -u`. The only change is replacement of the original theorem's
   `sorry` by its proof. The full declaration signature, docstring, public import,
   universes, instances, and surrounding commands are byte for byte unchanged.
   There are no other delivered modules, new declarations, or change records.
2. Proof validity: PASS. Independently compiled the module through `lcompile.py`
   without errors or warnings. Compiled a scratch copy with
   `#print axioms Algebra.Extension.smooth_conormal_sequence_exact`; the result is
   exactly `propext`, `Classical.choice`, and `Quot.sound`, with no `sorryAx`.
   Read the complete proof and its Mathlib lifting, infinitesimal-bijection,
   difference-factorization, and exactness lemmas. No forbidden declaration or
   hollow definition occurs, and no holes remain or are introduced.
3. Split statements: PASS (none). No split-off statement, helper theorem, or new
   node was added. Edge cases introduce no hidden hypotheses: for `A = B` and
   the identity structure map the conormal map is the identity and the
   differential module is zero; for `C` the zero ring all displayed modules are
   zero. For polynomial `B = A[X]` with evaluation to `C`, the variable contributes
   the expected differential summand. The proof makes no nontriviality, field,
   characteristic, or common-universe assumption.
4. Route and pruning: PASS. Independently searched Mathlib with launcher grep
   `conormal|Cotangent.*injective|Cotangent.*exact` and Loogle
   `Algebra.Extension.Cotangent.map, Function.Injective`, and searched the
   repository for `conormal_sequence_exact`, `06A9`, `06A7`, and cotangent-map
   injectivity. Found no direct replacement of this theorem; flat base-change
   and localization results have different hypotheses and maps. The existing
   proof already uses Mathlib for lifting, the derivation factorization, and
   right exactness. Its sole import, `Mathlib.RingTheory.Smooth.Basic`, supplies
   the signature's `Algebra.Smooth`, so its `public import` is necessary.
   All three old proof dependencies remain mathematically used; none is pruned.
   Read `dag/units/sk-thm-p1.json` including `realized`: this item is below the
   unit's realized statements and steps, all of which remain unchanged.
5. DAG agreement: PASS. Read the item's node and its three dependency records.
   The five-step argument and `proof_origin` still describe this proof: induced
   maps, square-zero lifting, a conormal left inverse, derivation factorization
   for middle exactness, and surjectivity. The square-zero-lifting dependency is
   a Mathlib leaf recorded as `FormallySmooth.comp_surjective`; the actual
   `liftOfSurjective` is the same lifting property packaged for an arbitrary
   surjection with nilpotent kernel. Here the kernel square is explicitly zero.
   Surjectivity uses Mathlib's right-exact conormal sequence and vanishing of
   differentials for the surjection `A → C`, implementing step 1. No node-field
   or route correction is required.

Second reading changed only this report by adding the independent checks and
verdicts. The Lean proof is correct as delivered and has been retained verbatim.
