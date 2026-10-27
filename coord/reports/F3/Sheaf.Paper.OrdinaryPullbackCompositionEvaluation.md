## What changed

Filled `WeilConjectures.PullbackCompositionTransport.ordinaryCompositionEvaluation` in
`Sheaf.Paper.OrdinaryPullbackCompositionEvaluation`, preserving both public signatures,
the definition of `ordinaryEvaluation`, and all public imports. Added proof-only
imports of `WeilConjectures.Mathlib.CategoryTheory.Adjunction.Mates` and the new
`Sheaf.Paper.OrdinaryPullbackEvaluationCalculus`, together with the Mathlib
weakly-etale and morphism-property over-adjunction modules used by the section proof.

The proof obtains both existing compositor mates and their section formulas, checks
that ordinary direct-image evaluation is the identity on sections, and proves that
the direct-image mate square commutes by the common fibre-product restriction formula.
Fully proved private adjunction calculations transport this equality to the left
adjoints. Cancellation yields the stated equation using the inverse evaluations.
The abstract calculations reuse the existing private proofs in
`Sheaf.Paper.FiniteSystemPullbackCoherence`; that module is not imported. No other existing Lean
module or definition changes. The item's node records these explicit proof
steps. The new supporting module gives a proved API for equality of the primitive
and integral direct images, direct-image evaluation, its identity action on sections,
and the primitive evaluation unit. An irreducible comparison wrapper prevents repeated
expansion of equality transports in the compositor calculation. The API is separated
from the compositor after profiling the coefficient-ring and sheafification reductions.

## Proved and sorry left

Closed the one original hole in
`WeilConjectures.PullbackCompositionTransport.ordinaryCompositionEvaluation`
(node `lem-pur-ordinary-pullback-composition-evaluation`). Holes added: zero.
Sorries left in the delivered Lean module: zero. No statements split off. Both delivered modules compile cleanly via `lcompile.py --all`: 
46.4 seconds for the supporting calculus and 54.9 seconds for the item.

The argument applies to arbitrary strict systems and arbitrary transitions, including
level zero (positive quotient exponent one). It imposes no geometric or normalization
hypotheses. All additional private lemmas and all statements of the supporting module are proved.

## No longer needed

None. All three declared dependencies remain used. All original public imports remain.
The search also found the abstract `adjunctionEvaluation_composition` theorem, but the
existing private evaluated-conjugate argument fits the chosen compositor normalization
more directly; neither that theorem's module nor FiniteSystemPullbackCoherence is added
as a proof dependency. No existing node or module is withdrawn or pruned.

## Where the brief, the DAG or earlier work was wrong

No mathematical defect found. The live server queue lists an ordinary one-hole proof
item, with no rework row or build-error file. The source's Tag 03D8 proof says the
composition isomorphisms are clear from the definitions; this delivery supplies the
explicit evaluation and mate calculation requested by the DAG. The unit record has
no realized statement or proof steps, and its route is preserved.

## New nodes

`lem-pur-ordinary-pullback-evaluation-calculus`, in
`dag/nodes/sec-smooth-purity/lem-pur-ordinary-pullback-evaluation-calculus.json`, records
the fully proved per-map section and unit API in `OrdinaryPullbackEvaluationCalculus`.
It has no holes. The direct comparison is explicitly `eqToIso` of the proved functor
equality, and the primitive unit property is extracted from its existing uniquely
normalized choice. No arbitrary data is selected. These are parts of the mate
argument, and do not assert compositor compatibility. No change records are required:
the only existing Lean module changed is the assigned item, with its public interface
preserved.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.OrdinaryPullbackCompositionEvaluation": "fd2334028d30846a0998313b46e18c52f55a6313", "Sheaf.Paper.OrdinaryPullbackEvaluationCalculus": "13792e00b7f07d5c631385eaca4d91785faab4a0"}, "results": {"Sheaf.Paper.NormalizedPullbackCompositionTransport": {"hash": "de844ad92275fc3c9a2b27130515209e8f7f3b6a", "status": "OK"}}, "seconds": 47, "time": "2026-10-28T01:44:56+0800", "transitive": 0, "version": 1}
```

## Second reading by F3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
