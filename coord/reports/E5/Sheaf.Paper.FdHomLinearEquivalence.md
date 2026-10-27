## What changed

Replaced the proof of `WeilConjectures.fdHomLinearEquivalence` in
`Sheaf.Paper.FdHomLinearEquivalence`. Added proved private helpers for
stage Hom bijections, full faithfulness on the actual pair quotient, and an
explicit equivalence with specified preimage objects and counit. A fully proved generic
assembly theorem keeps concrete coefficient-category elaboration out of the proof
steps; the public theorem specializes it using the two published scalar-action
formulas.

The proof locally reduces the stage-system functor object projection and keeps
the scalar-localization category and preadditive instances irreducible during
elaboration. These local attributes change no exported attribute. The only added
import is the private proof import `Mathlib.CategoryTheory.Adjunction.Limits`,
used for preservation of products by equivalences.

The proof uses the actual `StageSystem.Morphism` transport and inclusion API.
It constructs the additive stage equivalences, proves quotient full faithfulness
without assuming faithful transitions, establishes essential surjectivity at each
original field label, and proves Omega-linearity by computing the published scalar
actions at a finite field containing the scalar. It then constructs all remaining
Hom and chosen-inverse formulas. The existing declaration signatures are unchanged.
The theorem node's proof plan is updated to record these implementation steps.
Binary products are supplied explicitly from the published source pretriangulation,
avoiding instance search through the distinct generic pair preadditive structure.

## Proved and sorry left

Closed: `WeilConjectures.fdHomLinearEquivalence` (one original hole).
Added holes: none. Remaining holes in delivered modules: none.
All ten private helpers, including the generic assembly theorem, have complete
proofs. Existing imported theorem holes are unchanged and are not counted as
holes closed by this delivery.

## No longer needed

No imports are removed. No dependency nodes or modules are withdrawn. All four
declared proof dependencies remain used. The finite-field datum, characteristic
inequality, exactness and shift comparison hypotheses are unnecessary for this
Hom/linear argument but remain in the published theorem signature.

## Where the brief, the DAG or earlier work was wrong

No mathematical error found. The source pair category's published preadditive
structure is defined via colimit coordinates, while the upstream generic one uses
representatives directly. The proof obtains additivity from preservation of binary
products by the proved equivalence, so it does not assume these implementations are
definitionally equal. In the latest blueprint, the trace definition is under
`sec-fourier-transform/sk-cor-plancherel/def-fd-trace-function.md`; the DAG's historical
`sk-def-trace` unit has no realized statement or steps, and its route is untouched.

## Second reading by E5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
