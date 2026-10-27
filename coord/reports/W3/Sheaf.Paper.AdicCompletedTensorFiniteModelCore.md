## What changed

Proved `WeilConjectures.AdicQbarRealization.completed_tensor_finite_model_core`
without changing its statement or the `CompletedTensorFiniteModelCore` structure.
The item module and its node change, and the proved generic total comparison is
added as `Sheaf.Paper.ProEtaleScalarTensorBalance`, with its own node. Its theorem is
`AlgebraicGeometry.Scheme.pbc_tensor_balance_exists`; all its local helpers are private
and proved. No other existing module changes.

The proof transports the existing ordinary scalar tensor comparison to the recorded
`pbcExtend` functor, forms its signed total comparison, and proves the normalized
section formula, first at scalar 1 and then by linearity for every scalar. Independent
coefficient change of rings proves K-flat preservation. The product good-complex
localization and `tensorComparisonDescent` construct the derived comparison with
exactly the required representative equation. The supplied completion presentation
is used as given; no new completion or arbitrary existence witness is introduced.

The proof uses existing generic scalar/tensor results as tools: the independent
ringed tensorator construction, K-flat change of rings, total comparison naturality,
and representative descent. Existing private proved helpers are accessed by proof-only
`import all` imports. The finite cochain calculation is proved for an arbitrary ring-sheaf
map first, then specialized to the recorded coefficient map; this avoids unfolding the
completed coefficient-ring construction during the section calculation.

Validation: the final `lcompile.py --all` check compiled the generic scalar module in
55.8 s, the item in 1.5 s, and its unchanged direct importer
`Sheaf.Paper.AdicCompletedTensorFiniteModelExistence` in 4.5 s, without warnings.
The unchanged importer was copied only for this check and removed from the packet.
All delivered Lean files contain zero `sorry` tokens, and the original structure and
theorem signature were checked verbatim against the source.

## Proved and sorry left

Closed 1 of 1 original holes:
`WeilConjectures.AdicQbarRealization.completed_tensor_finite_model_core`
(node `new-sf-adic-completed-tensor-finite-model-core`).

Added holes: none. Remaining holes in the item: none. Split-off statements: none.
Existing dependency proofs retain their own axioms and obligations; this is a proof
from the published declarations, not a claim that the entire target closure is closed.

## No longer needed

Removed `public import Sheaf.Paper.RationalRealizationTensorComparison`.
Neither its theorem `rational_realization_tensor_comparison` nor its normalization
system is used. The existing direct importer already imports that module separately.
No declaration or module is withdrawn.

The original planned dependency `lem-pur-cochain-pullback-tensor-coherence` is not
needed: scalar tensor normalization follows from the ordinary scalar comparison and
the direct signed-total construction, without general composition, symmetry, or
coefficient-change coherence. `lem-fix-constructible-tensor-completion` is not used
to obtain a presentation, since the item takes one as an argument. Its presentation
interface remains necessary through the existing public statement import.

The general derived ringed-topos monoidality theorem is not applied: only its proved
total-chain construction is used, followed by the smaller explicit descent theorem.
No proof dependency or unit step is bypassed above the item's scalar-extension role.
No additional module is claimed globally unreachable merely from these local prunings.

## Where the brief, the DAG or earlier work was wrong

The previous split left a scalar-extension core which the existing ordinary tensor,
K-flat change-of-rings, localization, and representative descent APIs can prove.
No further proof obligation is split off. The fixed completion argument makes a fresh application
of constructible tensor completion unnecessary. The original public rational
realization import was unrelated to this proof.

The proof checks arbitrary scalar maps, including nonflat maps: K-flat preservation
uses exact restriction and tensor cancellation, not flatness of the coefficient map.
Zero complexes and empty schemes require no exceptions. All original assumptions
and the fixed completion presentation are preserved.

## New nodes

`new-sf-proetale-scalar-tensor-balance` is the proved ordinary/total part of the core,
in `Sheaf.Paper.ProEtaleScalarTensorBalance`. It records a normalized cochain comparison
for an arbitrary coefficient-sheaf map, without the completion, K-flat, derived, or
representative parts of the item. It adds zero holes. Separating the proved calculation
keeps each file within the fixed compilation limit after local opacity and component
equations reduced repeated unfolding. No shared definition or attribute is changed.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.AdicCompletedTensorFiniteModelCore": "13816da4798b80161d5e37796c62c0078f6696a4", "Sheaf.Paper.ProEtaleScalarTensorBalance": "18988a90711eb4d64fa45e458d6524f1b9603a6a"}, "results": {"Sheaf.Paper.AdicCompletedTensorFiniteModelExistence": {"hash": "893b8cf937f3df5d0dd9cfb168b68b7d868b8b21", "status": "OK"}}, "seconds": 71, "time": "2026-10-28T05:37:51+0800", "transitive": 0, "version": 1}
```

## Second reading by W3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
