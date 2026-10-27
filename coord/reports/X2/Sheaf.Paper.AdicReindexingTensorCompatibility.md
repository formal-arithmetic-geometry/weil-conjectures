## What changed

Replaced the `sorry` in
`WeilConjectures.AdicQbarRealization.normalized_reindexing_tensor_compatibility`
by a complete descent argument from a square on integral objects at one finite
coefficient field. Added the proof imports
`Sheaf.Paper.AdicReindexingTensorIntegral` and
`Sheaf.Paper.DerivedPullbackTensorIso`; the existing public import and theorem
signature are unchanged. No other existing module is changed.

The proof constructs the two routes as natural transformations of bifunctors.
The common-stage comparison is supplied by `derivedPullbackTensorIso`, together
with its equality to the prescribed canonical map. For arbitrary M,N it chooses
their coefficient compositum and the two specified `isoToStage` isomorphisms.
Every rational object is the rationalization of its underlying integral object
(the raw localization introduces no new objects). The integral lemma at this
one field gives equality of components there. Naturality and cancellation of
the image of the product isomorphism give the original equation at M,N.
The private proved helper `app_eq_of_iso` performs that cancellation.
The new statement module compiled in 11.0 s; the complete parent proof compiled
in 17.9 s with no diagnostics, both through `lcompile.py`.

## Proved and sorry left

This is a decomposition, not a net proof of the mathematical obligation.
One original hole is closed and one strictly restricted hole is added; net zero.
The original module now has zero holes. Its theorem
`WeilConjectures.AdicQbarRealization.normalized_reindexing_tensor_compatibility`
is completely proved from the new integral lemma and existing declarations.

The only added and remaining hole is
`WeilConjectures.AdicQbarRealization.normalized_reindexing_tensor_integral`
in `Sheaf.Paper.AdicReindexingTensorIntegral`, node
`lem-sf-adic-reindexing-tensor-integral`.
It fixes one coefficient field E, assumes normalization only at E, and asserts
the square only on rationalizations of two integral objects at E. It has no
coefficient-stage enlargement or descent to arbitrary common-stage objects.
Its docstring and node describe the K-flat, balanced-section and whole
quotient-completion calculation, including the zero shifted coordinate.
The statement is not the parent with its universal normalization hypothesis
repackaged: it requires only one field's normalization, and the parent proof
actually performs the compositum choice and isomorphism transport.

Edge cases checked mathematically: zero integral objects and the empty scheme
have the same zero-map square; repeated coefficient stages are allowed by the
specified stage system and raw localization; the argument does not assume
faithfulness of coefficient extension, flatness of arbitrary constructible
objects, or that finite reductions detect an arbitrary completion morphism.

## No longer needed

No existing imports or modules are removed or withdrawn. The parent no longer
uses `lem-fix-constructible-tensor-completion` and
`lem-pur-cochain-pullback-tensor-coherence` directly; both remain required by the
fixed-integral-field calculation and are listed on its new node. They are not
claimed as globally pruned. `lem-pur-derived-pullback-tensor-iso` remains a direct
parent dependency to obtain the canonical natural comparison. No blueprint unit
statement or proof step is bypassed; the item's unit has empty realized fields.

## Where the brief, the DAG or earlier work was wrong

No false statement or interface defect was found. The existing three-step plan
combined a fixed-field integral calculation with a separate, generic descent
argument. This delivery formalizes the latter. The new hole is the former,
with precisely one field's normalization hypothesis, rather than another
statement about arbitrary common-stage objects.

## New nodes

`lem-sf-adic-reindexing-tensor-integral`, in
`dag/nodes/sec-six-functors/lem-sf-adic-reindexing-tensor-integral.json`,
records the fixed-field integral square in the new module
`lean/Sheaf/Paper/AdicReindexingTensorIntegral.lean`. Its source is
Bhatt--Scholze Proposition 6.8.14, Remark 6.8.15 and Lemma 6.5.5,
with HRS Lemma 7.9; the exact normalization computation is explicitly identified
as an agent refinement of those results. Three kinds of actual Mathlib search
found only generic monoidal and naturality tools. No change record is needed:
only the assigned module, its own node, and the new module/node are changed.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.AdicReindexingTensorCompatibility": "3fc3054fe0f10bb8ef1b4e3e0e8a52cf2f9b19c7", "Sheaf.Paper.AdicReindexingTensorIntegral": "ba5677c32b2c89b2f65b51784a0634424e0e6f39"}, "results": {"Sheaf.Paper.AdicReindexingTensor": {"hash": "6135e6ffbf3326dd6fb96a1ddd6a2c424008f50e", "status": "OK"}}, "seconds": 85, "time": "2026-10-28T05:14:47+0800", "transitive": 0, "version": 1}
```

## Second reading by X2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
