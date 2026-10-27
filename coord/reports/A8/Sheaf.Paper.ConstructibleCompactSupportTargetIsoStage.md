## What changed

Reduced `constructible_compact_support_target_stage_comparison` to finite rational geometry,
and wrote the common-stage assembly and its transition compatibility in Lean. The item
keeps its statement and both public imports. Its new proof import is
`Sheaf.Paper.CompactSupportTargetRationalComparison`, together with the proved generic
`Sheaf.CategoryTheory.StageSystemTargetComparison`.

The new module states `compact_support_target_rational_comparison` on ring and field
systems alone. Its conclusion uses finite rational operations and rational pullback;
it has no closed operation, common-stage inclusion, or common-stage comparison.
`rationalOperationTransition` explicitly conjugates the existing rational q comparison
by the specified stage-transition identifications.

The item constructs each comparison by composing the inverse common comparison of S,
the included finite rational comparison, the pullback inclusion comparison, and the
common comparison of S' whiskered by pullback. The generic module exports the completely proved `CategoryTheory.StageSystem.assembleTargetComparison`.
A private isomorphism constructor and its private lemmas paste the transition
squares, compute the image of a transition under a stage morphism, assemble the whole
family, relabel scalar transitions, and extract the common-system transition law.
Private `import all` declarations and local transparency controls identify the
coefficient instance diamonds without changing shared definitions or attributes.
No existing dependency module is changed.

## Proved and sorry left

One original hole is reduced:
`WeilConjectures.ConstructibleExceptionalCoefficients.constructible_compact_support_target_stage_comparison`
(node `lem-sf-constructible-compact-support-target-stage-comparison`). The item has zero
remaining holes. The generic assembly and every private helper are proved; the isomorphism constructor
contains no proof hole. The generic module has zero holes.

Validation: the final import-ordered server compile passed for all three modules:
StageSystemTargetComparison in 3.1 s, CompactSupportTargetRationalComparison in 17.6 s,
and the assigned module in 50.7 s. The assigned theorem signature is byte-for-byte unchanged.
No profiling or diagnostic options remain.

One hole is added and remains:
`WeilConjectures.ConstructibleExceptionalCoefficients.compact_support_target_rational_comparison`
(node `lem-sf-compact-support-target-rational-comparison`). Its whole proof is `by sorry`.
This is a decomposition: one upper hole closed, one finite rational hole added, net zero.
The geometric finite/integral/rational argument is still required. No claim of an
axiom-free geometric proof or a net decrease in the targets' hole count is made.

## No longer needed

Both original public imports remain, and no existing node or module is pruned.
The new finite rational module omits a redundant direct import of DerivedPullbackTensorHom,
which its necessary CommonStagePullbackNormalizedDescent import already exports. The original geometric
dependencies (proper derived pushforward composition, isomorphism-field transport,
compactification coherence, prescribed integral compact-support reductions, and finite-free
completed scalar comparison) remain needed by the finite rational comparison. The coefficient
system and common-stage category definitions remain needed by the proved assembly. The
item's direct proof dependencies now describe this division explicitly. Normalized
common-stage pullback descent is used as an existing proved categorical tool.

## Where the brief, the DAG or earlier work was wrong

The previous split still bundled geometric finite rational comparison with the additional
passage to the closed-coefficient functors and their transition laws. This delivery proves
that passage, including the stage-morphism transition computation and the full comparison
square; it does not replace the obligation by an alias or an extra hypothesis on a System.
The remaining statement concerns the earlier finite rational categories and only the
ring/field projections. It does not assume or assert the original closed-stage conclusion.

Searches found no ready-made target comparison: Mathlib provides ordinary sheaf pushforward
composition and generic natural-isomorphism constructors, while the project supplies proper
composition, field transport, compactification refinement, and normalized pullback descent.
The blueprint's cited final exceptional-adjunction sentence does not itself contain the
“finite-stage and common-stage comparison paragraphs” attributed by the old docstring;
the detailed proper/open and coefficient argument is an agent expansion of that sentence
and of the inherited proof plan, recorded as such. The unit route is unchanged. The first complete combined file typechecked but took 63 s.
After local transparency controls and a small isomorphism constructor removed repeated
unfolding, the remaining self-contained categorical calculation was moved to the generic
module so every delivered file can compile separately within the 60 s limit.

## New nodes

`lem-sf-compact-support-target-rational-comparison` records the finite rational geometric
comparison with its coefficient square, its complete proof in words, the actual searches,
and the canonical transition-conjugation definition. This is a strictly earlier coefficient
step: closed/common-stage assembly is proved in the assigned module. The declaration is
used only to obtain finite rational comparison maps, and no definition chooses arbitrary
data from its unproved existence claim.

`lem-sf-stage-system-target-comparison` records the completely proved categorical assembly
in `Sheaf.CategoryTheory.StageSystemTargetComparison`. It contains no geometry or coefficient
choice: the two inclusion-cone equations and the finite scalar square are its explicit
hypotheses. Its proof constructs the comparison and pastes the three squares. This is
extracted proved code, not another split-off obligation. No change record is needed: no
existing public declaration, instance, attribute, signature or public import changes.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.CategoryTheory.StageSystemTargetComparison": "4808fa9c6dd9d8e0e55c5f70950af1efa63cf42b", "Sheaf.Paper.CompactSupportTargetRationalComparison": "c6894157c6bdbd7c0d014a2ba7936495b04c1458", "Sheaf.Paper.ConstructibleCompactSupportTargetIsoStage": "7fe9966a7630415b6be6fed93d2be6a0fd6dcebe"}, "results": {"Sheaf.Paper.ConstructibleCompactSupportTargetIso": {"hash": "f16d0d15f1ad9f5bd295e86c5c590d90e52a37f3", "status": "OK"}}, "seconds": 21, "time": "2026-10-28T04:36:23+0800", "transitive": 0, "version": 1}
```

## Second reading by A8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
