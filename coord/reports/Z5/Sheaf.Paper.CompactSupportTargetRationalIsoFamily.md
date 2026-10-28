## What changed

Proved `WeilConjectures.ConstructibleExceptionalCoefficients.compact_support_target_rational_iso_family`
without changing its signature or its public imports. The proof compares completed
proper/open functors through a common compactification refinement, transports the
proper target along the inverse isomorphism, restricts to the recorded constructible
functors, and localizes their integral natural isomorphism. It then conjugates by
the two `RingSystem.rationalLeft` identifications at each finite coefficient stage.

Added the proved module `Sheaf.Paper.CompletedDirectImageTargetIso`, containing
`WeilConjectures.completedDirectImageTargetIso`. Its proof identifies module direct
image with exact sectionwise inverse image by uniqueness of right adjoints, checks
the completed coefficient map on every finite quotient, and derives the comparison.
The proof reuses the proved private `sectionwiseModuleAdjunction` and
`sectionwiseConstantDirectMap` helpers from `Sheaf.Paper.IsomorphismDerivedPullback`
through a proof-only `import all`, supplies the exactness instances explicitly,
and uses the existing site adjunction in
`Sheaf.AlgebraicGeometry.ProEtaleIsomorphismInverseImage`. No adopted source
file was changed. Added proof-only imports and updated the item's DAG proof route.

The proof uses `lem-zl-qcqs-completed-refinement` as a tool from the Deligne--Laumon
chapter: its hypotheses are exactly the qcqs finite-type hypotheses available here.
The older recorded identification in the integral coefficient comparison requires
separated structure maps and a finite-Tor input, and cannot be used directly for
this statement. The scalar-localization component lemma and raw isomorphism pullback
comparison supply the other existing tools; no approval fields were added.

## Proved and sorry left

Closed the original one hole in
`WeilConjectures.ConstructibleExceptionalCoefficients.compact_support_target_rational_iso_family`
(node `lem-sf-compact-support-target-rational-iso-family`). Added zero holes.
`WeilConjectures.completedDirectImageTargetIso` is proved, including all private helpers.
There are zero `sorry` declarations in the delivered Lean files. This is a proof
from existing project declarations, including the existing completed-refinement and
pullback-comparison obligations, rather than a further decomposition of the item.

Validation: `lcompile.py --all` compiled both delivered modules cleanly against
published artifacts, in 16.2 seconds for `CompletedDirectImageTargetIso` and 16.8
seconds for the item. Both transparency-respecting elaboration settings remain
true; no heartbeat or compile limit was raised.

## No longer needed

Removed the erroneous self-dependency and the sibling
`lem-sf-compact-support-target-rational-coherence` from this node's proof route.
Coherence is not required for the stagewise existential family; it remains required
by the parent comparison and is not globally pruned. The normalized common-stage
descent import is retained as an existing public interface, but its transition
normalization theorem is not used in this proof. No existing module is withdrawn,
and no public import or adopted source declaration is removed.

## Where the brief, the DAG or earlier work was wrong

The original node's only proof step cited itself and the coherence sibling. This
was a cyclic plan rather than a proof of the family. Replaced it by the actual
refinement, target transport, and localization steps. No statement or definition
repair is needed. The unit's realized statement and proof steps are unchanged.

## New nodes

`lem-sf-completed-direct-image-target-iso` records a fully proved comparison on the
entire completed-coefficient derived category, without compact-support family data
or constructibility hypotheses. Its identity and empty-scheme cases are covered
by the site equivalence and functorial direct-image compositor. It is a genuine
proper-map target-transport step, not the item restated under a new name. There are
no change records because no existing signature, definition, attribute, or public
import changes.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.CompactSupportTargetRationalIsoFamily": "db4dd961ed68579ac192e3124a680e6c9aa2ebd6", "Sheaf.Paper.CompletedDirectImageTargetIso": "da8f8a15ef910102b64a9c3fcb72649bbcf7181a"}, "results": {"Sheaf.Paper.CompactSupportTargetRationalComparison": {"hash": "e13b8312b2e2d7788761b30c6cf6e0dd560a149a", "status": "OK"}}, "seconds": 71, "time": "2026-10-28T08:15:09+0800", "transitive": 0, "version": 1}
```

## Second reading by Z5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
