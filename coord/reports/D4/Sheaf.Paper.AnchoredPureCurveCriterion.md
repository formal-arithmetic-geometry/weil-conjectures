## What changed

Completed the assembly proof of `WeilConjectures.anchoredPureCurveCriterion`, preserving
its entire signature and all definitions. The only residual step is isolated in the new
module `Sheaf.Paper.ClassicalRealizedAnchorEigenvalue` as
`WeilConjectures.classicalRealized_anchor_eigenvalue`.

The private helpers in the item specialize `commonStageWeilFiniteRealization` to a
one-vertex quiver, identify finite spectra with scalar-extended eigenvalues by
`LinearMap.charpoly_baseChange` and `Module.End.hasEigenvalue_iff_isRoot_charpoly`,
prove closed residue cardinalities exceed one, and cancel positive natural powers.
They then prove purity transfer from `LocalPower`, including the target presentation
and its residue embedding. The final proof chooses one covering curve at the anchor,
uses a single existing anchor eigenvalue to compare every supplied and further curve,
proves global purity, and establishes the logarithmic formula, nonvanishing and uniqueness.

Added private proof imports of `ClassicalRealizedAnchorEigenvalue`, `CommonStageWeilIterate`
and Mathlib's eigenspace/characteristic-polynomial comparison. No public imports change.
The DAG records the actual proof and the residual step.

Validation: source-only comparison confirms every existing declaration signature,
attribute/head, non-theorem body, and public import is unchanged. All five added
private helpers have complete proofs. The new node's Lean signature is verbatim.
The final item compiles cleanly in 20.0 seconds, with exit code zero and no warnings.
The residual lemma module also compiled successfully. The delivery tool performs
the final compile and axiom/sorry probes.

## Proved and sorry left

Original item: one sorry, `WeilConjectures.anchoredPureCurveCriterion`
(node `lem-zl-anchored-pure-curve-criterion`). Its proof body is now complete.

Added one sorry: `WeilConjectures.classicalRealized_anchor_eigenvalue`
(node `lem-zl-classical-realized-anchor-eigenvalue`). This is precisely the first step:
existence of a punctual eigenvalue at one closed point for a nonzero classical lisse sheaf.
It has no curve, family, local power, purity, weight, or uniqueness hypothesis or conclusion.
The theorem is not an equivalent reformulation of the criterion. Its docstring and node
explain the fibre equivalence, normalized operator comparison and finite-stage passage.

Thus this is a decomposition: one upper hole closed and one strictly smaller hole added;
net hole change zero. The remaining six steps are proved, including the spectral power
transfer; no other sorry remains in the delivered item and all private helpers are proved.

## No longer needed

Removed the item's private imports of `Sheaf.Paper.GaloisLisseRepresentations`,
`Mathlib.LinearAlgebra.Eigenspace.Triangularizable` and
`Mathlib.AlgebraicGeometry.Noetherian`: the classical nonzero-fibre/eigenvalue argument
is now the new lemma's responsibility. Its node retains
`cor-galois-lisse-representations`, `lem-zl-classical-local-frobenius-iterate-comparison`,
`lem-zl-alg-closed-endomorphism-eigenvalue`,
`lem-pod-separated-finite-type-base-change` and
`lem-weil-pbc-finite-type-over-noetherian`; none is globally withdrawn.
The old direct `cor-galois-lisse-representations` tool-use approval is removed from
the parent, since only the new lemma uses it. The reader should retain the same
previously reviewed generic-tool justification for that new lemma.

`lem-a1-real-logarithm-power` is no longer needed by the proof: positive natural-power
cancellation yields the norm formula directly, so no `rpow_logb` inversion step is used.
No source-library declarations or modules are removed. No entire module is claimed
pruned from the targets' closure.

## Where the brief, the DAG or earlier work was wrong

The original route is mathematically sound and is preserved. Its declarations do not
package the final passage from a nonzero classical fibre and normalized comparison to
an actual finite-presentation `SfPunctualEigenvalue`; that step is isolated explicitly.
The pointwise power calculation also needs a finite presentation of the restricted
Weil object, since `LocalPower` quantifies over such presentations. The existing
`commonStageWeilFiniteRealization` supplies this and is now an explicit proof dependency.
It is a generic finite-diagram descent tool from `lem-wf-common-stage-weil-iterate`,
not a replacement for any step of the unit's curve route; approval of that tool citation
is requested from the independent reader/maintainer. Its module was checked before use.

Edge cases checked: coinciding anchor and second point; degree one; residue cardinality
two; repeated eigenvalues and zero roots (charpoly retains them); zero fibres (the
pointwise assertion is vacuous); empty test family (excluded by covering the anchor);
zero sheaf (excluded only for anchor spectrum and uniqueness). Power transfer proves
nonvanishing from positive curve modulus, without assuming Frobenius invertibility.
The new lemma cannot be used for a disconnected base or zero carrier, and retains
exactly those exclusions. All original universes are preserved.

## New nodes

`lem-zl-classical-realized-anchor-eigenvalue` in
`dag/nodes/sec-deligne-laumon-general/` states only existence of an anchor eigenvalue,
with a full natural-language proof, source, three executed Mathlib searches, and the
Lean attachment to `Sheaf.Paper.ClassicalRealizedAnchorEigenvalue`. Search found
`Module.End.exists_eigenvalue`, which supplies the final linear-algebra step but not
the classical/normalized/finite-stage comparisons. No definition or existing public
statement was changed. The source scanner notices the three local `omit ... in`
commands used only on proved private helpers. Their scope and lack of downstream
effect are recorded in `coord/changes/D4-anchored-private-helper-binders.md`.
No consumer adaptation is required.

## Second reading by D4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
