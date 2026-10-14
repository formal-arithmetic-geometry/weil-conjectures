## What changed

In `Sheaf.AlgebraicGeometry.StandardSingleOpenRelativeArrow`, replaced the proof of
`AlgebraicGeometry.standardSingle_open_relative_arrow` by a compiling reduction.
The supplied signature and existing docstring are unchanged. The scheme isomorphism is
constructed by pullback symmetry, pullback pasting and pullback.map, with both
projection equations proved. Private helpers prove normalization and invertibility
of the pinned single comparison along any open immersion. Both coefficient
isomorphisms are constructed from those comparisons and literal tensor composition;
their normalization equations are proved. Source-coordinate conjugacy then gives
the commuting arrow square and its isomorphism.

Added proof imports for the new coefficient equation, pullback pasting, generic
left-derived invertibility and the source-library exact restriction instance.
Added `Sheaf.AlgebraicGeometry.SingleOpenTensorCoefficientCoherence` and its node,
and updated the original node's proof route. The new theorem has no direct image,
base scheme, cartesian square or base-change map; it assumes normalized coefficient
maps and states just their pullback compatibility equation.

## Proved and sorry left

Closed the original textual hole:
`AlgebraicGeometry.standardSingle_open_relative_arrow`
(node `lem-pc-standard-single-open-relative-arrow`). Its proof is complete Lean.
The private normalization, open-immersion invertibility and inverse-cancellation
helpers are also proved without local holes.

Added one hole:
`AlgebraicGeometry.single_open_tensor_coefficient_coherence`
(node `lem-pc-single-open-tensor-coefficient-coherence`). This is a decomposition,
not a complete sorry-free proof: one original hole closed, one lower hole added,
net zero. No sorry remains in the original module. No data definition contains a
sorry or chooses an arbitrary object from an unproved existence assertion.

The two delivered modules compile individually in dependency order, without
warnings, via lcompile.py. The open comparison applies to arbitrary modules;
no flatness or quasi-coherence is imposed. Edge cases checked from the argument:
empty opens and zero modules use the same isomorphisms; Z=W uses isoOfLE with
reflexive inclusion. The coefficient lemma does not invert q or t comparisons,
so it does not incorrectly require arbitrary tensor pullback to be exact.

## No longer needed

No existing import was removed: StandardSingleBaseChangeMap and RelativeMVMaps
are needed by the unchanged signature, and DerivedBaseChangeSourceIso is applied.
The original node no longer uses separate proof dependencies
`def-pc-module-pullback`, `def-pc-derived-pullback`, or
`lem-pc-derived-direct-image-composition` as proof steps. The first two notions
remain needed by the statements and transitively imported definitions. The
standalone derived direct-image composition theorem is unnecessary here:
source-coordinate conjugacy already supplies the vertex comparisons.

No globally unreachable module is claimed. The proof does not need
RelativeMVOpenCoefficientTransport (which the original plan warned was cyclic),
SingleComplexOpenNestedComparison, StandardSingleBaseChangeTopRestrictionAux,
TensorSinglePullbackComposition or Picard.CanonicalSinglePullbackSquare. These
related interfaces were inspected but are not imported. The direct normalized
coefficient equation uses only the original single-map composition and tensor
composition associativity in its remaining proof plan.

## Where the brief, the DAG or earlier work was wrong

No statement error found. During the first dry run, deliver3.py fetched an
upstream base which had removed both the item's module and its node. The
initial read-only checkout contained them (E3 delivery), and the sandbox copy
was made before that fetch. The updated base also makes downstream.py report
"unknown module" for the item. This delivery preserves the supplied declaration
and records its reintroduction as a new module/node, with V4 provenance as the
current base requires. The independent reader should check whether the upstream
removal made this item unnecessary; no claim of target-closure progress is made.
The required change record is
`coord/changes/standardSingle_open_relative_arrow-reintroduction.md`.

 The original plan's separate derived direct-image
composition invocation is redundant once the proved source-coordinate conjugacy
is used. The remaining computation is only a coefficient equation: all geometry,
exact-open invertibility, coefficient data construction, mate transport and final
Arrow.isoMk assembly are now actual Lean. The unit record has no realized nodes
here; no unit statement or prescribed unit step is bypassed.

Searches actually run: LeanFinder for derived pullback on an open single returned
restrictFunctorIsoPullback; Loogle for isoOfLE returned its projection equations;
LeanSearch for the coefficient square was unavailable (HTTP internal error);
Loogle for isIso_of_isLeftDerivedFunctor_of_inverts returned the generic tool;
grep returned single-comparison and exact-functor APIs. Local rg inspected the
canonical single square, termwise composition and tensor composition associativity.
Blueprint search for "single coefficient" returned no nodes. Search results are
recorded in the new node; unavailable service is not an absence verdict.

## New nodes

`lem-pc-single-open-tensor-coefficient-coherence`, in
`dag/nodes/sec-picard-framework/lem-pc-single-open-tensor-coefficient-coherence.json`,
is the normalized coefficient equation of the original node's second step. It is
strictly below the original arrow isomorphism and omits all direct images and
base-change mates. Its source, proof in words, actual searches and exact Lean
signature are recorded. No supplied definition or statement changed and no forced adaptation is needed.

`lem-pc-standard-single-open-relative-arrow` is also present in the delivery,
now as a reintroduced node because the fresh upstream base removed the original
node and module. It retains the exact supplied statement, source, chapter, unit
and blueprint ancestry, and records the implemented proof route. Its change
record is `coord/changes/standardSingle_open_relative_arrow-reintroduction.md`.


## Second reading by V4

1. Interface check: both delivered module paths and both node paths are absent
   from the current read-only checkout. The requested diff therefore reports a
   missing original, rather than a changed signature. No existing repository
   module is delivered or adapted. I compared the reintroduced theorem's
   signature with the Old and New signatures in the change record and with its
   node's lean.statement (whitespace normalized); they agree. The prior module
   is no longer available for a byte-for-byte historical comparison, so I do
   not certify that historical claim. Verdict: a documented reintroduction with
   no change to a current existing declaration or target. Local rg finds no
   current importer or user of the removed module; no target-closure progress
   is claimed.

2. Proof check: compiled both delivered modules in dependency order using
   lcompile.py, with no error or warning. Scratch copies with #print axioms show
   cancel_single_maps uses only propext; single_normalize and single_open_iso
   use only propext, Classical.choice and Quot.sound. The two public theorems
   use those standard axioms plus sorryAx. Exactly one textual sorry remains,
   in single_open_tensor_coefficient_coherence, as reported. There is no axiom,
   unsafe, opaque, implemented_by, extern, hollow definition, or newly chosen
   data witness from an unproved existence assertion. The concrete pullback
   isomorphism and both coefficient isomorphisms are constructed in the proof.
   Verdict: the original theorem has a genuine Lean reduction; the delivery
   remains a one-for-one decomposition, not a complete sorry-free proof.

3. Split statement check: I checked the coefficient equation by postcomposing
   with Q_r(T_q N). Its explicit IsIso hypothesis permits the final cancellation;
   naturality, the four single-comparison composition equations and tensor
   composition associativity identify the resulting composites. In particular
   arbitrary alpha is sufficient: its normalization is used after mapping by
   L_k and postcomposing with the single comparison, so no uniqueness of alpha
   or invertibility of Q_i is silently assumed. Empty opens/schemes, zero N,
   identity maps and reflexive equalities introduce no extra hypothesis.
   Non-flat q and t are allowed because their comparisons are never inverted.
   The statement omits the original theorem's direct images, base scheme,
   cartesian base-change square and arrow-category isomorphism; it is strictly
   a part of that argument. Its docstring and node give its source and proof.
   Independent Loogle search for singleMapHomologicalComplex found naturality
   and composition tools; LeanFinder search for naturality of derived-to-
   underived pullback and composition found ordinary pullback comparisons;
   grep for singlePullback, singleMap naturality and leftDerived factorization
   found generic tools. Local rg and reading CanonicalSinglePullbackSquare,
   CanonicalSinglePullbackComposition, PicardTermwiseSingleMapComposition,
   OpenPinnedSingleDegreeZeroCounitIso and the top-restriction auxiliary module
   found related interfaces, but no identical normalized literal-tensor
   equation. Verdict: true, needed and smaller; no direct replacement found.

4. Route and pruning check: the scheme geometry uses Mathlib pullback symmetry,
   pasting and map, exact-open invertibility uses the proved source restriction
   limits instance and Mathlib's left-derived invertibility theorem, and final
   conjugacy uses the proved DerivedBaseChangeSourceIso. Each proof import is
   used by one of these steps. Both public imports of the original module are
   needed by its signature. The coefficient module's public imports supply its
   signature; tensor associativity is correctly a plain proof import. The
   No longer needed section records the earlier plan dependencies discarded by
   this route; their old node is absent in the current checkout, which limits
   independent comparison with that earlier list. No current globally pruned
   module is claimed. sk-thm-picard-coherence has empty realized statement and
   step arrays, and neither delivered node realizes a prescribed unit step.
   Verdict: no unit route is bypassed and no further import pruning identified.

5. DAG check: opened both delivered nodes and their referenced modules. The
   original node's four steps match the concrete scheme construction, exact-
   open comparison, coefficient equation and source-isomorphism conjugacy in
   Lean. Its proof_deps are the union of those steps' uses. The new node's
   proof_deps match its documented single-map and tensor-associativity route.
   Both nodes have source, proof_origin, searches, provenance, chapter, unit,
   blueprint ancestry and matching Lean records. Verdict: consistent with
   the implemented reduction and remaining coefficient proof obligation.

Second reading changed only this report: recorded the independent checks,
axiom results and the limits of comparison after upstream removal. No Lean
statement, definition, proof, import or node was changed.
