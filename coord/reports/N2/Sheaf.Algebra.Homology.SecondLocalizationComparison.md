## What changed

Removed the previous worker's `secondLocalization_comparison_restricted` and its
node: applying restriction along the identity of D merely restated the target.
The unchanged target now follows from an ordinary, unlocalized comparison square
and the existing proved `ModuleCat.scalarExtension_homology_square`.

Constructed the ordinary coefficient chain map concretely using the scalar-extension
adjunction, with a proved pure-tensor formula in the private helper
`exists_secondCoefficientMap`. Conjugating it with the models' ordinaryIso maps
produces the additive chain map. Tensor induction proves its square with both
ordinaryToLocalized maps and the supplied tau; the scalar tower equations identify
the coefficient in D. The library's scalar-extension theorem then proves the target.

Added `SecondLocalizationOrdinarySquare.lean`, containing only the smaller ordinary
comparison obligation. Both new imports of the target are proof-only imports.
Kept the existing include list and theorem signature exactly, using a scoped
unusedSectionVars linter setting because three inherited instances are unused by
this proof. No signature, visibility, definition, or target statement changed.

## Proved and sorry left

Closed original hole: `RingTensorCohomology.secondLocalization_comparison`.
Added hole: `RingTensorCohomology.secondLocalization_ordinary_square`, node
`lem-pc-second-localization-ordinary-square` in its own new module.
The private coefficient-map construction is proved and contains no sorry.
The rejected identity-restriction hole and its node were removed from the sandbox.

This is a decomposition, not a completed proof of the target's import closure:
one original hole closed and one strictly smaller hole added, net zero.
The remaining obligation is the ordinary derived-counit/cohomology square before
extension to D. It has no e, he, tau, ordinaryToLocalized or localizedComparison
in its statement, and requires no compatibility of any actions on D. Its input
chain map is fixed on all generators; it is not an arbitrary witness selected from
an unproved existence theorem. The actual chain map used in the target is constructed
by a sorry-free proof. Its derived-functor homology transport is substantial and
was not a hole that could be closed in a few minutes.

## No longer needed

No existing imports, nodes or modules are pruned. The old proof dependency
`lem-pc-second-localization-map` remains used. The rejected new node
`lem-pc-second-localization-comparison-restricted` is not delivered.

## Where the brief, the DAG or earlier work was wrong

The first worker's reduction was equivalent to the original conclusion, and its
new node even cited the original target as a proof dependency. It made no actual
reduction and did not update the target node's proof route. Replaced this with the
ordinary counit square as a strictly smaller step, and recorded the actual proof
route in the target node. The existing proved scalar-extension transport lemma was
available and removes the need to leave its formal adjunction argument open.

Checked the mathematical sources at
[Stacks 06Y6](https://stacks.math.columbia.edu/tag/06Y6) (derived tensor associativity
and independence of choices) and
[Stacks 0DJ8](https://stacks.math.columbia.edu/tag/0DJ8) (the affine localization
identity). The new statement isolates the counit compatibility part of that route.

## New nodes

`lem-pc-second-localization-ordinary-square`: the additive ordinary cohomology
comparison under flat B-to-Bp coefficient change, before scalar extension to D.
Its complete docstring explains the leftDerivedLift factorization, exact homology
transport, adjunction unit, comparison_eq substitution, and forgetful homology
coherence. Its node records the actual leanfinder, loogle and grep searches; no
exact prior theorem was found. No change record is needed because existing
statements and definitions are unchanged.

## Second reading by N2

1. Compared the target module with the repository by diff and declaration-table
   signature comparison. Verdict: every existing declaration signature and
   visibility is byte-for-byte unchanged; the target docstring and hypotheses
   are unchanged. The only existing declaration's proof is replaced. No forced
   adaptation or definition change is present.
2. Compiled both delivered modules locally in import order, and checked the source
   for sorry, axiom, unsafe, opaque, implemented_by and extern. Verdict: the sole
   new sorry is the public named ordinary-square theorem; none occurs in a
   definition or private helper. Checked #print axioms for the helper, target,
   and split theorem in a scratch copy: only the permitted standard axioms and
   sorryAx (the named ordinary-square obligation and open imported statements).
3. Read the new statement and its full proof docstring, and checked the zero
   complex, zero coefficient ring, identity coefficient map and nonflat D cases.
   Verdict: the coefficient chain-map formula uniquely determines the map because
   L.ordinaryIso is surjective and pure tensors generate. Exact B-to-Bp extension
   and the counit factorization supply the ordinary square, independently of D
   actions. No hypothesis asserting the desired localized square is hidden in
   the split. Searches of Mathlib, lean/Sheaf, and upstream WeilConjectures found
   generic derived-functor tools and the useful scalar-extension transport theorem,
   but no exact arbitrary-model ordinary square. The split is strictly a part of
   the argument; the identity-restriction restatement was removed.
4. Read the proof from the target down. Verdict: its final transport uses the
   already proved scalarExtension_homology_square; the ordinary coefficient map
   and coefficient-complex square are proved directly, leaving only the derived
   ordinary square. Both added imports are plain import and are used. No old
   proof dependency is dropped. Checked dag/units/sk-thm-picard-semicon.json:
   its realized statement and step lists are empty, and no protected unit route
   is bypassed or changed.
5. Read the target and new nodes against the Lean. Verdict: the target now cites
   the existing coefficient-map node, the ordinary-square node, and the proved
   scalar-extension-square node; proof_deps equals the union of proof-step uses.
   The new node carries its source, complete statement/proof, all required search kinds
   (LeanSearch was unavailable; leanfinder, loogle and grep ran), creation metadata, blueprint ancestry, chapter/unit, and verbatim
   Lean signature. No circular dependence on the target remains.

Changes made in this reading: removed the identity-restriction restatement;
constructed and proved the actual coefficient chain map; proved the coefficient
complex square and final scalar-extension reduction; added the strictly smaller
ordinary-square module/node; updated the target node and rewrote the report to
state the one-for-one decomposition honestly.
