## What changed

Proved `AlgebraicGeometry.ProEtale.directImageCTFEtaleOrigin` in
`Sheaf.Paper.SfDirectImageCTFEtaleOrigin`, with its statement unchanged.
The proof follows the existing etale direct-image and comparison route. It converts
the finite-ring constructibility conventions, applies `directImageCTFNonproper`,
passes from the bounded-below comparison to the unbounded direct images, and uses
the canonical intrinsic realization comparison to obtain the actual output object.
The ordered Tor interval is transferred using `comparison_torAmplitudeIn_iff`.
Its invariance under isomorphism is proved directly from the universal resolution test.

For the last conjunct, exact comparison identifies all output cohomology sheaves
with the intrinsic comparison of the etale cohomology. Scalar restriction and its
canonical realization isomorphism give constructibility. Their support lies in the
same finite integer interval. The two private helpers are completely proved.
The node's proof and dependencies now describe this implementation.

Private proof imports were added for canonical realization transport, scalar
restriction constructibility, its realization isomorphism, comparison of etale
constructibility conventions, fixed-coefficient constructible sheaves, and the
unbounded/bounded-below compatibility. Existing public imports are preserved.
No other Lean module, declaration signature, or definition was changed.

The source-library stability theorem with the blueprint's name was inspected: its
fixed-coefficient conclusion does not include the required intrinsic object and
intrinsic constructibility. The existing nonproper corollary avoids repeating its
coefficient-exponent argument. LeanFinder, Loogle and Mathlib grep searches were
run; no direct Mathlib match supplied the intrinsic conclusion.

## Proved and sorry left

Closed 1 hole: `AlgebraicGeometry.ProEtale.directImageCTFEtaleOrigin`
(node `cor-sf-direct-image-ctf-etale-origin`). Added 0 holes; split off 0 statements.
There are no remaining `sorry`s in the delivered module. Both private helpers,
`boundedConstructible_iff` and `intrinsicTor_of_iso`, have complete proofs.

The module compiles cleanly through `lcompile.py` (10.0 seconds).
An explicit axiom check reports `propext`, `Classical.choice`, `Quot.sound` and
`sorryAx`; the latter comes from existing imported theorem obligations, not any
new hole in this delivery. Its proof uses existing library
interfaces, including the normalized intrinsic derived direct-image comparison;
this delivery does not claim to close their transitive proof obligations.

## No longer needed

Removed the redundant private import `Sheaf.Paper.IntrinsicFiniteTorsionConstructibility`
(the definition remains available through the existing public finite-Tor import).
Removed the private import `Sheaf.Paper.ProEtaleConstructibleOrigin` and the proof
dependency `lem-sf-proetale-constructible-origin`. Only the forward preservation of
constructibility is needed, so the full equivalence and reverse descent argument
are avoided. Direct cohomological transport, using existing proved fixed-scalar
constructibility and scalar restriction, gives the required intrinsic predicate.
No module is withdrawn, and no declaration is removed from the adopted source tree.
The etale direct-image corollary, comparison-direct-image theorem and Tor-interval
comparison all remain used; the unit's etale/comparison route is preserved.

## Where the brief, the DAG or earlier work was wrong

No statement correction was needed. The original plan suppressed the distinction
between fixed-coefficient and intrinsic direct images: the proof now explicitly
inserts their uniquely normalized canonical realization comparison. Its final use
of the full constructible-origin equivalence was stronger than necessary.

The existing generic interfaces from `def-sp-finite-intrinsic-direct-adjunction`,
`src-right-derived-functor-plus-compatibility`, the exact homology comparison,
scalar restriction and constructibility comparison are used only as categorical
and coefficient-presentation tools; they do not replace the unit's route. No new
tool approval is written into the DAG.

## Second reading by D3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
