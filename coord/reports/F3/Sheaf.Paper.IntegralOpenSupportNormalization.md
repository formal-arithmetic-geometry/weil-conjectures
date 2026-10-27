## What changed

Restored the assigned quarantined module without changing `OpenSupport` or the signature
of `WeilConjectures.IntegralSupportNormalization.openSupportNormalization`. Replaced its
single `sorry` by a construction of every field. Added private proved helpers for generic
adjunction-unit recovery, ambient completeness, finite identity direct image, the actual
finite reduction comparison, preservation of every reduction interval, and invertibility
of the whole-system compact comparison.

The comparison `dj` is the prescribed compact-support realization followed by
`openIdentity`. Its projection formula is proved by cancelling those actual isomorphisms
and applying the existing realization specification. Completeness holds for every ambient
complete object, using open quotient-Koszul completeness and its ringed identification.
Finite exact extension by zero and its homology comparison preserve the same interval,
including an empty interval. Shift compatibility is transported along `dj` through the
fully faithful constructible inclusion, and triangulatedness is transported for that
same shift structure.

Added the proof-only imports used for these arguments, and one new statement module
`Sheaf.Paper.IntegralOpenAdjunctionTransposeNormalization`. Its remaining obligation
is the normalized ordinary pullback presentation together with the whole-system
Hom-transpose square. The main proof obtains the system counit formula by specializing
that square to the counit, and its unit formula by specializing to an identity and
cancelling an invertible compact comparison. Joint conservativity of system evaluations
is used only to establish invertibility; no faithfulness on morphisms is assumed.

Updated the item's node proof and dependencies and added the node of the smaller
Hom-transpose obligation. No existing module besides the item was changed. All existing
public interfaces, definitions, targets and source-library declarations are unchanged.

Validation: both delivered modules compiled with `lcompile.py` without errors or
warnings and within its acceptance limit. The final main-file check reported 25.6 s.
Static comparisons verified the unchanged structure and theorem signature, matching
node statements and proof dependencies, and the 100-character line limit.

## Proved and sorry left

Original holes: one, `WeilConjectures.IntegralSupportNormalization.openSupportNormalization`.
Its proof is now complete relative to the imported declarations. The item's module has
zero remaining `sorry` bodies.

Added holes: one,
`WeilConjectures.IntegralSupportNormalization.openAdjunctionTransposeNormalization`,
node `lem-sf-open-support-adjunction-transpose`, in its own new module. Its body is exactly
`by sorry`; its docstring and node give the source and proof in words. It asserts only
the pullback comparison and compatibility of the two Hom transposes. Completeness,
interval preservation, finite reductions and their projection equation, shift
compatibility, and triangulatedness are proved in the main module and are absent
from the new statement. This is a decomposition (one upper hole closed, one strictly
smaller lower hole added), with net hole change zero among the delivered statements,
not a claim of an axiom-free proof of the target closure.

## No longer needed

No original import was removed: the original module publicly imported only
`Sheaf.Paper.IntegralSupportNormalizationData`, which remains necessary. No module
or declaration is withdrawn, and no adopted source-library declaration is removed.
The development imports `Sheaf.AlgebraicGeometry.SfIntrinsicRealizationTransport`,
`WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Coherence` and
`WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor` were removed
as redundant: the unchanged public normalization data already exposes them.

The item's direct proof no longer needs
`lem-sf-open-finite-constructibility-interval` or its module
`Sheaf.Paper.OpenFiniteConstructibilityInterval`: its interval field concerns only
cohomological support, which follows from the actual finite comparison and exact
extension by zero. It does not ask to reprove finite constructibility.

The original direct dependence on `lem-weil-strict-roos-comparison` for shift
normalization is replaced by `Functor.CommShift.ofComp` and its compatibility lemma.
This does not assert that Roos comparisons are unused elsewhere or in existing
realization constructions.

The original direct uses of `lem-sf-integral-open-reduction-comparison` and
`lem-sf-integral-immersion-pullback-normalization` are confined to the new Hom-transpose
node's mathematical proof; they remain necessary dependencies there. The old direct
ringed-open operation dependencies are supplied by the unchanged normalization data
and exactness constructions. No global pruning is claimed for these dependencies.

## Where the brief, the DAG or earlier work was wrong

The module was quarantined, not withdrawn. Its archived source was restored and its
Lean attachment retained. The old proof plan's completeness argument was expressed
on the constructible domain, whereas the actual `openComplete` field quantifies over
all complete ambient objects. The existing open quotient-Koszul theorem already
provides that stronger domain. The interval field requires preservation of the same
interval even when it is empty; exact finite extension and homology establish this
without an extra boundedness hypothesis. The remaining mismatch is presentation
transport between the actual ordinary/system functors and the slice-normalized open
comparison; it is isolated as the smaller Hom-transpose statement rather than
inferred from equality after finite evaluations.

## New nodes

`lem-sf-open-support-adjunction-transpose`, in
`dag/nodes/sec-smooth-purity/lem-sf-open-support-adjunction-transpose.json`, states the
normalized open pullback presentation and compatibility of the whole-system Hom
transposes. It is strictly a part of the original argument, with the inherited
chapter, unit and blueprint ancestry. The identity open, empty open, zero input,
and adjunction-triangle cases were checked in the proof in words; the parent proof
handles empty intervals independently. No change record is needed because existing
statements and definitions are unchanged.

## Second reading by F3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
