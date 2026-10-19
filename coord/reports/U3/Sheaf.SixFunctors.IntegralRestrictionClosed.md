## What changed

Completed integralRestrictionClosed, preserving every public statement and definition.
The proof uses the formal support triangle, exact closed pull-push, integral inverse-image
preservation, compactification comparison and explicit Yoneda naturality on full localizing
subcategories. The retained private Hom-equivalence helpers compile unchanged in signature.

Also proved the retained new prerequisite integralComplementFiniteness in its own module.
Its triangulation argument uses the existing exact-coefficient integral Serre-closure theorem,
a real rank-zero scalar model for zero, isomorphism invariance and the generic weak Serre
homology-property construction. Its open term uses IntegralModelsOperations, Dctf=Dbc and
integralOpenDirectImage in exactly the padicIntegersRingObj coefficient presentation.
Updated both DAG proof records to follow the Lean argument. Added only proof imports to
the existing item; no existing public imports, definitions, signatures or visibility changed.

## Proved and sorry left

Closed the original hole
AlgebraicGeometry.ProEtale.CondensedRing.IntegralCompactSupport.integralRestrictionClosed
(det-thm-int-restriction-closed): 1 of 1 original holes closed, no holes added.

The retained prerequisite
AlgebraicGeometry.ProEtale.CondensedRing.IntegralCompactSupport.integralComplementFiniteness
(lem-sfb-int-closed-complement-finiteness) is now proved as well. Both delivered modules
contain zero sorry. The proofs use existing named dependency theorems which can themselves
still depend on sorry; this is a proof from those declarations, not a claim that the entire
transitive dependency closure is axiom-free. No split-off hole remains.

## No longer needed

Removed the item module's six original proof imports:
Sheaf.Paper.FormalClosedSupportSheaves (already provided by FormalClosedSupportDerived),
Sheaf.Paper.IntegralConstantModelHeart (replaced by exact-coefficient Serre closure),
Sheaf.Paper.IntegralTensorPullback (replaced by IntegralModelsOperations),
Sheaf.Paper.LocalizingClosureCtfEqualsBc (used in the new finiteness module instead),
Sheaf.SixFunctors.IntegralLocalizingCompactSupport (already a public statement dependency
through IntegralBrownAdjoint), and Sheaf.SixFunctors.ProEtale.IntegralOpenDirectImage
(replaced by the exact-coefficient IntegralOpenImageProperFormulas interface).
No original public import was removed. No direct proof import of IntegralTensorPullback,
IntegralOpenDirectImage or IntegralConstantModelHeart is needed. The exact-coefficient
IntegralModelsOperations and IntegralOpenImageProperFormulas interfaces avoid their
coefficient-presentation comparison. The full integral heart theorem is replaced below
unit level by the existing integral Serre-closure theorem and the generic homology argument.
The new finiteness lemma is fully proved, so it creates no new proving obligation.

Removed obsolete top-level tool_uses approvals det-lem-formal-closed-support-sheaves,
det-lem-int-tensor-pullback,
det-lem-int-integral-heart-triangulated, det-prop-int-brown-adjoint and
det-thm-sf-pf-adic-open from the item's node: sheaf exactness comes directly from recollement.
The integral pullback, heart and open-image details use the exact-coefficient interfaces above.
The Brown existence assertion is unnecessary since
the required comparison already quantifies over a specified adjunction. IntegralBrownAdjoint
remains a public statement dependency for lowerShriek.

The derived cone-fibre formula is unnecessary: exact closed pull-push gives the recovery
isomorphism directly. The original localizingClosure_ctf_equals_bc use in the Yoneda step
is unnecessary: generators belong to their ordinary localizing closure by definition.
Its theorem is used instead in the new finiteness proof to provide finite Tor amplitude.
No unit statement or closed-immersion localization step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The earlier report's missing-source claim is stale: IntegralTensorPullback and
IntegralOpenDirectImage now exist in the current checkout. Their coefficient presentations
differ from padicIntegersRingObj, but existing IntegralOpenImageProperFormulas and
IntegralConstantModelHeartClosure already provide the exact-coefficient conclusions.
Thus the retained finiteness sorry was unnecessary and is now proved.

The static checker requested a record for the added top-level proof commands. The record
`coord/changes/integral-restriction-closed-proof-scope.md` lists the consumers; no public
signature, definition or consumer changes. On resumption, checked both original public
definitions and the theorem signature against current sources: all remain textually
unchanged. Both modules recompiled with lcompile.py --all in 1.2 seconds each, without
errors or warnings. Both have zero sorry tokens and satisfy the 100-character line limit.
The required dry run was started before further work; the delivery tool manages its queue.

## New nodes

lem-sfb-int-closed-complement-finiteness: a fully proved prerequisite giving triangulation
and the open-complement term's finiteness, strictly before the support-triangle and Yoneda
arguments. It has no closed-support or Brown-adjoint conclusion. Its edge cases include
K=0, empty X, i=id and empty Z. Its module and the main module were checked by lcompile.py.
The proof-scope change record is
`coord/changes/integral-restriction-closed-proof-scope.md`.

## Second reading by U3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
