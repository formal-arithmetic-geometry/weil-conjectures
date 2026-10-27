# Individual compactness obstruction in the Brown-hypotheses module

## Reason

The current queue marks the item disputed, with the original single hole in
`CategoryTheory.brownHypotheses`. Its unrestricted compactness assertion cannot be
supplied by the finite-field theorem or the Ext-bounded integral criterion. The
maintenance rollback in `maintenance-K4-brown-false-split-rollback.md` explicitly
forbids recreating the retired unrestricted compactness witnesses. This packet
preserves the disputed statement and its hole, and strengthens the proved obstruction
so it identifies an individual noncompact object without assuming a Brown bundle.
This is partial diagnostic work, not a proof of the unrestricted Brown theorem.

## Old

The finite-support, degreewise-disjoint, varying-heart and uniform-heart arguments
were available only under `BrownHypothesesFor Λ X` and constructibility with finite
Tor amplitude of the source. Their bodies extracted the source's compactness from
the Brown bundle, then carried out the actual compactness argument. Thus the proof
could not be applied directly to an independently compact source object.

The file imported the full proper-direct-image coproduct module to get the
`countableAB4Star_mod` instance.

## New

Extract three proved private helpers for finite Hom support and eventual vanishing,
using individual compactness. Reuse the structural theorem to obtain the canonical
triangulation and repleteness, independently of the Brown assertion. Add the proved
public theorem `CategoryTheory.exists_uniform_hom_single_shift_bound_of_compact`
and its contrapositive `CategoryTheory.not_isCompactObject_of_unbounded_ext`.
The source may be any object of the localizing closure, including an unbounded one.
The result holds for every scheme and commutative condensed ring; no geometric
cohomological bound is asserted.

Preserve every existing declaration signature and public import. Derive the existing
Brown-specific theorems by extracting compactness once and applying these helpers.
Move the local irreducibility declaration for the large Brown bundle just after
its criterion API, so later proofs use the API without unfolding the bundle.

Replace the proof-only import
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ProperLowerStarCoproducts`
by the narrower imports
`WeilConjectures.AlgebraicGeometry.ProEtale.RepleteAddCommGrp` and
`WeilConjectures.CategoryTheory.ModuleObjects.SequentialLimitEpi`.
A proved private local instance obtains the same countable exactness directly from
repleteness, the exact conservative module forgetful functor, and
`CountableAB4Star.of_epi_π_app_zero`. No adopted source module is changed, and no
new axiom, object data, or hole is introduced.

## Users

| Module | Holder | Effect |
|---|---|---|
| Sheaf.SixFunctorsBasics.BrownHypotheses | B2 assignment | Private proof refactor, two added proved theorems, narrower private imports. |
| Sheaf.SixFunctorsBasics.BrownHypothesesFiniteField | no local claim recorded; unchanged | Direct importer; every existing signature, public import and instance is preserved. |
| Sheaf.SixFunctorsBasics.BrownHypothesesCoefficientIso | no local claim recorded; unchanged | Direct importer; existing Brown criterion and local elaboration helpers are unchanged. |
| Sheaf.Paper.LocalizingExceptionalAdjoint | no local claim recorded; unchanged | Direct importer; both calls of the disputed theorem retain their exact types. |

No forced adaptation and no target-statement or definition change is made.
The delivery tool checks these direct importers against the delivered module.

## Status

Pending delivery and the maintainer's independent review/global build.
The initial unchanged item exceeded 60 seconds (68.9 seconds). The refactored
profiled version compiled in 49.2 seconds. Profiling options were removed before
the final compile and delivery. The final file compiled without warnings in
29.5 seconds; importer and axiom checks are performed by deliver3.py.
