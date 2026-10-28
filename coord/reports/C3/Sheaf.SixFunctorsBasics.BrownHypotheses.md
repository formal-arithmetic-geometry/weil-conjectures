## What changed

Added the proved specialization
`CategoryTheory.brownHypotheses_padicIntegers_of_finite_or_separablyClosed`
to `Sheaf.SixFunctorsBasics.BrownHypotheses`, for the canonical integral
coefficient object of a finite extension of Q_ell. The explicit hypothesis
`Finite k ∨ IsSepClosed k` is retained from the existing upstream theorem
`CondensedRing.hasUniformConstructibleExtBound_padicIntegersRingObj`.

A proved private helper converts finite constant-model constructibility to
ordinary constructibility on compact quasi-separated schemes. It uses local
finite presentation and transport across the canonical coefficient isomorphism.
The main proof converts the upstream bound on single-complex degrees to a bound
on positive shifts, and applies the existing integral Brown equivalence.
Added four private proof imports: BrownHypothesesCriteria,
FiniteConstantLocalModel, CondensedConstructibleSerre (all), and the upstream
CompactConstructibleEllAdic module. All previously exported declarations,
attributes, instances and public imports are preserved.

The complete item compiles in 9.4 seconds. The empty scheme, zero sheaves, and
arbitrary signs of the upstream integer bound are covered by the same proof:
q > -d implies -q <= d. The finite-or-separably-closed hypothesis is passed
verbatim to the upstream theorem. No source-library file is edited.

## Proved and sorry left

Original holes closed: 0 of 1. New holes added: 0. Split off: 0.
The original `CategoryTheory.brownHypotheses` remains the sole direct `sorry`
in this packet, tracked by `sk-lem-brown-hypotheses`; its statement and proof
are unchanged. The new specialization and the private helper are fully proved
from existing named declarations. In particular the specialization uses the
already-stated upstream Ext-bound theorem, whose existing `sorry` is tracked by
`lem-sfb-uniform-constructible-ext-bound-integral`; this is not an axiom-free
completion of that dependency or of the original target route.

## No longer needed

None. No previous import, module, declaration or node is withdrawn. The original
unit's dependencies and route remain in place. The new supported specialization
uses the uniform Ext bound and the integral Brown criterion; it does not assert
that the existing finite-field or conditional compactness modules are globally
unneeded.

## Where the brief, the DAG or earlier work was wrong

STATEMENT-DISPUTED: The original Brown assertion assumes an arbitrary
positive-characteristic field. Finite type over such a field does not supply
finite ell-cohomological dimension. Its existing comment gives the field
F_3bar(t_1,t_2,...) and coefficient F_2 obstruction. This packet preserves that
mathematical diagnosis rather than claiming its formalization.

The current server queue assigns the disputed route; there is no current rework
or return entry requiring an additional repair. The build-error record is an old
bad-import failure whose imports are already absent from the current item.
The maintainer record `maintenance-K4-brown-false-split-rollback.md` explicitly
preserves the original hole and forbids recreating unrestricted compactness or
Ext-bound splits. The new specialization retains the necessary field hypothesis
and does not change the unit statement or shift the false assertion to a new hole.

The compiler used the current unpublished Definitions/Criteria dependency split
through its private overlay. The coefficient-transport proof explicitly unfolds
CondensedRing.upperStar locally, respecting the existing local irreducibility
settings without altering any shared definition.

## New nodes

`lem-sfb-brown-integral-finite-or-separably-closed` records the proved integral
specialization, its exact Lean signature, the local-presentation comparison,
existing uniform Ext bound, and existing integral Brown equivalence. It adds no
new proof obligation. The original unit node and realized route are unchanged.

Change record: `coord/changes/C3-brown-integral-finite-or-separably-closed.md`.

## Related modules compiled before delivery

4 related module(s) compiled against this delivery by deliver3.py: 4 OK.

```json
{"capped": false, "direct": 4, "left_out": 0, "own": {"Sheaf.SixFunctorsBasics.BrownHypotheses": "826b90564595afe8ca7f1f40af6ab42f1b2e9522"}, "results": {"Sheaf.Paper.ExceptionalInverseImageExistence": {"hash": "e047ddc64ca96bb191cbf95acc82e09bbcecd38a", "status": "OK"}, "Sheaf.Paper.LocalizingExceptionalAdjoint": {"hash": "9b80929ae886e8305a73db59aae3e626c6c33cd3", "status": "OK"}, "Sheaf.SixFunctorsBasics.BrownHypothesesCoefficientIso": {"hash": "3e88941ba8a08ff09caa78531b8976313e338427", "status": "OK"}, "Sheaf.SixFunctorsBasics.BrownHypothesesFiniteField": {"hash": "4631bb5554deea7420a4891b81aec3ba809214d0", "status": "OK"}}, "seconds": 151, "time": "2026-10-28T14:07:32+0800", "transitive": 0, "version": 1}
```

## Second reading by C3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
