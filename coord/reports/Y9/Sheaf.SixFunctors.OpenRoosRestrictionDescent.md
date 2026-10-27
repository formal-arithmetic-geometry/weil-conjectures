## What changed

Proved `WeilConjectures.OpenRoosRestriction.restrictionDescent` with its original
signature and both unit normalizations. The coefficient maps are the existing
canonical slice maps, by the proved normalization equalities. The finite transitions
use the existing finiteTransportSquare calculation from the supplied systemMap.
Restriction preserves
countable products as a right adjoint, making the specified `scalarRoosMap` invertible.
The proof constructs the good-representative comparison `c`, descends the full
completion comparison by fully faithful whiskering, and checks the all-object unit
square using the strict first/zero-second Roos coordinates. The generic augmented
Roos-map lemma is reused from IsomorphismOrdinaryCompletionChain; that helper has
no geometric isomorphism hypothesis. No duplicate generic coordinate proof is added.

Added `Sheaf.SixFunctors.OpenRestrictionQuotientTower`, with a complete proof of the
ordinary strict quotient comparison for the supplied Operations. The construction
uses the existing quotient-unit cokernel calculation and the existing normalized
uniformizer transport. Restriction preserves those cokernels, so their universal
property gives the level isomorphisms preserving the actual quotient units.
The image augmentation is an epimorphism; canceling it proves the strict transition
squares. This supplies the ordinary chain step without invoking another completion
or choosing an arbitrary cone filler. The zero complex, empty open, and n=0
(exponent one) all satisfy the same cokernel and augmentation equations.

Only the item, its node, this new proved module and its node are changed. Existing
public imports and all existing declaration signatures remain unchanged. All added
imports of the item are proof imports. Compilation and the delivery probe are run
through the required launcher tools. Local irreducibility keeps the completed
coefficient inverse limit and the constructed quotient isomorphisms from unfolding
during proof elaboration. Private categorical lemmas handle composition cancellation
the representative unit equation, and fully faithful descent before specializing
to the large coefficient categories; this avoids repeated dependent rewrites across
the completion data.
The exactness instances used in the existing signature are proved from the supplied
ordinary adjunction and localized restriction. No shared definition or exported
attribute is changed.

Validation: the required launcher `lcompile.py --all` compiled both delivered Lean
modules without warnings or errors, within the per-file limit. Temporary profiling
options and timing markers were removed before this clean compile.

## Proved and sorry left

Closed the one original hole:
`WeilConjectures.OpenRoosRestriction.restrictionDescent`
(`lem-sf-open-roos-restriction-descent`).

Also proved the new theorem
`WeilConjectures.OpenRoosRestriction.quotientTower`
(`lem-sf-open-restriction-quotient-tower`).

Holes closed: 1. Holes added: 0. Sorries left in either delivered module: 0.
The new module is a proved helper, not a split-off obligation.
Imported declarations retain their existing proof dependencies.

## No longer needed

No existing public import is removed, and no library module is withdrawn.
The following original direct proof dependencies are unnecessary for this proof:

- `lem-sf-open-quotient-completion-unit-comparison` /
  `Sheaf.SixFunctors.OpenQuotientCompletionUnitComparison`: the published quotient
  tower is compared directly by cokernels, then its actual Roos completion is
  descended. No transport from an existentially supplied alternative Operations
  or from a separate derived-limit completion model is needed.
- `lem-weil-pbc-proetale-immersion-limit-preservation` /
  `Sheaf.AlgebraicGeometry.ProEtaleImmersionLimitPreservation`: countable products
  are preserved by the supplied ordinary open restriction's actual right adjunction.
- `lem-cbc-exact-product-functor-strict-limit` /
  `Sheaf.Paper.ExactProductFunctorStrictLimit`: only the ordinary product Roos map
  and its coordinate characterization are needed, before derived descent.
- `lem-weil-pbc-profinite-coefficient-inverse-image` /
  `Sheaf.AlgebraicGeometry.ProfiniteCoefficientInverseImage`: open slice coefficient
  maps are identified by the existing finite constant-section and completed
  projection normalizations, without the general profinite inverse-image theorem.
- `lem-weil-proetale-weakly-etale-localization` is not an additional direct proof
  input: the proved canonical slice coefficient and good-restriction lemmas already
  supply its specialization. Its module can remain transitively needed by those
  lemmas; this is not a claim of a global withdrawal.

The existing ordinary quotient-module, open scalar transport, good-restriction,
Roos-coordinate and product-preservation lemmas are reused. No unit-level statement
or step is bypassed; only the internal route of this auxiliary node changes.

## Where the brief, the DAG or earlier work was wrong

The previous plan suggests transporting the alternative strict completion
comparison, but that theorem supplies an existential Operations and a different
completion model. It does not immediately give the requested comparison for the
prescribed Operations and published quotient Roos unit. The ordinary quotient-unit
cokernel API provides a shorter route: it avoids that entire model transport.

The rework entry lists this module's earlier quarantine. The current item source
was present and was preserved, with its original signature and Lean attachment.
No archive or module was deleted.

## New nodes

`lem-sf-open-restriction-quotient-tower` records the proved cokernel construction of
the ordinary strict augmented quotient-tower isomorphism, before any Roos complex
or derived localization. It is strictly the ordinary chain component of the parent
argument and introduces no new hole. Its module is
`Sheaf.SixFunctors.OpenRestrictionQuotientTower`.

## Second reading by Y9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
