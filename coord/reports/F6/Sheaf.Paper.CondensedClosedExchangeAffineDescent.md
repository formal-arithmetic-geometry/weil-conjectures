## What changed

Replaced the whole-proof sorry of
`AlgebraicGeometry.ProEtale.CondensedRing.condensed_closed_exchange_affine_descent`
by the quotient-chart and cover argument. For the affine cover of Y, Mathlib's
`IsClosedImmersion.Spec_iff` supplies the ideals and quotient-spectrum presentations.
The proof transports the Cartesian squares along those isomorphisms, replaces the
domains of the base-change cover using `Cover.copy`, and weakens the resulting
open cover to a pro-etale cover. It forms the two further canonical pullbacks,
uses the single-open comparison, transports `hloc` through
`mapDerivedCategorySingleFunctor`, and applies the already-proved
`condensed_cover_restriction_conservative` to the actual global exchange component.

Added one proof-only import of the comparison module and one proof-only import
of the existing conservativity module. Existing public imports and signatures stay
identical. No source-library module, definition, instance or consumer is changed.
The item node's proof, proof_deps and proof_origin now describe this Lean argument.

The private, proved `isIso_iff_on_condensed_cover` packages the coefficient ring
and covering record while their maps are abstract. The private definition
`exactSingleIso` is the canonical Mathlib single-functor isomorphism with explicit
endpoints; its body contains no proof hole. The private theorems
`isIso_at_pullback_single_iff` and `isIso_restricted_exchange_of_single` perform the
degree-zero transport and apply the one-open comparison. The actual global exchange
keeps the canonical square and input literally identical in each occurrence.

Both files locally select the published sheaf monoidal and module abelian structures
instead of the definitionally equal closed-test cache wrappers. No instance body,
existing definition or public import is changed. Profiling isolated a deterministic
kernel timeout when specializing the single-functor transport with those wrappers.
Selecting the existing structures makes the argument share their data and removes
that conversion cost. All profiling options are removed from the delivery.

Validation: the final `lcompile.py --all` check compiled both sandbox modules with
exit code zero and no warnings. The reported module times were 44.2 s and 49.6 s,
both within the 60 s limit. Static checks confirm the unchanged item signature and
public imports, the exact node signatures and dependency unions, no profiling options
or forbidden constructs, and at most 100 characters per Lean line.

## Proved and sorry left

Closed the one existing whole-proof hole:
`AlgebraicGeometry.ProEtale.CondensedRing.condensed_closed_exchange_affine_descent`
(node `lem-sfb-condensed-closed-exchange-affine-descent`). The item module has zero
remaining sorries.

Added one hole:
`AlgebraicGeometry.ProEtale.CondensedRing.condensed_exchange_one_open_restriction`
in `Sheaf.Paper.CondensedExchangeOpenRestriction`
(node `lem-sfb-condensed-exchange-one-open-restriction`). Its proof is exactly
`by sorry`; there are no hidden proof holes and no data chosen from an unproved
existence theorem. The remaining statement is a comparison on one open, for an
arbitrary derived input and an arbitrary Cartesian presentation.
It asserts neither affine descent nor conservativity on any cover. The actual
quotient-cover argument and degree-zero transport are complete Lean in the item.

For the declarations changed here, this is a decomposition: one hole closed and
one hole added, net zero. It is not an independent proof of the remaining comparison.
The ledger determines the totals in the targets' import closure.

Edge cases checked mathematically: empty base/open and closed subscheme, I=0,
I=top, zero coefficient ring and zero input. The cover construction uses no
nonemptiness assumption. The comparison on an empty open is between maps in the
zero derived category, and both sides are invertible. Identity localization gives
the canonical exact/total-left comparison. No properness or finiteness hypothesis
is introduced.

## No longer needed

No existing Lean import is removed, and no module is withdrawn. No global module
pruning is claimed.

The item no longer directly uses
`lem-sfb-nonaffine-closed-test-exchange-identification` or its module
`Sheaf.Paper.NonaffineClosedTestExchangeIdentification`: the local comparison
works for arbitrary open localizations, without closed lifted-test evaluation.
This node remains needed by other consumers and is not withdrawn.

The item's old direct proof dependencies
`lem-weil-pbc-ringed-derived-slice-localization`,
`lem-sf-ringed-restriction-exchange-open-descent` and
`lem-sfb-internal-module-operations-transport` are replaced by the explicit
single-open comparison and the existing internal covering-conservativity theorem.
Ringed open restriction and internal-operation transport remain proof dependencies
of the new comparison; they are not claimed globally unnecessary. Generic exact
pullback and the ringed open comparison supply the localization used there.

## Where the brief, the DAG or earlier work was wrong

The planned section-module descent is mathematically applicable, but its interfaces
have different module presentations. The ordinary internal-operation transport
statement and ringed derived open restriction cannot simply be applied as one
Lean theorem about internal derived mates. The new node records just that local
comparison; cover detection is reused from the existing internal-module theorem,
which was not listed in the item's old proof_deps.

LeanFinder and LeanSearch returned ordinary structure-sheaf module restriction
adjunctions, not the internal condensed derived mate comparison. Loogle returned
no matching transformation theorem. Source searches found the exact internal
conservativity theorem and the ringed open-restriction theorem used by this route.
A further library search found `derivedOpenRestrictionNormalization` in
`Sheaf.Paper.DerivedOpenRestrictionNormalization`: its first clause supplies the
canonical open direct-image isomorphisms for arbitrary coefficients and schemes.
It does not compare the restricted arbitrary exchange with the localized exchange.
Together with `CategoryTheory.exchangeMate_cube`, it is an alternative internal
route for the remaining comparison; no new open direct-image lemma is needed.
The current blueprint refinement paragraph (2) is unchanged; this is an interface
reduction below the unit and does not replace its closed-complement argument.

## New nodes

`lem-sfb-condensed-exchange-one-open-restriction` compares invertibility of the
restricted actual ambient exchange with the local exact-pullback mate on one open.
It is strictly the localization/comparison step of the original proof, and contains
no cover or affine-chart hypothesis. The source is Stacks sites-cohomology,
Tags 0D6F and 07A7, with the existing ringed open-restriction and internal-operation
transport theorems. Its docstring gives the explicit comparison equation and explains
why all four auxiliary comparisons are invertible. Blueprint and library searches
found no existing internal-derived one-open comparison to reuse. It inherits the
item's chapter and unit. The generic ringed and internal-operation lemmas are used
as tools; no chapter or unit route is changed.

Change record: `coord/changes/F6-condensed-exchange-one-open-restriction.md`.

## Second reading by F6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
