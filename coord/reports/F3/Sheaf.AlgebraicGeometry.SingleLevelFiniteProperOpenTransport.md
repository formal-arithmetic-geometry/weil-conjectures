## What changed

The statement and public imports of
`Sheaf.AlgebraicGeometry.SingleLevelFiniteProperOpenTransport` are unchanged.
Its original sorry is replaced by a proof from an ordinary sheaf alpha equation.

The proof constructs the exact bounded-below pullback/open comparisons, proves
that exact localization preserves the ordinary alpha equation, proves the two
derived counit equations from the normalized underived mates, transports the
proper mate, identifies the etale normalization, and checks compatibility with
the unbounded inclusion. It uses the proved private generic helpers
`exactComparison_factorsh` (RightDerivedPlusCube), `derived_mate_eq`
(FixedComparisonDirectImageMate), `transport_mate`
(FiniteClopenMateSiteTransport), and `mate_ambient`
(EtaleClopenMateNormalization). These are generic category-theoretic tools;
no statement or step of the blueprint unit is bypassed.
The off-unit tool nodes are
`lem-weil-pbc-right-derived-plus-cube` (only its proved exact-comparison
factorization helper) and
`lem-weil-pbc-comparison-direct-image-canonical-mate` (only its proved generic
derived-mate helper). They supply formal localization and adjunction identities;
no node of this unit provides these generic APIs. No tool approval is written
into either node by this delivery.

The new module `Sheaf.AlgebraicGeometry.FiniteCoefficientClopenAlpha` constructs
`hPullbackIso`, `hPullbackPlus`, and `hOpenPlus`. Its one remaining theorem compares
ordinary sheaf alpha maps before complexes, localization, derived direct image,
or proper mating. Its docstring and node explain the section/projector argument,
the site factor, the identity-scalar realization factor and scalar restriction.
No existing definition or statement is changed and no consumer adaptation or
change record is needed. Both modules passed the remote compiler (28.1 seconds
for the new ordinary module and 44.1 seconds for the item). The sole unused simp
argument was then removed; delivery preflight validates the final sources.

## Proved and sorry left

This is a decomposition, not a net hole closure: the one original hole in
`AlgebraicGeometry.ProEtale.StrictTower.singleLevelFiniteProperOpenTransport`
is closed conditionally on one new strictly earlier sheaf-level step. There are
zero sorries in the item module. The private helpers `exactPlusNatIso_symm`,
`exactPlusMap_ι`, `homotopyPlus_whiskerRight_app`, `homotopyPlus_whiskerLeft_app`,
`exactAlphaCube`, `coefficientClopenAlphaPlus`, and `coefficientPlusCounit`
are completely proved. The localization calculation `exactAlphaCube`
works with abstract exact functor parameters, avoiding unfolding the concrete
sheafification and chosen left-adjoint constructions during rewriting.

One hole is added:
`AlgebraicGeometry.ProEtale.StrictTower.finiteCoefficientClopenAlpha`, node
`lem-cbc-finite-coefficient-clopen-alpha`. It is an equation on ordinary sheaves,
not the target equation under a renamed derived-direct-image interface. The item
contains the actual localization, derived-counit, proper-mate and inclusion
arguments combining it with the existing normalizations. Net hole change: zero.

## No longer needed

No module is withdrawn. No original public import is removed. The projector and
beta dependencies are needed by the remaining ordinary alpha obligation; they
are not claimed as globally pruned. In particular,
`lem-cbc-proper-open-clopen-projector` and
`lem-cbc-tower-open-beta-normalization` are no longer direct proof steps of the
item, and remain recorded under the new alpha node. The specialized site-mate
assertion is not applied in the item: only its proved generic `transport_mate`
helper is reused. The site-alpha comparison remains part of the ordinary-alpha
proof plan. No strict-tower evaluation or scalar-gamma statement is used in the
item proof.

## Where the brief, the DAG or earlier work was wrong

No statement is disputed. The original plan bundled ordinary coefficient alpha
compatibility, exact localization, proper transposition and inclusion
compatibility into one hole. The delivery proves the latter three steps, leaving
only ordinary alpha compatibility. The declared site and scalar alpha lemmas do
not alone identify the finite coefficient realization C with the constant-ring
clopen projector; the new node isolates that missing compatibility.

The new statement was checked on empty clopen images, empty complements, zero
rings and zero complexes. Restriction of scalars preserves zero maps and retains
the underlying additive sections, so no flatness is added. The shared library's
cartesian Noetherian scalar-extension comparison is a different interface and
does not imply this arbitrary scalar-restriction statement.

## New nodes

`lem-cbc-finite-coefficient-clopen-alpha`, in
`dag/nodes/sec-smooth-purity/lem-cbc-finite-coefficient-clopen-alpha.json`, states
the ordinary-sheaf compatibility in original parent steps 1--2. It inherits the
parent chapter, unit and explicit blueprint ancestry. The latest blueprint
`sec-six-functors-basics/sk-thm-sf-pf-adic/thm-cbc-complete-proetale.md`
states the condensed integral result and explicitly gives the factorization
`Rf^c_! = Rp_* ∘ i_!`. This delivery retains the assigned finite-level auxiliary
and its strict-tower ancestry; it changes no target or unit statement. The parent node now
records the localization, counit, mate and inclusion proof actually written.

## Second reading by F3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
