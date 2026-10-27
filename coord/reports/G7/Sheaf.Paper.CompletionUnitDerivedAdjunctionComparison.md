## What changed

Replaced the single hole in `CompletionUnitDerivedAdjunctionComparison` by a
resolving-class construction and an explicit comparison of left adjoints. The
existing statement and `systemLimitUnit` definition are unchanged.

The proof establishes that the ordinary tensor inverts quasi-isomorphisms between
K-flat complexes, using its finite evaluations, the existing scalar-extension
witnesses, and the calculus's joint conservativity. Flat-term K-flat resolutions
then construct the universal left-derived functor. The resolving-derived-adjunction
theorem gives its adjunction and Hom formula on every chain map. The canonical
left-adjoint isomorphism transports the comparison to the original `S.reduction`,
including its universal property, invertibility on flat-term K-flat complexes, and
the full Hom formula. This retains the fixed calculus, rather than choosing a new S.

The remaining geometric/interface work is separated into two genuine proper steps:
limit-acyclicity of the restriction of a K-injective system, and the finite scalar
adjunction-mate calculation for an already supplied comparison with the correct
unit. The former supplies the right comparison's K-injective computation, from
which the main module proves its right-derived universal property. The latter is
applied only after the main module constructs epsilon and proves its unit equation
by specializing the full Hom formula to an identity.

New modules are `CompletionUnitRestrictionAcyclicity` and
`CompletionUnitFiniteMateComparison`. Every new module has one named public theorem,
its source, a complete proof in words, and its own node. The parent node now follows
the actual resolving-class proof and these two smaller obligations.

Validation: the remote `lcompile.py --all` accepted all three modules. The item
compiled in 27.6 seconds; the finite-mate and acyclicity modules compiled in 8.4
and 2.8 seconds respectively, all below the 60-second limit.

## Proved and sorry left

Closed the item's original hole:
`WeilConjectures.CompletionUnit.derivedAdjunctionComparison_exists`.
Its module contains zero `sorry` after the change. The private proofs
`systemLimitUnit_isIso`, `tensor_inverts`, `flat_resolution`, and
`tensor_derived_exists`, and the K-injective instance, are fully proved.

Added exactly two holes, each with proof exactly `:= by sorry`:

- `WeilConjectures.CompletionUnit.restricted_limit_acyclic`, node
  `lem-trf-completion-unit-restriction-acyclicity`.
- `WeilConjectures.CompletionUnit.finiteComparison_of_unit`, node
  `lem-trf-completion-unit-finite-mate-comparison`.

This is a decomposition: one upper hole closed, two strictly smaller holes added,
not a claim of an axiom-free proof or a net hole reduction. The acyclicity lemma
has no calculus, ordinary model, derived comparison, or derived-adjunction
existence conclusion. The finite lemma takes an already supplied epsilon and only
its unit equation; it asserts solely its finite evaluation, not universality,
invertibility, an adjunction, or existence of any data. The construction and
transport combining the two are real Lean proofs in the item module.

The assertions include empty W, zero complexes, n = 0 (exponent one), arbitrary
integer degrees, and unbounded complexes. No preservation of K-injectivity by
scalar restriction or flatness of the quotient coefficient rings is assumed.

## No longer needed

No existing public import was removed, no module was withdrawn, and no global
pruning is claimed. The original module had only its public models import, which
is retained. New imports are private proof imports.

The parent no longer directly needs
`lem-coef-sequence-pushforward-limit-projections`
(`Sheaf.CategoryTheory.SequencePushforwardLimitProjections`): the finite calculation
uses the actual coefficient calculus's unit projection and the fixed finite scalar
unit, rather than constructing a second sequence-site derived adjunction and
comparing its counit. It also no longer directly invokes
`lem-weil-pbc-ringed-topoi-derived-pushforward-composition`
(`Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition`): the precise
restriction-acyclicity consequence is isolated instead. The generic sequence
adjunction and composition theorems remain among the dependencies of the existing
restricted-tower acyclicity theorem, so they are not globally obsolete.

All other original dependencies remain, directly or through the two smaller
obligations. The unit statement and its realized proof steps are unchanged.

## Where the brief, the DAG or earlier work was wrong

No false statement was found. The generic sequence-site declarations do not
specialize definitionally to the coefficient-site modules and its uniquely
characterized scalar-restriction functor. The remaining acyclicity obligation is
exactly that transport, rather than an assumption that exact restriction preserves
K-injectivity.

The finite comparison can use the unit equation alone. Its proof plan first extends
the normalized tower projection from K-injectives by exact evaluation and
naturality, then uses injectivity of the finite scalar Hom equivalence. Equality of
arbitrary derived system maps is never inferred from equality of their levels.

The hypotheses giving coherence of S and the right-derived universal property of
eta are retained verbatim in the original signature. The constructed proof needs
only the indicated calculus data and eta's stronger K-injective normalization; it
proves the required right-derived universal property of the composite directly.

## New nodes

`lem-trf-completion-unit-restriction-acyclicity` specializes the existing
`lem-coef-restricted-tower-resolution-acyclicity` to the actual coefficient sequence
site and its characterized restriction functor, using Stacks 0941 and 0D6E. Its
statement is only that ordinary limit sends the displayed tower resolution to a
quasi-isomorphism.

`lem-trf-completion-unit-finite-mate-comparison` is the finite calculation in parent
step 3, using Stacks 07A6, 0941, and the fixed 06YY/09T5 scalar-unit normalization.
It requires only the unit compatibility of an already supplied natural comparison.

LeanSearch, Lean Finder, Loogle and local source searches found the generic derived
adjunction and uniqueness APIs but no duplicate specialized theorem. Whole-blueprint
searches for restricted towers and finite scalar adjunctions found no duplicate
blueprint node. Both nodes inherit the parent's chapter, unit and blueprint ancestry.
No existing statement or definition changed, so no change record is required.

## Second reading by G7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
