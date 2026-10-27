## What changed

The item retains its original theorem signature and public imports. Its proof now
constructs the lift of the canonical small coefficient field into the scheme universe.
The private helpers prove equality of the extended absolute values, identify the integer
subrings, construct the integer ring equivalence and its homeomorphism, and induce the
condensed ring-object isomorphism by postcomposition on continuous functions.

The existing constant-model coefficient transport and
IntegralConstantModel.constructible_iff identify the constructible module with its
completed section-action realization. The proved two-term perfect-model helper from
IntegralCohomologicalAdicCriterion, together with adic_stratified_perfect, gives local
derived completeness. The exact functor/single-complex comparison transports this to
the realization of C[0]. The item then applies the new general comparison
smallIntegralRoosCompletenessTransport, which isolates the remaining comparison of
local ringed-site completeness with the actual small-coefficient augmentation.

The new module has one statement. No definition, existing signature, source-library
module or consumer was changed. All added imports are private proof imports in the
item; the new comparison module publicly imports only its statement interfaces.

Validation: both Lean modules compiled successfully through lcompile.py. The item
compiled without warnings in 24.5 seconds; the comparison module compiled in 54 seconds.
The theorem signature was checked verbatim against the original, and both node files
have valid dependency references with proof_deps equal to their proof-step uses.

## Proved and sorry left

This is a decomposition, with one upper hole closed and one comparison hole added;
no net reduction in holes is claimed.

Closed in the item: AlgebraicGeometry.ProEtale.integralHeart_constructible_module_complete
(node lem-sfb-integral-heart-constructible-module-complete). Its proof combines the
constructed coefficient isomorphism, the existing constructibility and perfect-model
results, the single-functor isomorphism, and the general completeness comparison.
The private liftFinite, liftAbsoluteValue, liftMemIntegers, liftIntegers,
liftIntegerHomeo and liftPointIso constructions have complete proofs and no holes.

Added and remaining: AlgebraicGeometry.ProEtale.smallIntegralRoosCompletenessTransport
(node lem-sfb-small-integral-roos-completeness-transport), in
Sheaf.Paper.SmallIntegralRoosCompletenessTransport. Its whole proof is `by sorry`.
It compares completion presentations for arbitrary unbounded complexes and arbitrary
condensed coefficient isomorphisms; it has no constructibility assumption and does
not assert the item under another name. The item's nontrivial finite-model argument
establishes this comparison's local-completeness premise from constructibility.

There are zero textual holes left in the item and one in the new comparison module.
Existing imported holes, including integralSectionLocalModels, are used as the stage
brief authorizes and are not duplicated or counted as new holes.

## No longer needed

No existing import or module was removed or withdrawn.

The original direct dependency on sk-lem-integral-models / Sheaf.Paper.IntegralModels
is unnecessary: its embedded-field and finite-type-base hypotheses are avoided by
using the general Noetherian perfect-model criterion already stated below that unit.
The unit's route and realizations are preserved.

The original direct dependency on sk-def-pe-derived-completion /
Sheaf.SixFunctors.ProEtale.DerivedCompletion is unnecessary in the item's argument:
the conclusion uses SmallAdicCompletion and its remaining comparison is stated for
that exact interface. This does not withdraw the ordinary completion API.

The original direct dependency on lem-sfb-integers-profinite-tower is not needed for
the explicit ULift coefficient isomorphism: uniqueness of the absolute value and
isometry suffice. The tower theorem remains a dependency of the new general
completion-comparison node, so its module is not claimed pruned globally.

The constructibility definition node remains a statement dependency and its interface
is used through the existing transport theorem. It is not separately needed as a
proof lemma. No target or blueprint unit is bypassed.

## Where the brief, the DAG or earlier work was wrong

The planned embedding into an algebraic closure is unnecessary. The canonical small
field can be lifted directly by ULift; its coefficient-ring comparison is proved here.
The degree-zero part of the cohomological criterion already has a proved private
perfect-model helper, so a new constructibility/completeness assertion is unnecessary.

The small-coefficient Roos interface has no published comparison to the ringed-site
local-completeness predicate. The ordinary-universe completion-presentation lemmas
and IntegralConstantModel's ordinary realization do not by themselves supply this
independent-universe comparison. It is isolated explicitly, with quotient units,
transitions and the zero augmentation coordinate retained in its proof plan.

The new statement was checked on zero complexes, the empty scheme, unbounded
complexes and torsion coefficients. Coefficient isomorphisms preserve the unique
maximal ideal even when the chosen uniformizers differ by a unit; quotient powers,
not an equality of chosen uniformizers, are what the comparison requires. The
comparison imposes no finite Tor or constructibility restriction and does not choose
any data from its unproved implication.

Searches used LeanFinder, LeanSearch, Loogle and local ripgrep. The recorded Mathlib
hits concern ordinary adic completion and condensed-module construction, rather than
this normalized derived-completion comparison. The blueprint search found no existing
small integral Roos comparison node.

## New nodes

lem-sfb-small-integral-roos-completeness-transport realizes the comparison part of
integral-heart-local-model clause (2), Completeness. It retains the same chapter and
unit as the item. Its source is Stacks Tags 099L, 099M and 0A0E, together with the
blueprint's canonical completion map. Its proof plan identifies the coefficient
quotients and their units, uses the existing constant-completion equivalence, and
identifies its unit with the explicit augmented Roos complex using K-flat models and
exact countable products. The item proves the needed local completeness separately.
No change record is required: no existing public interface or definition changed.

## Second reading by S6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
