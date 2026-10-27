## What changed

Proved `WeilConjectures.IntegralSystemRealization.integralComparisonRecursionLaws`
in the assigned module without changing its statement or any shared interface.
Restored the quarantined item source, which is also now present in the live library.
Added proved private helpers and a structurally recursive family of natural isomorphisms.
The construction restricts each child to the parent's full admissible domain;
pullback and tensor insert inverse actual counits, proper image uses the given
ambient comparison, and open extension uses the specified open realization.
Its naturality follows by cancelling the invertible outer factors in its normalization.
Compact support is exactly the proper-after-open composite.
Updated the item's node to describe this direct proof.

Validation: the complete module compiled cleanly through `lcompile.py` in 39.6 s,
with no warnings or errors. The delivery tool performs the final preflight and axiom checks.

## Proved and sorry left

Closed 1 existing hole:
`WeilConjectures.IntegralSystemRealization.integralComparisonRecursionLaws`
(lem-sf-integral-comparison-recursion-laws).
Added 0 holes. No `sorry` remains in the delivered module. All private helpers are proved.
Existing imported model theorems remain obligations of their own modules.

## No longer needed

Removed direct proof imports `Sheaf.SixFunctors.IntegralBasicRealization` and
`Sheaf.SixFunctors.IntegralExpressionRecursion`.
The proof does not invoke lem-sf-integral-basic-realization,
lem-sf-integral-expression-recursion, or lem-sf-generator-reduction-coherence.
It needs neither primitive coefficient transposes nor direct support projections.
The given AmbientModels already supplies proper and open comparisons, while
published canonical pullback/tensor models supply those constructors directly.
The actual reconstruction theorem is used through the unrestricted
lem-pod-unrestricted-normalized-reconstruction rather than the older
lem-pur-normalized-actual-reconstruction-maps attachment.
The assembly-data public import still transitively imports some of these modules;
no module is withdrawn or claimed to leave the target import closure.

## Where the brief, the DAG or earlier work was wrong

The old proof plan unnecessarily requested identification of a separately selected
basic realization model with the supplied ambient model. The direct construction
uses the supplied model throughout and requires no such uniqueness proof.
Also, ExpressionRecursion.Reconstruction.reduction asks that every constructible
input reduce to a Good system, including uniform finite Tor bounds and origins.
That record is stronger than the hypotheses available here: the item retains those
conditions only on its explicit full expression domain. The proof does not assume
that constructibility provides them. It uses each recorded intermediate Good witness.
The unit route and all six required recursion equations are preserved.
No shared statement or definition is changed.

## Second reading by S3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
