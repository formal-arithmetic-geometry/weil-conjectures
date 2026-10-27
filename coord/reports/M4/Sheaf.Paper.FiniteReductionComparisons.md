## What changed

`Sheaf.Paper.FiniteReductionComparisons` now proves
`WeilConjectures.PurityFiniteSetting.finiteReductionExceptionalComparison_isIso`
by identifying the existing finite exceptional coefficient isomorphism with the
counit-normalized comparison. Positive exponents are written as successors; the
impossible zero cases are discharged from the existing positivity hypotheses.
Uniqueness of `existsUnique_finiteReductionExceptionalComparison` supplies the
identification, after which the hom of an isomorphism is invertible.

The new module `Sheaf.Paper.FiniteReductionExceptionalFiniteModel` constructs
`finiteReductionExceptionalFiniteModel` by applying the full finite-Tor inclusion
to the specified `FiniteExceptional.b` and using its existing invertibility
statement. This is an actual fixed construction, not a choice of an arbitrary
endpoint isomorphism. The remaining normalization equation is a named theorem
in that module, with its complete argument and source in its docstring.
The item imports this module privately. Existing signatures and definitions are
unchanged; the original node's proof records the assembly argument.

The earlier source-chart uniqueness proof uses `Iso.cancel_iso_hom_right` directly
instead of searching for a `Mono` instance of the chart hom. The initial full
compile exhausted instance-search heartbeats at that search. The explicit
isomorphism-cancellation proof avoids unfolding the chart construction.
The proof disables, for the two affected declarations, the overlapping
`WeilConjectures.IntegralHom.derivedCategory` instance imported through the new
finite-exceptional dependency. Its unconstrained coefficient-universe parameter
otherwise obstructs the existing scalar-adjunction normalization helper. The
original helper, source theorem and derived localization are preserved. These
scoped attributes does not change any imported declaration or exported attribute.

## Proved and sorry left

Original item holes: 1. Closed:
`WeilConjectures.PurityFiniteSetting.finiteReductionExceptionalComparison_isIso`
(node `def-pur-finite-reduction-comparisons`). No `sorry` remains in the item.

Added holes in this delivery: 1:
`WeilConjectures.PurityFiniteSetting.finiteReductionExceptionalFiniteModel_counit`
(node `lem-pur-finite-reduction-exceptional-model-counit`). Its proof is exactly
`by sorry`. This is a decomposition, closing one local hole and adding one, not a completed
proof of the coefficient compatibility from axiom-free dependencies.

The remaining equation compares the concrete finite mate's normalization with
the published purity counit and the scalar adjunct of the proper/open restriction
comparison. Its isomorphism has already been constructed from
`FiniteExceptional.finite_exceptional`; neither its existence nor its
invertibility is assumed by a new theorem. The assembly from that equation to
the original assertion is complete Lean.

## No longer needed

None. No original import, declaration, node or module is withdrawn. The preceding
six parts of the item still use their recorded dependencies. In particular,
the existing compact-support comparison and its finite-Tor invertibility remain
needed for existence and uniqueness of the exceptional comparison.

## Where the brief, the DAG or earlier work was wrong

The assigned hole is the final exceptional-comparison invertibility theorem; the
other declarations in the current item are already proved. Its node's last step
merely recorded that obligation. The existing `FiniteExceptional` theorem supplies
the invertible mate; the remaining work is matching its counit and support
normalizations with the purity presentation, rather than reproving duality.
No mathematical statement correction or target change is made.

The new normalization statement was checked for equal exponents, the zero
object, empty source and target, and nonflat quotient maps. Its argument uses
finite-Tor constructibility, rather than quotient flatness, for the bounded
etale-origin domain. It does not assume smoothness, although the original
comparison's existence theorem does.

## New nodes

`lem-pur-finite-reduction-exceptional-model-counit` carries the normalization
identity for the full inclusion of the existing finite exceptional mate. Its
source is the current blueprint finite-reduction proof, Steps 2 and 4, together
with the counit clause of `lem-coef-finite-exceptional`. It inherits the item's
chapter and unit. LeanSearch and LeanFinder locate ordinary scalar counits and
the formal mate identity; Mathlib and project searches find no theorem comparing
these two specified site realizations. Its proof records the finite counit
identity, normalization of each realized counit, normalization of the
proper/open scalar comparison, and substitution. There are no change records,
because no existing statement or definition is changed.

## Second reading by M4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
