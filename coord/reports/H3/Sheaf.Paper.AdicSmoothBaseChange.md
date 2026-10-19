## What changed

Proved `WeilConjectures.adicSmoothBaseChange` from the canonical finite reduction
comparisons, finite smooth base change, and one separate coefficient-coordinate lemma.
The theorem signature and all definitions are unchanged. Private proved helpers establish
conservativity of canonical reductions on complete objects, reconstruct constructible
membership from uniformly bounded canonical reductions, and transport finite cohomology.
The latter reconstruction explicitly lifts successive quotient normalizations through the
fully faithful bounded-below site comparison.

Added `Sheaf.Paper.SbcFiniteExchangeCoefficientRealization`, stating the independent
comparison between ordinary ringed finite exchange and realized fixed-scalar exchange.
It assumes no geometric finiteness, smoothness, boundedness, or constructibility. Its
source, complete proof in words, and matching DAG node are included. No object or
functor is selected from an arbitrary existence assertion in this delivery.

## Proved and sorry left

Closed the original module's one hole, `WeilConjectures.adicSmoothBaseChange`.
Added one named theorem hole:
`WeilConjectures.sbcFiniteExchange_coefficient_realization`, node
`lem-sbc-finite-exchange-coefficient-realization`.
Thus this is a decomposition: one original hole closed, one separate hole added, net
zero holes closed. The main module has zero `sorry`; the new module has one `sorry`.
Every private helper is proved; no definition contains `sorry`.

The main proof and the new statement compile individually through `lcompile.py`.
The missing proof is precisely compatibility of the two coefficient presentations with
canonical derived pullback composition and the units and counits defining the mate.
The existing underived direct-image comparison alone does not establish that compatibility.

## No longer needed

Removed direct proof imports:
`Sheaf.Paper.CompletedDirectImageLimits`,
`Sheaf.Paper.CompletedPullbackReduction`,
`Sheaf.Paper.PerfectProjectionFormula`,
`Sheaf.AlgebraicGeometry.ProEtaleRingSheafChangeAdjunction`,
`Sheaf.AlgebraicGeometry.ProfiniteCoefficientInverseImage`,
`Sheaf.Paper.CompletedAdicLevelwiseIsomorphismCones`,
`Sheaf.Paper.ConstantCompletionEquivalence`,
`Sheaf.Paper.FiniteRingConstructibleDerivedOrigin`,
`Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`,
`Sheaf.AlgebraicGeometry.ProEtaleSiteComparisonDerived`,
`Sheaf.AlgebraicGeometry.ProEtaleFiniteModules`, and
`Sheaf.Paper.NormalizedEtaleOriginWitnesses`.

The completed-operation API already supplies complete endpoints and the actual reduction
comparison equation, so the direct-image and perfect-projection arguments are not repeated.
The private conservativity proof uses actual strict completed identity pullback and exact
evaluation of derived towers. The private membership proof uses normalized local effectivity
and explicitly constructs compatible etale origins. Consequently the separate levelwise-cone,
constant-completion-equivalence, finite-ring-origin and normalized-origin-witness results are
not invoked directly by this proof. Some removed imports remain transitive dependencies of
retained APIs, so this does not claim their modules have left the targets' import closure.
No entire existing module is withdrawn.

The node's direct proof dependencies and steps now follow the implemented argument.
Removed obsolete top-level tool-use entries:
`prop-weil-pbc-direct-image-limits`, `lemma-weil-pbc-completed-pullback-reduction`,
`lemma-weil-pbc-perfect-projection-formula`, `lem-weil-pbc-ring-sheaf-change-adjunction`,
`lem-weil-pbc-profinite-coefficient-inverse-image`,
`lem-weil-pbc-levelwise-isomorphism-cones`, `lem-weil-pbc-constant-completion-equivalence`,
`lem-weil-pbc-finite-ring-constructible-derived-origin`,
`lem-weil-pbc-ringed-topoi-derived-tensor-pullback`, `thm-weil-pbc-site-comparison`, and
`lem-weil-pbc-normalized-etale-origin-witnesses`. These remain available transitively where
needed by retained APIs. No unit statement or realized unit step is removed.

## Where the brief, the DAG or earlier work was wrong

The landed finite smooth theorem presents its exchange in fixed-scalar coordinates, whereas
the adic theorem uses `sbcFiniteExchangeApp` in quotient ring-sheaf coordinates. The required
comparison was not a declaration of the stated dependencies. The new lemma isolates this
coefficient change independently of smooth base change and completion.

The retained report incorrectly said no new hole was added. The exact decomposition count
is recorded above. A failed experimental scalar-restriction construction was removed; it is
not part of this delivery. No existing statement, definition, visibility, or target changed.

## New nodes

`lem-sbc-finite-exchange-coefficient-realization`: coefficient-coordinate invariance of
ordinary finite exchange, sourced from the normalized adjunction-mate construction in Stacks
Tags 07A7 and 0D6D. It is strictly part of the finite-level step: it proves no invertibility,
uses no smoothness, and includes no completion or constructible landing claim. Its Lean
module is `Sheaf.Paper.SbcFiniteExchangeCoefficientRealization`.

Change record: `coord/changes/adic-smooth-base-change-proof-interface.md`. The finite
site-comparison unit-route import is retained.

## Second reading by H3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
