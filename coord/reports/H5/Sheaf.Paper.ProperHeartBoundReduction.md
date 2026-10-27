## What changed

Proved `AlgebraicGeometry.ProEtale.properHeartBoundReduction` with its statement and all
three existing definitions unchanged. Added private proved helpers, including the generic algebraic-closure
coefficient argument, for extension-closed
properties, finite subobject filtration induction, lattice filtration, and transport between
the original finite coefficients and the universe-lifted spectral-norm coefficients.

The finite-coefficient case applies the existing lattice-subquotient filtration. The
algebraic-closure case descends each lisse quotient to F0, chooses a finite common upper bound F of E and F0,
and applies the same argument after ordinary scalar extension. The outer filtration comes
from clause (11) of `coefficientHeart`. The proof uses the proved private scalar and universe
transport helpers of `IntegralModelsGenerators`, rather than its derived-generation theorem.
The node's proof, proof dependencies, and proof origin now describe this route.
The higher-vanishing predicate is used for all degrees at once, with direct proofs
of its closure rules. Generic private helpers use the same concrete module presentation
as the imported library; scalar comparison is wrapped in a proved private isomorphism.
The outer constructible filtration is applied once, after coefficient reduction.
A private named stratum predicate keeps the extension-by-zero expressions shared between
the lattice and constructible-filtration interfaces. This removes repeated kernel expansion
of their coefficient structures. No compiler limits are increased, and no proof or module
is split to satisfy the limit. The complete file compiled cleanly in 44 seconds under normal
settings against the unchanged shared library. Experimental changes to `ModuleObjects` were discarded; only the item is delivered.
The directed finite-field poset supplies a common upper bound of E and F0, avoiding
unfolding a concrete compositum throughout the coefficient constructions.

## Proved and sorry left

Closed the single existing hole:
`AlgebraicGeometry.ProEtale.properHeartBoundReduction`
(`det-proper-heart-bound-reduction`).

Holes closed: 1 of 1. Holes added: 0. No `sorry` remains in the delivered module;
no new modules or unproved intermediate declarations are added. Existing stated dependencies
remain proof dependencies as intended by stage 3; this does not assert that the complete
target import closure is axiom-free.

## No longer needed

Removed direct proof imports: `Sheaf.Paper.CompletedCondensedCoefficients`,
`Sheaf.CategoryTheory.DerivedCategory.LeftDerivedTotalTensorExact`,
`Sheaf.Paper.FiniteCoefficientDescentTwoColimit`, `Sheaf.Paper.StratifiedLattice`,
`Sheaf.Paper.CoefficientHeartCommonStratification`, `Sheaf.Paper.CoefficientHeartFiltration`,
`Sheaf.AlgebraicGeometry.ProEtaleOpenClosedSequenceRingSheaf`,
`Sheaf.Paper.CartesianCoefficients`, and `Sheaf.SixFunctors.ScalarSixPullback`.
Also removed `Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses`: the
existing internal-module Grothendieck instance supplies enough injectives directly.
Retained `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility`
for the exactness of ordinary finite-field to algebraic-closure scalar extension.
Public imports stay unchanged. Added direct proof imports of the lisse descent and
lattice-filtration modules, the proved coefficient transport helper modules, and Mathlib's
extension-closed object properties.

The direct proof uses ordinary scalar extension and its proved comparison with locally
closed extension. It does not construct a derived scalar comparison or prove localization
exactness from a filtered-colimit presentation. The original direct dependencies on
`sk-prop-sfb-qlbar-colimit-x`, `lem-sfb-subfield-flat`,
`def-sfb-left-derived-exact`, and `det-prop-scalar-six-pullback` are not needed for those
steps. It uses `coefficient_finite_descent_lisse` rather than the full two-colimit theorem.

The common-stratification, stratified-lattice, cartesian-coefficient, open-closed, and
coefficient-heart-filtration arguments are supplied by the existing coefficient-heart and
lattice-filtration dependencies. They are no longer separate direct steps here. These
modules may remain needed transitively; no global module withdrawal is requested.

Removed obsolete direct tool-use approvals from this node: the Noetherian-open,
common-stratification, coefficient-heart-filtration, scalar-six-pullback, coefficient-colimit,
cartesian-coefficient, locally-Noetherian quasi-separated, open-closed-sequence, and
finite-subfield-flatness entries. Kept the existing long-exact, enough-injectives,
finite-type Noetherianity, and algebraic-closure flatness entries. The general ringed-site
K-injective-resolution entry is also removed; the proof uses `lem-sfb-modobj-grothendieck`.
No new approval is asserted by the packet.

## Where the brief, the DAG or earlier work was wrong

No statement correction was needed. The DAG's seven-step route contains a longer
ordinary-versus-derived scalar detour than the proof needs. Existing ordinary coefficient
transport and lattice-subquotient declarations already provide the necessary comparisons.
The unit route (extensions, strata, lattices) is preserved, including enlargement of the
descended field to contain E. Empty filtrations, zero pieces, and negative c are covered by
the generic finite-filtration induction and the unchanged natural-degree definition.

## Second reading by H5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
