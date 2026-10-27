## What changed

Replaced both original proof holes by complete Lean assembly, preserving their
signatures and the three public imports. The coefficient proof obtains the
completed traces from `diagonalTower_trace`, constructs the condensed initial
diagram by transport, extends that fixed diagram to a family, and combines
one-level finite comparisons with explicit every-level arithmetic. The base-change
proof constructs the actual three geometric squares and combines the non-torsion
comparison with the quotient comparison for each scalar-compatible diagram pair.

The completed-diagram transport is proved: its canonical right-derived functors
retain the full universal cochain unit; the class is conjugated through the
source and line endpoints; each trace is defined through the inverse comparison;
the two integration equations follow by naturality and cancellation. The root
map is constructed from its compatible finite projections and the preserved
module limit, not from a choice of a root generator. The uniformizer arithmetic
uses maximal-ideal membership of ell and ideal powers, so exponent n+1 already
kills O_E/(pi^(n+1)); it requires no choice of ramification index or cofinal level.

New proof-only imports are the component modules listed below. No existing
definition, theorem statement, source-library declaration, or target was changed.
No module was withdrawn. All new unfinished comparison results retain the
Cartier, whole-system, canonical-mate and normalized-root requirements of the
blueprint; none replaces the item with the same assertion under a new name.

## Proved and sorry left

This is a decomposition, not a net hole reduction: two original holes are
replaced by five component holes (closed-minus-added = -3). The two original holes are
closed by composition from the remaining statements:

- `diagonalTower_coefficients`.
- `diagonalTower_coefficients_baseChange`.

There are zero holes left in the assigned module and five new holes:

- `diagonalCompleted_frame` (`lem-diagonal-completed-frame`): the normalized
  coefficient equivalences, ordinary squares and supported
  source comparisons; no class, trace or integration assertion.
- `diagonalCoefficientFamily_extension`
  (`lem-diagonal-coefficient-family-extension`): scalar extension of an arbitrary
  fixed Z_ell diagram; no completed reference or quotient realization.
- `diagonalCoefficient_uniformizerFiniteComparison`
  (`lem-diagonal-coefficient-uniformizer-reduction`): one finite Cartier/trace
  comparison, with the killing exponent and finiteness supplied explicitly;
  no non-torsion family construction.
- `diagonalCoefficient_nonTorsionBaseChange`
  (`lem-diagonal-nontorsion-base-change`): class and trace squares before taking
  uniformizer quotients; it asserts none of FamilyPullback's quotient fields.
- `diagonalCoefficient_quotientBaseChange`
  (`lem-diagonal-quotient-base-change`): generic scalar/pullback compatibility for
  quotient diagrams from their integral square; no completed geometric input.

The universal-unit-normalized derived square is proved by
`diagonalExactSquare_exists`, reusing the existing exact-equivalence
Kan-extension theorem. The unfinished frame supplies only the ordinary
squares and source data; `CompletedOrdinarySquare.derive` constructs their
derived squares from the proved theorem.

The finite comparison uses the existing `QuotientCompatibility` interface
without expanding its dependent realization/line/trace data in the new theorem
statement. Its explicit annihilator, finiteness, invertibility and finite root
inputs are supplied by proved declarations. The earlier expanded existential
and structure presentations exceeded the file's limits and are not retained.

The five holes are the only occurrences of `sorry` in the delivered Lean files.
Proved new declarations are `integration_transport`,
`canonicalDiagonalUnit_universal`, `canonicalDiagonalRightDerived` (all fields),
`diagonalIntegralRoots_exists`, `diagonalIntegralRoots_unique`,
`diagonalUniformizer_annihilator`, `diagonalFiniteRoots_exists`,
`diagonalBaseSquares`, `diagonalExactSquare_exists`, and
`diagonalCompletedDiagram_realization`. `canonicalDiagonalUnit` is an explicit
natural transformation. No new definition contains a proof hole or takes an
arbitrary witness from an unproved existence theorem.

## No longer needed

Removed these direct proof imports from the assigned module:

- `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`.
- `Mathlib.AlgebraicGeometry.Noetherian`.
- `Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf`.
- `Sheaf.AlgebraicGeometry.BoundedContinuityDirectImage`.
- `Sheaf.AlgebraicGeometry.GeoCartierCycleClass`.
- `Sheaf.AlgebraicGeometry.GeoP1Cohomology`.
- `Sheaf.AlgebraicGeometry.ProEtaleAbelianClosedSupport`.
- `Sheaf.AlgebraicGeometry.ProEtaleCoefficientComparisonsPullback`.
- `Sheaf.AlgebraicGeometry.ProEtaleIntegralCoefficientLimit`.
- `Sheaf.AlgebraicGeometry.ProEtaleToposFunctorialityInverseImage`.
- `Sheaf.Paper.CartesianCoefficients`.
- `Sheaf.Paper.DiagonalTowerLimit`.
- `Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`.

These removals are local import pruning, not a claim that their mathematics can
be removed from the library. Most are still needed by the comparison components
and remain cited in those components' proof plans. In particular the Cartier,
finite trace, limit, exact inverse-image, closed-support, tensor, coefficient
and bounded-continuity nodes remain needed below the new holes. No adopted
source declaration was removed and no dependency of such a declaration was pruned.

`lem-weil-pbc-finite-type-over-noetherian` is not needed by this proof: all six
Noetherian instances are already explicit hypotheses of the unchanged original
statements. Removed just that obsolete entry from the existing top-level
`tool_uses`, retaining the other approvals in their order. No module is claimed
to be globally unreachable. The unit statement and every unit proof step remain.

## Where the brief, the DAG or earlier work was wrong

The original plan supplies the mathematical coefficient, limit, Cartier and
trace ingredients, but none of their existing declarations constructs the
normalized `Family`, `Reference`, finite-realization or `FamilyPullback` data.
The missing glue includes full universal-unit-normalized derived squares, not
just equalities of functor objects. The new component statements isolate those
requirements rather than treating unrelated derived models as definitionally equal.

Finiteness and ell-annihilation are separate facts. No discrete cofinal-only
argument suffices for the arbitrary uniformizer exponent in `FiniteReductions`.
The elementary ideal-power proof supplies every positive level directly.

The quotient base-change component does not rely on properness preserving
arbitrary coproducts or on inverse image preserving arbitrary limits. Its scalar
comparison uses the perfect two-term quotient resolution; the non-torsion
component uses bounded continuity only on the specified lines and explicit
limits only on the two specified systems. Empty schemes, ell=2, exponent n=0,
the bottom field, ramified uniformizers and nonflat base changes are covered.

## New nodes

`lem-diagonal-base-squares` (`Sheaf.Paper.DiagonalBaseSquares`): The three actual base-change squares. For any morphism g:Yprime→Y of schemes, the maps baseP and baseW in [def-sfb-diagonal-coefficient-source-pullback] satisfy BaseSquares g: they commute with the diagonal immersion and with each product projection. No flatness hypothesis is needed.

`lem-diagonal-canonical-right-derived` (`Sheaf.Paper.CanonicalDiagonalRightDerived`): The canonical diagonal right derived model. For an additive functor F:C→D between abelian categories with the indicated derived localizations and K-injective resolutions in C, construct a DiagonalRightDerived F as defined in [det-prop-diagonal-tower-limit]. Its functor is literally F.rightDerivedFunctor, and its full unit on every complex is rightDerivedFunctorUnitQ. It has K-injective computation, the canonical commutation with shifts and the triangulated structure.

`lem-diagonal-coefficient-family-extension` (`Sheaf.Paper.DiagonalCoefficientFamilyExtension`): Extend a fixed diagram to non-torsion coefficient fields. Let ell be prime and Y,P1_Y,P1_Y×_Y P1_Y Noetherian, with ell a unit on Y. For every Diagram d of [def-sfb-diagonal-coefficient-category] over condensed Z_ell with the fixed line zlLine, there exists a Family of [def-sfb-diagonal-coefficient-diagrams] whose Z_ell component is literally d. All integral, rational, closure and transition scalar squares are the specified adjoint-normalized ScalarCompatibility data. No completed reference or finite quotient realization is asserted.

`lem-diagonal-coefficient-integration-transport` (`Sheaf.CategoryTheory.IntegrationTransport`): Transport of an integration identity. Let C,D,Cprime,Dprime be categories, F:C→D and Fprime:Cprime→Dprime functors, U:C→Cprime and V:D→Dprime, and beta:F⋙V→U⋙Fprime a natural transformation. Let S,L in C and T in D, with arrows a:T→F(S), delta:S→L, trace:F(L)→T whose composite a F(delta) trace is id_T. Given primed endpoints and arrows, source and line comparisons s:U(S)→Sprime, h:U(L)→Lprime, and an isomorphism e:V(T)≅Tprime, suppose the source, class and trace comparison squares commute. Then aprime Fprime(deltaprime) traceprime=id_Tprime.

`lem-diagonal-coefficient-uniformizer-reduction` (`Sheaf.Paper.DiagonalCoefficientUniformizerReduction`): Compare an arbitrary positive uniformizer reduction with the finite Cartier class. Assume the completed diagonal reduction, completion, cycle-system and limit-arrow specifications on Y, and a Family with a Reference to that completed arrow [def-sfb-diagonal-coefficient-reference]. Fix a finite field E, a uniformizer pi and n≥0. Supply finiteness of the lifted residue ring, the explicit annihilation by ell^(n+1), invertibility of this exponent on Y,W, and kernel-normalized FiniteRoots on P,W. Then there exist a quotient Diagram d, its ScalarCompatibility with family.integral E, and QuotientCompatibility of [def-sfb-diagonal-coefficient-quotients]: finite realizations, root-projection-normalized line identifications and the canonical Cartier class and unit/Chern trace. No construction of a non-torsion Family and no geometric base-change square is asserted.

`lem-diagonal-completed-diagram-realization` (`Sheaf.Paper.DiagonalCompletedDiagramRealization`): Transport the completed diagonal diagram to condensed coefficients. In the setting of [lem-diagonal-completed-frame], let delta be a completed diagonal arrow and tq,t1,t2 the three completed traces in the prescribed projective models. Assume normalized sources a1,a2 satisfy a_i R_i(delta) trace_i=id. There exists a condensed Z_ell Diagram d as in [def-sfb-diagonal-coefficient-category], such that every Family whose Z_ell component equals d admits a Reference for the specified whole completed arrow delta and traces as in [def-sfb-diagonal-coefficient-reference]. No integral extension, rationalization or quotient assertion is made.

`lem-diagonal-completed-frame` (`Sheaf.Paper.DiagonalCompletedFrame`): Normalized completed coefficient frame. Let ell be prime, Y a scheme with ell invertible on global sections, and Y,P=P1_Y,W=P×_Y P Noetherian with the specified DiagonalTraceLocalizations. Fix the projection-normalized IntegralRoots maps at Y,P,W from [lem-diagonal-integral-root-map]. Given any three completed trace Results for q,p1,p2 and normalized supported sources for p1,p2 as in [det-prop-diagonal-tower-trace], there exist exact completed-to-condensed Z_ell equivalences at Y,P,W as in [def-sfb-diagonal-coefficient-reference], with those exact root maps, a normalized supported-source isomorphism, ordinary direct-image squares whose normalized derived squares are supplied by [lem-diagonal-completed-push-square] in the fixed canonical models [lem-diagonal-canonical-right-derived], and acyclic normalized supported sources on the condensed side. The supported-source derived squares commute. This assertion contains no diagonal arrow, trace morphism, integration equation or extension of coefficient fields.

`lem-diagonal-completed-push-square` (`Sheaf.Paper.DiagonalCompletedPushSquare`): Deriving ordinary coefficient squares with their full units. Given additive F:A→B and G:C→D between abelian categories, independently sized derived categories on A,B and C,D, exact equivalences U:A→C and V:B→D, right-derived models RF,RG as in [det-prop-diagonal-tower-limit], and an ordinary isomorphism F V≅U G, there exists ExactSquareOfUniverses with the full universal-unit normalization of [def-sfb-diagonal-trace-models]. Consequently an ordinary normalized coefficient square between CompletedRealizations of [def-sfb-diagonal-coefficient-reference] yields a CompletedPushSquare with precisely that ordinary comparison and normalized derived square.

`lem-diagonal-finite-root-map` (`Sheaf.Paper.DiagonalFiniteRootMap`): The kernel-normalized finite root comparison. For a scheme X and every positive N invertible in global sections, there exists FiniteRoots X N of [def-sfb-diagonal-coefficient-diagrams]. Its isomorphism is cartierRootsIso and its composite with the inclusion into pro-etale units is exactly the pulled-back etale kernel inclusion followed by cartierUnitsComparison.

`lem-diagonal-integral-root-map` (`Sheaf.Paper.DiagonalIntegralRootMap`): The normalized root map into the integral line. For prime ell, any scheme X, and any finite subextension E of the fixed algebraic closure, there exists IntegralRoots ell E X of [def-sfb-diagonal-coefficient-diagrams]. Its map from the actual root-tower limit to the underlying integral twist has, at each positive level, exactly the root-limit projection followed by the free-module unit. Thus the map is determined by these projections. Any two such IntegralRoots are equal.

`lem-diagonal-nontorsion-base-change` (`Sheaf.Paper.DiagonalNonTorsionBaseChange`): Base change before uniformizer reduction. In the standing separated finite-type setting of [sk-def-sfb-dc-setting], let g:Yprime→Y and fix the two derived reductions, their CompletionSpec and CycleSystemSpec, the two whole-system diagonal limits, and coefficient families with Reference data as in [def-sfb-diagonal-coefficient-reference]. Given BaseSquares g from [def-sfb-diagonal-coefficient-source-pullback], there exists NonTorsionPullback: residue-field invertibility on the two projective lines and products, projection-normalized CartesianAdicComparison for baseP and baseW, and PullbackCompatibility at Z_ell, every integral finite extension, every rational finite extension, and the algebraic closure. These use the actual Cartesian root comparisons. No uniformizer-quotient compatibility is asserted.

`lem-diagonal-quotient-base-change` (`Sheaf.Paper.DiagonalQuotientBaseChange`): Pullback of scalar-compatible quotient diagrams. Let ell be prime, g:Yprime→Y a morphism of Noetherian schemes, family and familyprime the two coefficient Families of [def-sfb-diagonal-coefficient-diagrams], and E a finite subextension. Suppose their integral E diagrams have PullbackCompatibility using the specified integral root comparisons. For every uniformizer pi and n≥0, and every pair of diagrams over O_E/(pi^(n+1)) with the ScalarCompatibility squares from the two integral E diagrams, there are maps mP,mW satisfying QuotientPullMap of [def-sfb-diagonal-coefficient-family-pullback] and PullbackCompatibility for these two quotient diagrams. No completed class, Reference, base field, or choice of Cartier arrow is required.

`lem-diagonal-uniformizer-annihilator` (`Sheaf.Paper.DiagonalUniformizerAnnihilator`): An explicit ell-power annihilator of every uniformizer quotient. Let ell be prime, E a finite intermediate extension inside Qbar_ell, and pi an element of its integer ring generating the maximal ideal. For every n≥0, ell^(n+1) is zero in ULift(O_E/(pi)^(n+1)), the actual completedResidue coefficient of [def-sfb-diagonal-coefficient-diagrams].

No change records are required: all existing statement signatures and definition bodies are unchanged.

## Second reading by U4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
