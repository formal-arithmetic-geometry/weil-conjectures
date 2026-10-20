## What changed

FiniteLevelRectangle is proved from the proved pointwise coefficient_exchange_of_counit_at
mate theorem and the new pure pullback/reduction compatibility statement
fourCornerReductionPullback_square. The proof retains exactly the specified
finite-linear exchange and projection arrows. Private proved counit interfaces
keep the formal mate calculation separate from the chosen derived adjunctions.
No target signature is changed. The chosen comparison data are unchanged.
The pointwise API is proved in CoefficientExchange; the existing universal theorem
retains its signature and its proof applies the pointwise variant. The change
record is coord/changes/Q4-finite-rectangle-pointwise-mate.md.

Also proved fourArrowIntegralCoefficients_comm and
fourArrowFiniteCoefficients_comm in the unclaimed dependency
ProperBaseChangeFourArrows, directly from fourCornerCoefficientCoherence and
the equality of composite scheme morphisms. No source-library file changes.
The proof-only change record is
coord/changes/Q4-finite-rectangle-coefficient-proofs.md.

ProperBaseChangeFourCorners now types its four functors using the same raw
DerivedCategory interface as adicDatumReduction,
exposes the two geometric adjunctions with those types, and types the existing
fourCornerReductionPullback using adicDatumReduction. The functors and adjunctions
are ordinary definitions with unchanged geometric values. ProperBaseChangeFourArrows
similarly exposes typed integral/finite comparisons and exchange transformations;
its finite exchange and tuple use those same transformations. These interfaces keep
component types from expanding the chosen derived functors. The decisive fix is
using identical hidden category arguments in every Functor.obj expression: mixing
the fourCornerDerived abbreviation and raw DerivedCategory made the kernel unfold
the entire chosen reduction functor to compare otherwise identical reduced objects. Their records are
coord/changes/Q4-finite-rectangle-comparison-type.md and
coord/changes/Q4-finite-rectangle-finite-exchange-type.md.

AdicCoefficientDatumCompleted gives adicDatumReduction an explicit derived-category
return type. Its scalar-extension, counit, and tensor-section constructors retain
the same data with explicit universe arguments and unfolding during elaboration.
A generic adicDatumSiteModulesAbelian helper keeps the site variable in the
coefficient-universe proof applications, and adicDatumModulesAbelian specializes
that existing Mathlib construction to the geometric Abelian data; local priorities beginning at adicDatumReduction select it and the existing
standard geometric derived-category instance. The sheafification criteria are
Prop-valued, but Abelian itself carries data, so fixing its interface matters.
No global instance priority changes. The record is
coord/changes/Q4-finite-rectangle-reduction-type.md.

The new pointwise mate theorem takes the four exchange/projection maps only at the
object in question, with their four counit equations. No naturality law for these
four maps is used in its calculation. The existing uniform theorem keeps its
verbatim signature and applies the pointwise API to its components. The geometric
cube is expressed by coefficientPullbackSquare, the original explicit equation
with fixed category/functor arguments. Neither generic addition has any sorry.

Validation: all six delivered Lean files compile with the normal project limits and
no warnings. The rectangle takes 5.1 seconds. Unchanged consumer sources also compile
against the delivery: FiniteLevelRingedProEtaleBaseChange (9.2 s),
IntegralResidueExchangeAlgebra (13.1 s), SequentialDerivedInverseLimitCompleted (3.5 s),
IntrinsicCompletionCompleted (27.4 s), and A2's FiniteReductionReconstructionCompleted
(4.1 s). Their temporary source copies are removed from the packet; no adaptation
of another holder is needed. The original rectangle signature and the existing
uniform coefficient_exchange_of_counit signature are verbatim unchanged.

## Proved and sorry left

Closed existing holes:

- AlgebraicGeometry.Scheme.fourArrowIntegralCoefficients_comm: proved from the
  integral composition clause of fourCornerCoefficientCoherence.
- AlgebraicGeometry.Scheme.fourArrowFiniteCoefficients_comm: proved from its
  finite composition clause.
- AlgebraicGeometry.Scheme.properBaseChangeFiniteLevelRectangle: complete Lean
  mate calculation from the new pullback/reduction coherence statement. This is
  a decomposition, not an additional standalone hole reduction.

Added one hole:

- AlgebraicGeometry.Scheme.fourCornerReductionPullback_square, in
  Sheaf.Paper.FiniteReductionPullbackCoherence, node
  lem-weil-pbc-finite-reduction-pullback-coherence.

The item has zero remaining sorries. ProperBaseChangeFourArrows retains its two
unchanged holes, AlgebraicGeometry.Scheme.fourArrowProjection_isIso and
AlgebraicGeometry.Scheme.fourArrowFiniteExchange_isIso (both attached to
node def-weil-pbc-four-arrows). ProperBaseChangeFourCorners also retains its eight unchanged holes:
fourCornerCoefficientTowerNaturality, fourCornerProjectionComm,
fourCornerFiniteTransitionComm, fourCornerCoefficientCoherence,
fourCornerRestrictionPushforward_exists, fourCornerRestrictionPullback_exists,
fourCornerOrdinaryComparison_transition, and fourCornerReductionPullback_exists
(all in AlgebraicGeometry.Scheme, node def-weil-pbc-four-corners).
AdicCoefficientDatumCompleted: this delivery also proves ten of its twenty former
holes (reviewer correction; the earlier text called all twenty unchanged):
adicDatumScalar_exists, adicDatumModel_exists, adicDatumRestriction_exact,
adicDatumOrdinaryUnit_exists, adicDatumOrdinaryAdjunction_exists,
adicDatumOrdinaryTransition_id, adicDatumOrdinaryTransition_comp,
adicDatumOrdinaryTower_additive, adicDatumModelComplexRestrictionIso_exists and
adicDatumModelReductionComparison_isIso (the first five axiom-free, the rest
through still-`sorry` statements). Ten unchanged holes remain, all in
AlgebraicGeometry.Scheme and attached to def-weil-pbc-adic-coefficient-datum:
adicDatumFiniteCoefficientIso_exists, adicDatumFiniteCoefficientIso_natural,
adicDatumQuotients_exists, adicDatumAdjunction_exists, adicDatumComplexCounit_isIso,
adicDatumOrdinaryTransition_exists, adicDatumTowerDerived_exists,
adicDatumBalance_exists, adicDatumExtension_kflat, and adicDatumBalance_cocycle.
CoefficientExchange has zero holes, including its new pointwise theorem.
There are twenty-one sorries in the six delivered Lean files: ten unchanged
coefficient-data holes, eight unchanged corner holes, two unchanged arrow holes,
and the new coherence statement. Thirteen old bodies are closed and one new body is
holed. No axiom-free target claim is made.

## No longer needed

Removed proof imports from FiniteLevelRectangle:

- Sheaf.Paper.ProjectionFormulaBaseChangeNaturality
- Sheaf.AlgebraicGeometry.ProfiniteCoefficientInverseImage
- Sheaf.AlgebraicGeometry.ProEtaleAmbientRingedExchange
- Sheaf.Paper.AdicCoefficientDatum
- Sheaf.Paper.CondensedAmbientExchange
- Sheaf.Paper.FourArrows
- Sheaf.Paper.FourCorners
- Sheaf.Paper.PerfectProjectionFormula

AmbientRingedExchange and coefficient data remain available through the public
FourArrows dependency; only their redundant direct imports are removed. The
rectangle proof no longer directly needs the nodes
lemma-weil-pbc-projection-formula-base-change-naturality or
lemma-weil-pbc-perfect-projection-formula, nor the newer AdicCoefficientDatum
presentations in FourArrows/FourCorners. Perfect projection is still needed to
certify the horizontal arrows as isomorphisms in ProperBaseChangeFourArrows;
no global withdrawal of that node or its dependencies is requested. No module
is deleted, and the unit route is retained. The proof node now records its
actual mate and pullback-coherence dependencies.

## Where the brief, the DAG or earlier work was wrong

The planned general tensor/projection rectangle does not directly supply the
finite-linear coefficient comparison cube for the named adicDatumReduction
and fourCornerReductionPullback normalizations. The attached module uses the
older ProEtaleAdicCoefficientDatum API, whereas several original proof imports
now expose the newer AdicCoefficientDatum API. Keeping quotient scalar actions
requires a comparison argument; the new node isolates exactly that argument,
without any direct images or exchange-invertibility claim.

The new statement was checked mathematically for identity squares, index zero
(which denotes exponent one), zero coefficient quotients, the zero ideal,
empty schemes, and unbounded derived inputs. Its proof uses flat-term K-flat
representatives, not an unjustified boundedness or flat-quotient hypothesis.
Both geometric routes use the same balanced tensor scalar and fibre-product
pasting map. What remains to formalize is the comparison of these ordinary
normalizations and its descent through the specified K-flat normalization
interfaces, not the adjunction calculation, which is Lean code in this packet.

## New nodes

lem-weil-pbc-finite-reduction-pullback-coherence states compatibility of reduction
with the canonical geometric pullback square. It applies to arbitrary integral
objects on Y, has no properness/completion/origin hypotheses, and involves no
pushforward functor. It is a genuine independent pullback coherence result from
Stacks 07A4 and 0D6D underlying the coefficient specialization of 0E48. The node
records the ordinary comparison, K-flat descent, and equality-transport steps,
with the actual Lean signature and three kinds of Mathlib search. It is not a
renaming of the four-arrow exchange rectangle.

Change records: coord/changes/Q4-finite-rectangle-coefficient-proofs.md,
coord/changes/Q4-finite-rectangle-comparison-type.md,
coord/changes/Q4-finite-rectangle-reduction-type.md,
coord/changes/Q4-finite-rectangle-pointwise-mate.md, and
coord/changes/Q4-finite-rectangle-finite-exchange-type.md.

## Reviewer correction (2026-10-21)

The statement of fourCornerReductionPullback_square is now the explicit cube equation
instead of Adjunction.coefficientPullbackSquare, so the new node does not depend on a
definition owned by lem-weil-pbc-coefficient-exchange-mates outside its stmt_deps. The
rectangle still passes it as the hcube argument; the predicate unfolds to it.

## Second reading by Q4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
