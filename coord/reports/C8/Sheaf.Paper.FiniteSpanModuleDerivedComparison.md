## What changed

The main theorem now uses the proved locallyFiniteCoefficientRing_realization to obtain
the normalized coefficient isomorphism. It applies finiteSpanScalarTransport to that
supplied isomorphism and its coefficient square, substitutes the returned theta equality,
and assembles every clause of the unchanged Properties predicate. Adjunction
transposition proves the inverse coefficient square, and cancellation of the invertible
pullback of theta proves invertibility of rho. These are separate proved arguments.

The exchange argument is written in Lean: localize ordinary_composition by
mapDerivedCategorySquareIso_comp, invert the compositor equation, paste the square with
square_pasting, invert the comparison cube, apply exchangeMate_cube and rewrite its two
vertical mates using field_normalization. This works for every derived object and needs
no exchange invertibility, properness or constructibility.

The 25 existing data/operation/predicate declarations move to
Sheaf.Paper.FiniteSpanModuleComparisonData, which the item publicly imports. Every
signature and existing attribute is retained; 21 bodies are byte-identical. Properties
and ExchangeProperty factor their final formulas through the new scheme-level
abbreviations DerivedNormalization and ExchangeEquation, preserving all binders and
the literal equations. The canonical derived adjunctions are also shared abbreviations.
DerivedComparisonFrame bundles the specified derived operations once, and the two
formulas specialize MateCondition and PullbackExchangeCondition, stated on an abstract
bundle; the latter extracts the commutative square before specializing ExchangeCondition.
The bundle uses the actual derived universe levels (objects u+2, morphisms u+1).
It is constructed field by field from the
original operations, with no choice or additional hypothesis. This prevents repeated field-dependent instance wrappers in
kernel checking. The split construction uses the same DerivedNormalization formula.
Sheaf.Paper.FiniteSpanScalarTransport is the new construction item. Its input is a
supplied natural coefficient-ring isomorphism, with no finite-field chart assumption;
its conclusion excludes the chart, direct coefficient square, inverse coefficient
square, rho invertibility and exchange assertions. No arbitrary data are
chosen in a definition. The main theorem's statement is unchanged.

The exchange specialization checks in about 1.6 seconds and the final theorem in about
20 seconds with profiling; the compile service accepts all three modules under its
per-file limit. Diagnostic options and test files were removed before final validation.

Final validation: the clean data module, scalar statement and item compile without
warnings, as do all
three unchanged direct importers: NativeEncodingDerivedOperations,
NativeWeilScalarFrobeniusCounit and NativeProperNaturalBaseChange. Their verification
copies were removed; the delivery contains only the item and its two new modules.

Change record: coord/changes/C8-finite-span-comparison-data-placement.md.

## Proved and sorry left

Closed the original named hole:
AlgebraicGeometry.ProEtale.FiniteSpanComparison.finiteSpanModuleDerivedComparison
(node lem-sf-finite-span-module-derived-comparison).

Added one named hole, whose whole proof is `by sorry`:
AlgebraicGeometry.ProEtale.FiniteSpanComparison.finiteSpanScalarTransport
(node lem-sf-finite-span-scalar-transport). This is the supplied-theta scalar module
transport construction of steps 1--7, with its source and complete argument in the
docstring. The coefficient realization, inverse coefficient square, rho invertibility and final
exchange calculation are outside this remaining hole.

Counts: one original hole closed, one lower hole added; zero holes remain in the item
module. This is a decomposition with net zero holes, not a complete proof of scalar
transport. The local categorical cancellation, compositor, square and exchange proofs
have no holes. The data module has zero holes and no changed mathematical definition.

## No longer needed

No mathematical module or node is withdrawn. Existing proof dependencies needed for
scalar transport remain dependencies of the new construction node. All earlier public
imports remain visible through the data module; the item now imports the data module
and the scalar construction, plus the three proved categorical pasting modules.
Removed redundant private imports from the relocated data file:
Sheaf.Paper.SectionModuleOperationsData,
Sheaf.AlgebraicGeometry.InternalModuleOperationsTransport,
Mathlib.CategoryTheory.Adjunction.Mates,
Mathlib.CategoryTheory.Functor.Derived.Adjunction,
Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor,
Mathlib.Algebra.Homology.DerivedCategory.KInjective,
Sheaf.CategoryTheory.KInjectiveDerivedMapComputation, and
Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses.
The split statement needs only the public data import; its five provisional private
proof imports were also removed: SectionModuleOperationsData,
InternalModuleOperationsTransport, SectionDerivedPushpullNormalization,
KInjectiveDerivedMapComputation and RingedSiteKInjectiveResolutionsMixedUniverses.
Their mathematical dependencies stay in the scalar construction node for its future
proof. The resolution dependency follows the current node attachment to the mixed
universe module. The definitions required by the data file are already public through
its retained public imports.

The original tool-use approvals are retained because their mathematics is still used
in the scalar construction. No unit route is bypassed.

## Where the brief, the DAG or earlier work was wrong

The rework row was checked before copying. The current source and quarantine copy
both preserve the original theorem and its single hole; neither is withdrawn.
The rework's missing transitive dependency SfP1ChartExchange is supplied by the compile
service's unpublished-dependency overlay. There is no need to remove its consumers.

The original plan gives a valid conceptual separation between normalized scalar
transport and exchange, but no existing declaration supplies the complete supplied-theta
scalar transport construction. The existing coefficient realization theorem is proved.
The exchange step can use the already proved mate-cube and exact-square composition
lemmas instead of expanding all units and counits concretely.

Edge cases checked in the split statement: arbitrary schemes, empty schemes, identity
and composite morphisms, rank-zero finite bases, unbounded complexes and unrestricted
derived objects. The field assumptions are confined to field_normalization and exchange.
The helper takes an actual ring isomorphism and its coefficient square and does not
assert normalization for an arbitrary choice of derivedPushComparison.

## New nodes

`def-sf-finite-span-module-comparison-data` attaches the 25 moved declarations, the two formula abbreviations and the
two shared derived adjunction abbreviations and the canonical derived-operation bundle with its three generic predicates,
and records their construction, including the explicit
scalar restriction equivalence. It introduces no new mathematical object. All original
signatures and attributes remain; the two predicate bodies factor literal formulas, and the exchange abbreviations share canonical adjunctions.

`lem-sf-finite-span-scalar-transport` is the remaining scalar transport construction
for a supplied theta and coefficient square. Its thirteen normalization clauses are the
corresponding clauses of Properties, with d.theta fixed to that supplied theta; it
omits the finite-field chart, the direct and inverse coefficient squares, rho
invertibility and final exchange assertions. The main theorem proves all of these
omitted clauses in Lean, so the split does not restate the original
conclusion under a new name.

## Second reading by C8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
