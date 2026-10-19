## What changed

The item assembles the relative calculation and canonical base-change conclusions from a proved
affine-line unit theorem and two genuinely separate source results: the punctured-line calculation
and its coordinate-naturality/exchange argument, conditional on both relative calculations. All
original theorem binders, universes, visibility and conclusions stay unchanged. Geometric points
require no finite-type hypothesis.

`relative_line_cohomology` is proved from the existing `affineLineOrdinaryInvariance` at twist
zero. Its proof identifies the actual coefficient sheaves with constants, compares bounded-below
and unbounded adjunction units, and uses a primitive root and scalar extension to trivialize the
finite root line. Naturality transports the unit isomorphism; the specified coefficient pullbacks
are isomorphisms. The item also proves affine-line exchange directly from the mate-unit identity,
rather than leaving it in the exchange split. Positive line cohomology vanishes by transporting the
degree-zero t-structure bound along the unit.

The seven canonical definitions move to `PurityRelativeKummerMaps`, publicly reexported by the item
to avoid an import cycle. Every original constant signature and visibility is preserved. Four
bodies are verbatim; three insert explicit reflexive coefficient-complex identifications, avoiding
expensive normalization of localization morphisms. The general definition lemma is proved by `rfl`,
with two Boolean proof abbreviations; functoriality and identity laws remove the inserted
transports, leaving the same actual pullback, coordinate class and Kummer edge map. No arbitrary
isomorphism or witness replaces them. The coordinate-naturality equation is named by the
irreducible `CoordinateKummerNaturality` predicate so that its identical uses share one statement
without repeated localization-type normalization. Its body is the exact equation, with no
assumption or proof hole. The change record includes verbatim old/new definitions and the 176
existing transitive consumers plus the item. No existing consumer is adapted. The established
public imports are retained to preserve cached instance elaborations; unused proof imports are
removed.

The full five-module overlay compiled successfully with the unchanged launcher and limits
(`compile-specialized-reflexive-api.log`): maps 53.9 s, exchange 5.6 s, affine-line cohomology 39.3
s, punctured statement 4.5 s, and the item 16.9 s. Both unchanged direct importers also compile
against that overlay: `PurityAffineLineOrientation` (22.3 s) and
`PurityAffineLineOrientationUniqueness` (8.2 s), as recorded in
`compile-unchanged-consumers-final.log`. A concrete coordinate-identity scratch check reached the
compile limit; the transport argument uses the general Mathlib equality-map and functor identity
laws. Both generic transport identities compile in an abstract category in 1.3 s
(`compile-generic-coordinate-transports2.log`), covering the equality maps in the coordinate class
and coefficient pullback. The required dry run passed (temporary commit `e0d79440e5`, review class CODEX);
nothing was pushed by that command. It noted that the affine-line axiom probe
reached 60 seconds when added to recompilation. A separate probe of both compiled theorems passed in 3.2 seconds
(`compile-final-axiom-probe.log`): each uses `propext`, `Classical.choice`,
`Quot.sound`, and the expected `sorryAx` from declared dependencies. The merge
also repeats the probe.

## Proved and sorry left

The item source contains a complete proof of `WeilConjectures.PurityFiniteSetting.relative_kummer`,
checked in the full five-module overlay. The new theorem
`WeilConjectures.PurityFiniteSetting.relative_line_cohomology` (`lem-pur-relative-line-cohomology`)
is proved, including all private comparison and unit lemmas. The public coefficient-complex
equality lemma is proved by reflexivity and its two Boolean proof abbreviations are
specializations; all definitions contain actual constructions.

Two holes are added, each the entire proof of a named public theorem:

- `WeilConjectures.PurityFiniteSetting.relative_punctured_cohomology`
  (`lem-pur-relative-punctured-cohomology`): punctured degree-zero unit, actual
  coordinate generator, and higher vanishing; no line or base-change assertion.
- `WeilConjectures.PurityFiniteSetting.relative_kummer_exchange`
  (`lem-pur-relative-kummer-exchange`): actual coordinate naturality and canonical
  punctured derived exchange, assuming the relative conclusions on both bases;
  no relative calculation or affine-line exchange assertion.

The item has zero remaining source holes; one original hole is replaced by two strictly smaller
source results. This is a decomposition, not a net proof: its arithmetic before the ledger's
import-closure calculation is 1 minus 2 = -1. There are no holes in definitions or private
declarations and no added axioms. The earlier attempt's third split, the affine-line calculation,
is proved in this session; its affine-line exchange part is also handled directly in the item.

## No longer needed

The earlier attempt's unused `PurityRelativeKummerConclusions` and `PurityRelativeKummerBaseChange`
scratch modules are absent from the packet. The retained generic mate helper is now used in the
affine-line exchange proof. No existing library module or node is claimed globally unnecessary: the
old punctured-line and exchange dependencies are retained in the corresponding new nodes. Ordinary
affine-line invariance avoids repeating its fibre calculation and stalk transport in the line
lemma. The blueprint unit's relative calculation, actual coordinate generator and canonical
exchange route are preserved.

These original direct imports are removed from the item. The old public roots are reexported
through the maps module. Other entries were unused direct proof imports. This is import pruning,
not a claim that every listed module is unnecessary to the two retained source arguments or to the
rest of the library:

- `Sheaf.Paper.PurityAffineLineDatum`
- `WeilConjectures.Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed`
- `Sheaf.AlgebraicGeometry.SmoothBaseChange.HigherDirectImageForgetComparison`
- `Sheaf.AlgebraicGeometry.EtaleModuleInjectiveForgetAcyclic`
- `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusHomology`
- `Sheaf.CategoryTheory.Abelian.RightDerived.AcyclicComparisonNatural`
- `WeilConjectures.CategoryTheory.Abelian.RightDerived.Acyclic`
- `Sheaf.AlgebraicGeometry.EtaleModuleCohomologyForget`
- `Sheaf.AlgebraicGeometry.ExchangeForgetCoefficients`
- `WeilConjectures.AlgebraicGeometry.Sites.Kummer`
- `Sheaf.CategoryTheory.SiteCohomologyPullback`
- `WeilConjectures.CategoryTheory.SiteMorphismComposition`
- `WeilConjectures.CategoryTheory.SiteContinuousPushforwardSheaf`
- `Sheaf.CategoryTheory.Abelian.HorseshoeDeltaFunctor`
- `Mathlib.Algebra.Homology.HomologySequence`
- `Mathlib.CategoryTheory.Abelian.RightDerived`
- `WeilConjectures.CategoryTheory.DeltaFunctor`
- `Sheaf.CategoryTheory.Abelian.RightDerived.FullLongExactSequence`
- `Mathlib.Algebra.Homology.ShortComplex.ShortExact`
- `WeilConjectures.Mathlib.CategoryTheory.Abelian.RightDerived`
- `WeilConjectures.AlgebraicGeometry.Sites.Gm`
- `WeilConjectures.AlgebraicGeometry.Sites.ConstantSheafSections`
- `WeilConjectures.AlgebraicGeometry.Curve.CohomologicalDimension`
- `Sheaf.AlgebraicGeometry.StrictHenselizationStalkFormula`
- `Sheaf.AlgebraicGeometry.AbelianHigherDirectImagePresheaf`
- `WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Theorem`
- `Sheaf.AlgebraicGeometry.StrictlyHenselianConstantCohomology`
- `Sheaf.AlgebraicGeometry.BaseChangeMapAbelianAndSets`
- `Mathlib.Algebra.Homology.DerivedCategory.HomologySequence`
- `WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint`
- `Sheaf.AlgebraicGeometry.CohomologyPullbackCanonicalArrows`
- `WeilConjectures.AlgebraicGeometry.CohomologyPullbackDerivedUnit`
- `Sheaf.AlgebraicGeometry.EtaleInverseImageModulesExact`
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous`
- `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct`
- `Sheaf.AlgebraicGeometry.EtaleInverseImageAlgebraicStructures`
- `Sheaf.Paper.KunBcMapOnCohomology`
- `WeilConjectures.SixFunctors.BaseChange.Square`
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance`
- `WeilConjectures.SixFunctors.Etale.LowerShriek.EtaleMap`
- `Mathlib.Algebra.Homology.ShortComplex.PreservesHomology`
- `Sheaf.AlgebraicGeometry.ComparisonDirectImage`
- `Sheaf.AlgebraicGeometry.ProEtaleSiteComparison`
- `Sheaf.AlgebraicGeometry.ComparisonDirectImageCanonicalMate`
- `Sheaf.AlgebraicGeometry.ComparisonGlobalCohomology`
- `WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange`
- `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Constructible`
- `WeilConjectures.CategoryTheory.DerivedCategory.Constructible`
- `WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`
- `WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.TStructure`
- `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Comparison`
- `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperLowerStar`
- `Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives`
- `WeilConjectures.CategoryTheory.DerivedCategory.Adjunction`
- `WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.Defs`
- `WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MapDerivedCategory`
- `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Defs`
- `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusComp`
- `WeilConjectures.CategoryTheory.GrothendieckAbelian.HasColimitsOfShape`
- `WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory`
- `WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution`
- `WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.TensorColimits`
- `WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf`
- `WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus`
- `WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal`
- `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs`
- `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Defs`
- `Sheaf.AlgebraicGeometry.AbelianEtaleProEtaleCohomologyComparison`
- `Sheaf.AlgebraicGeometry.AffinePuncturedLineAlgebra`
- `Sheaf.AlgebraicGeometry.CompactSupportComparisonUnit`
- `Sheaf.AlgebraicGeometry.ComparisonGlobalCohomologyFiniteNormalized`
- `Sheaf.AlgebraicGeometry.FixedComparisonDirectImageMate`
- `Sheaf.AlgebraicGeometry.KummerCoefficientBaseChange`
- `Sheaf.CategoryTheory.LeftModuleDerivedEvaluationForget`
- `Sheaf.Paper.ComparisonPullbackExact`
- `Sheaf.Paper.FiniteDirectImageComposition`
- `Sheaf.Paper.PurityFiniteKummerLevel`
- `Sheaf.Paper.PurityFiniteSetting`
- `Sheaf.Paper.SiteComparisonEdgeSection`
- `WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact`
- `WeilConjectures.CategoryTheory.Abelian.HorseshoeDeltaFunctor`
- `WeilConjectures.CategoryTheory.Abelian.RightDerived.AcyclicComparisonNatural`
- `WeilConjectures.CategoryTheory.Abelian.RightDerived.FullLongExactSequence`
- `WeilConjectures.SixFunctors.ProEtale.Comparison.CohomologicalDimension`

The parent's direct proof dependencies now record the maps, line and punctured calculations,
punctured exchange, mate-unit compatibility and the coefficient and cohomology definitions actually
used. Dependencies of the remaining source arguments are listed in their own nodes, rather than
imported unused in the item.

## Where the brief, the DAG or earlier work was wrong

The retained earlier report called its proposed split statements existing library dependencies and
claimed validation without current compiler evidence. They were new statements without nodes. This
packet supplies their nodes, proves the line result and the affine-line exchange, and records the
two remaining holes explicitly.

Existing abstract multiplicative-group cohomology isomorphisms do not identify the actual
coordinate Kummer generator or canonical exchange. The remaining source steps require those actual
maps and arbitrary bases; neither an arbitrary generator nor smooth base change with the wrong
smooth side suffices.

Detailed profiling located expensive conversions between named degree-zero coefficient complexes
and their single-complex expansions. The explicit reflexive identifications repair these
definitions. All compile limits and launcher scripts are unchanged. Removing redundant public roots
caused a fresh timeout, so the established headers are retained. No experimental predicate
structure or altered functor is retained.

The retained attempts `compile-resume.log` (2026-10-19 05:21:51 UTC) and `compile-mate.log`
(08:22:50 UTC) precede the current `.budget.start` (17:07:49 UTC). The launcher's reference clock
changed across resumed attempts. The packet and work were retained; no budget file, check marker or
launcher script was edited to alter that clock.

## New nodes

`def-pur-relative-kummer-maps`: the seven canonical definitions, the explicit
coefficient-complex identities and the same coordinate class with its equality
maps displayed. Module `Sheaf.Paper.PurityRelativeKummerMaps`. Change record:
`coord/changes/f4-relative-kummer-maps.md`.

`lem-pur-relative-line-cohomology`: the specified affine-line relative unit is a
derived isomorphism for either coefficient choice over any k-base. Module
`Sheaf.Paper.PurityRelativeLineCohomology`; proved.

`lem-pur-relative-punctured-cohomology`: punctured degree-zero unit, actual
coordinate generator and higher vanishing. Module
`Sheaf.Paper.PurityRelativePuncturedCohomology`; one named hole with source and proof.

`lem-pur-relative-kummer-exchange`: coordinate naturality and canonical punctured
exchange, conditional on the relative calculations. Module
`Sheaf.Paper.PurityRelativeKummerExchange`; one named hole with source and proof.

The four new nodes have search evidence and source provenance. The parent
`prop-pur-gm-relative-kummer` records the actual line-unit, mate-unit and punctured assembly route.
No unit statement or realized unit step is removed.

## Second reading by F4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
