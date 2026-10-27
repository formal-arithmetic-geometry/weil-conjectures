## What changed

Proved `WeilConjectures.commonStagePullback_descent_from_data` in
`Sheaf.Paper.DerivedPullbackTensorHom` from the already proved
`StageSystem.coefficientPairFunctor_exists`, imported privately from
`Sheaf.CategoryTheory.StageSystemFunctorDescent`. A proved private helper performs
specification transport over abstract stage systems, preserving unique existence;
the concrete theorem specializes it using the supplied component identifications.
The existing upper pullback existence theorem still combines comparison data with
this descent theorem. Updated the two corresponding existing DAG proof records.

A delivery compile exceeded 60 seconds. Profiling identified expensive concrete
naturality and specification conversions. Replaced the former with the proved
private helper `map_naturality_iso_components`, moved the latter to an abstract
private helper, and made `rationalDerivedInternalHom`, `ScalarLocalization.composition` and
`StageSystem.PairCategory.mkHom` locally irreducible in the common-stage section.
The trace showed the representative constructor and scalar composition being
expanded while comparing the generic and concrete specifications. The concrete
descent call also supplies its stage-category instances explicitly. Removed that naturality step's transparency overrides and
all temporary profiling options. The file still exceeded the limit, so extracted
its already proved generic scalar-localization calculus into four new modules:

- `Sheaf.CategoryTheory.DerivedScalarLocalizationFunctor`,
  `OperationsScalarLocalization.functor_existsUnique` (formerly private
  `rawFunctor_existsUnique`).
- `Sheaf.CategoryTheory.DerivedScalarLocalizationIso`,
  `OperationsScalarLocalization.iso_existsUnique` (formerly private
  `rawIso_existsUnique`).
- `Sheaf.CategoryTheory.DerivedScalarLocalizationBilinearComparison`,
  `OperationsScalarLocalization.bilinearComparison_existsUnique` (formerly private
  `semilinearTensorIso_localize`, together with its private generic helpers).
- `Sheaf.CategoryTheory.DerivedScalarLocalizationRestrictedHom`,
  `OperationsScalarLocalization.restrictedHom_existsUnique` (formerly private
  `homLocalization_existsUnique`, together with its private construction).

All four exported helpers are fully proved. They are imported privately by the
finite/rational construction module described below.

After these improvements, a delivery compile still exceeded 60 seconds. Split the
already proved finite, integral and rational constructions and scalar comparisons
into `Sheaf.Paper.FiniteRationalDerivedOperations`, leaving the common-stage part
in the item. The item retains all its original public imports and adds one public
import of this module, so every old name remains available. All 39 original public
definitions/abbreviations are preserved verbatim, as are all existing public theorem
signatures. The extracted module privately imports the four generic helpers; their
new names are not re-exported by the item. Thus the existing exported interface and
all definitions are unchanged. No consumer or source-library module is changed. No statement is weakened and no
arbitrary witness is chosen. The helpers' existing unique-existence constructions
continue to determine all chosen functors and isomorphisms uniquely.

## Proved and sorry left

Closed one of the item's four original holes:
`WeilConjectures.commonStagePullback_descent_from_data`
(`lem-weil-common-stage-pullback-descent-from-data`). No holes added or split off.
All five extracted modules contain zero holes.

Three original holes remain, with their original statements:

- `WeilConjectures.commonStagePullback_comparison_data`
  (`lem-weil-common-stage-pullback-comparison-data`).
- `WeilConjectures.commonStageDerivedTensor_existsUnique`
  (`def-weil-derived-pullback-tensor-hom`).
- `WeilConjectures.commonStageDerivedInternalHom_existsUnique`
  (`def-weil-derived-pullback-tensor-hom`).

## No longer needed

Removed or relocated these private imports from the item:

- `Sheaf.Paper.IntegralDerivedPullbackLinear`,
  `Sheaf.CategoryTheory.BilinearScalarLocalization`,
  `Sheaf.Paper.IntegralCompletedTensorBilinear`, and
  `Sheaf.Paper.IntegralDerivedHomBilinear` moved to
  `FiniteRationalDerivedOperations`, where their proofs are used.
- `Sheaf.CategoryTheory.SemilinearScalarLocalization` is imported by the extracted
  generic functor helper that uses it.
- `Mathlib.LinearAlgebra.TensorProduct.Tower` is imported privately by the extracted
  permitted-Hom helper that uses base-change distribution.
- The four newly added generic helper imports moved from the item to the
  finite/rational module.

The root node now cites the finite/rational extraction node and the two existing
common-stage pullback intermediates directly. Its previous scalar-localization,
linearity and bilinearity dependency edges are recorded at the extracted node and
its generic helper nodes instead. Every one remains needed transitively. The general
descent dependency is recorded at the fixed-family descent node.

No existing mathematical node or module becomes unnecessary. In particular, the
comparison-data and scalar-extension coherence work remains needed by the upper
pullback construction. The fixed-family descent proof uses the general declared
descent theorem and needs no additional specialized quotient construction.

## Where the brief, the DAG or earlier work was wrong

The descent node originally had an empty `proof_deps` although its proof plan called
for the StageSystem descent constructor. Its dependency list now explicitly names
`lem-sbc-coherent-pair-functor-descent`.

The latest blueprint places `def-weil-derived-pullback-tensor-hom` under
`sec-proetale-coefficients/sk-prop-sf-open-closed-triangle` and defines the operations
uniformly for condensed coefficients, with scalar/reduction compatibility as a theorem.
The attached historical node and this module describe finite/integral/rational/common-stage
constructions instead. This delivery preserves that existing interface and proves its
fixed-family descent theorem; it does not resolve the broader blueprint synchronization.
The new nodes precisely record the existing rational-operation scalar calculus.

## New nodes

`lem-sf-localized-functor` records the extracted normalized unique additive extension
of an R-linear functor, proved using the existing semilinear extension and tensor
induction. It is a proved technical specialization, not a new proof obligation.

`lem-sf-localized-natural-iso` records normalized unique comparison isomorphisms for
additive raw-localization functors. Unlike the existing triangulated descent lemma,
it assumes no shifts or triangles, and allows any coefficient function satisfying
the supplied pure-tensor formulas.

`lem-sf-localized-bilinear-comparison` records the extracted comparison between two
composites of localized bilinear functors and a semilinear scalar functor. It uses
double tensor induction; the existing bilinear-localization theorem constructs a
single bifunctor and does not assert this comparison.

`lem-sf-localized-permitted-hom` records the extracted contravariant bilinear
localization on a permitted full subcategory. Only the implication from localized
permitted pairs to integral permitted pairs is used. Empty domains and zero
coefficient localizations require no additional hypotheses.

`def-sf-finite-rational-derived-operations` records the already proved finite,
integral and rational clauses of the original node, with their normalized scalar
comparisons. It moves existing declarations and their definitions without changing
any of them. The original module re-exports them. This is a file split after the
profiled definition-abstraction improvements, and adds zero holes. All six delivered
Lean modules passed the standard `lcompile.py --all` check without warnings. The
unchanged direct importer `Sheaf.Paper.CommonStagePullbackRepresentativeLinearity`
also compiled against this packet. Its temporary sandbox copy was removed.

The four generic nodes cite Stacks Tags 00CV/00CX and the exact rational-operation
clause of the original node. The finite/rational extraction cites the original
source and records the corresponding clauses. Every new node records
LeanFinder/Loogle/Mathlib-source searches and has a complete implementation. Blueprint-wide searches for scalar localization
and bilinear constructions found no identical imported blueprint statement.
There are no change records because no existing public interface was changed.

## Forced adaptations

None in other modules. Reviewer correction (2026-10-27): two direct importers,
`Sheaf.Paper.FiniteProductFieldCoefficientDescent` and
`Sheaf.Paper.RationalRestrictionComparisonCoherence`, use
`import all Sheaf.Paper.DerivedPullbackTensorHom` and call the item's former private helpers
`rawBilinearIso_existsUnique`, `bilinearAdd`, `bilinearPost`, `bilinearPre`, `map_heq`,
`prod_hom_heq` and `rationalTensor_spec`. The extraction had moved these helpers to other
modules, where `import all` of the item no longer reaches them. Against the delivered files,
FiniteProductFieldCoefficientDescent failed with
`Unknown identifier rawBilinearIso_existsUnique` and `Unknown identifier rationalTensor_spec`.
The item now keeps verbatim private copies of these helpers, together with `chosenUnique_spec`,
and both importers compile against it. The claim above that "no consumer is affected" held only
for importers that do not use `import all`.

## Second reading by K2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
