## What changed

Decomposed coef_rational_operations into three independent steps: full rational Hom
identifications and scalar evaluation, scalar-compatible exceptional dual formulas, and
the structure-map dualizing comparison. The parent obtains the existing normalized
exceptional systems and simultaneous rational Verdier data, chooses existential coherent
dualizing witnesses inside its proof, applies the three steps, and assembles every
original conclusion. Its signature and quantifier order are unchanged.

The exceptional adjunction and its actual unit/counit formulas are constructed by
exceptionalIdentificationOfIso using Mathlib's ofNatIsoLeft and ofNatIsoRight; they are
not added as holes. The exceptional obligation asserts only the geometric formula
isomorphisms and their scalar square.

Moved the complete definition prefix verbatim to RationalOperationsData and publicly
re-exported it from the original path to avoid a circular proof import. The exact
block comparison passed. All original public dependencies are re-exported through the
data module. Reattached the existing definition node and added ownership for the other
published interfaces. No source-library file is edited.

Change record: coord/changes/D2-rational-operation-data-relocation.md. All 15 downstream
modules are listed there; none requires a source adaptation because declarations and
public visibility are identical. No target's statement or definition changes meaning.

Validation: all five delivered modules compiled through lcompile.py. The sole unused
simp argument was removed and the two affected modules were rechecked before delivery.
The exact moved-definition block, 100-character line bounds, three-hole inventory and
absence of a return path through each new DAG node were checked. No consumer source is
adapted: public re-export preserves every old declaration and its body.

## Proved and sorry left

Closed the original body of WeilConjectures.coef_rational_operations by a complete
combination of existing declarations and the three smaller steps. This is a
decomposition, not a sorry-free proof of the mathematical package: 1 original hole
closed, 3 named holes added, net -2. The original module and the data module have no
sorry. exceptionalIdentificationOfIso and both unit/counit fields are fully proved.

Every new hole is exactly a public theorem with := by sorry, one per module:

- WeilConjectures.RationalOperations.rationalHom_identifications:
  lem-sf-rational-hom-identifications, RationalHomIdentifications.lean.
- WeilConjectures.RationalOperations.rationalExceptional_identifications:
  lem-sf-rational-exceptional-identifications, RationalExceptionalIdentifications.lean.
- WeilConjectures.RationalOperations.rationalDualizing_identification:
  lem-sf-rational-dualizing-identification, RationalDualizingIdentification.lean.

The three statements are separate parts, not a renamed parent: Hom has one scheme
and no exceptional system; exceptional has no Hom or dualizing existence conclusion;
dualizing has no morphism f, Hom adjunction, or scalar square. Their docstrings retain
the complete representative, normalization and comparison arguments of the original
plan. Empty schemes, identity coefficient embeddings, and ramified extensions are
included; no positivity condition beyond the existing coefficient conventions was added.

## No longer needed

No existing module or DAG node is withdrawn. No dependency is declared globally pruned:
the original geometric dependencies still support the three obligations. All eleven
original public imports are retained through RationalOperationsData. The original
module's following direct proof imports are unnecessary for its assembly and are removed:

- Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
- Mathlib.Algebra.Homology.BifunctorShift
- Mathlib.Algebra.Homology.DerivedCategory.Basic
- Mathlib.AlgebraicGeometry.Sites.Proetale
- Sheaf.Algebra.Homology.ChangeOfRingsKFlat
- WeilConjectures.Algebra.Homology.HomTensorTotal
- Sheaf.Algebra.Homology.KFlat
- Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
- Sheaf.Algebra.Homology.KInjectiveHomComplex
- WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMap
- Sheaf.Algebra.Homology.RhomGlobalSectionsOfUniverses
- Sheaf.AlgebraicGeometry.CoefficientProEtaleTorAmplitude
- Sheaf.AlgebraicGeometry.CompactSupportRestrictionOfScalars
- Sheaf.AlgebraicGeometry.ProEtaleCountableProductsExact
- Sheaf.AlgebraicGeometry.ProEtaleExtensionZero
- Sheaf.CategoryTheory.PreDerivedAdjointFunctorsGeneral
- Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
- Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients
- Sheaf.NumberTheory.Padics.ExtensionIntegersDvr
- Sheaf.Paper.CompactSupportReductionTower
- Sheaf.Paper.ConstantCompletionEquivalence
- Sheaf.Paper.DerivedCompleteOnSlices
- Sheaf.Paper.DerivedScalarExtensionRestrictionAdjunction
- Sheaf.Paper.FiniteCoefficientTensorCtf
- Sheaf.Algebra.Homology.DerivedTensor
- Sheaf.Paper.FiniteTorAmplitude
- Sheaf.AlgebraicGeometry.ProEtaleTorAmplitude
- Sheaf.Paper.IntrinsicFiniteTorsionConstructibility
- Sheaf.Paper.FiniteFreeCompletedScalarComparison
- Sheaf.Paper.IntegralConstructibleInternalHom
- Sheaf.Paper.IntegralOperationsScalarComparisons
- Sheaf.Paper.IntegralOperationsWellDefined
- Sheaf.Paper.IntegralResidueTor
- Sheaf.AlgebraicGeometry.ProEtaleCohomologicalSupport
- Sheaf.Paper.NormalizedDVREffectivity
- Sheaf.Paper.NormalizedDVRTower
- Sheaf.Paper.PbcRationalTransport
- Sheaf.SixFunctors.IntegralVerdier
- Sheaf.SecSmoothPurity.IntrinsicCompactSupportRestriction
- Sheaf.SixFunctors.CoefDualFormulaScalarTranspose
- WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients
- Sheaf.Algebra.Homology.KFlatIndependentCoefficients
- Sheaf.Paper.FiniteFreeCoefficientExtension

- Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients
- Sheaf.SixFunctors.CoefIntegralFiniteExtension

The parent now directly needs the three new statement modules, the existing system
existence theorem, rational Verdier theorem, and integral dualizing-data existence.
The new statements retain their original proof dependencies for later workers; removing
direct imports here is not a claim that those mathematical dependencies are unnecessary.

## Where the brief, the DAG or earlier work was wrong

No mathematical correction to the statement or unit route. The recorded blueprint
source path is an older label: the current latest snapshot no longer contains a file
named lem-coef-rational-operations. The node's complete blueprint_update proof and the
published 20-step docstring were read, together with the current six-functors package
and general-biduality unit. The decomposition preserves their identification argument.
The adopted source RationalOperations module only gives the etale-domain adjunction
under ambient-adjoint hypotheses and explicitly omits finite scalar compatibility; it
cannot replace the assigned theorem's normalized pro-etale comparisons.

Searches used msearch LeanSearch, LeanFinder, Loogle, Mathlib grep and rg over both project
roots. Mathlib supplies adjunction transport component formulas, but no theorem with
the three normalized constructible coefficient assertions. No new axiom or hollow
definition is introduced. Existing dualizing witnesses are unpacked only in the proof.

## New nodes

lem-sf-rational-hom-identifications carries original steps 2--9, 12 and 20, with a
separate full Hom adjunction and evaluation scalar-square statement.

lem-sf-rational-exceptional-identifications carries the exceptional parts of original
steps 10--20. The actual adjunction is transported in Lean from the system, and the
remaining hole states the formula comparisons and scalar-square equation.

lem-sf-rational-dualizing-identification carries the structure-map clause of step 11.

def-sf-rational-operation-comparison-data owns the unchanged moved interfaces not
already owned by def-sf-rational-verdier-identifications. The latter's existing
attachment is relocated to RationalOperationsData. Both are definitions only, with
no added existence witness and no new mathematical body.

## Second reading by D2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
