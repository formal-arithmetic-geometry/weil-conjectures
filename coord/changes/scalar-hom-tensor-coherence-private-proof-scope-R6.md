# CategoryTheory.scalarHomTensorCoherence private proof interface

## Reason

The completed proof extends adjunction-unit normalization from flat K-flat resolutions to
all complexes, compares the chain and derived adjunctions, checks the tensor equations on
pure total generators, and descends along K-flat representatives. This replaces the former
private uniqueness route. Its three private uniqueness lemmas are unused by the new proof
and have no external users.

The static interface scanner also flags the local attributes, options, and declaration-scoped
`omit` commands introduced for the private proof API. The local opacity of the comparison
constructions and explicit restriction transports keep compilation and its axiom probe within
the unchanged 60-second limit. This record documents those commands and private removals.
Every existing public signature, public import, exported attribute, and target definition
is unchanged. No target statement or definition changes meaning; no target statement review
is reopened by this proof-only implementation.

## Old

The removed private signatures are verbatim:

```lean
private theorem complexIso_unique (μ ν : ScalarHomTensorComparison M a)
    (P Q : CochainComplex (scalarModules J R) ℤ) :
    (μ.complexIso P Q).hom = (ν.complexIso P Q).hom

private theorem tensorIso_unique (μ ν : ScalarHomTensorComparison M a) :
    μ.iso = ν.iso

private theorem comparison_unique (μ ν : ScalarHomTensorComparison M a) : μ = ν
```

The old proof environment commands were:

```lean
set_option autoImplicit false

set_option synthInstance.maxSize 2048

set_option backward.isDefEq.respectTransparency true

set_option backward.isDefEq.respectTransparency.types true

attribute [local instance] isMonoidal_W_independentCoefficients
  preservesZeroMorphisms_curriedTensor_independentCoefficients
  preservesZeroMorphisms_curriedTensor_obj_independentCoefficients

attribute [local irreducible] monoidalCategory
```

The public theorem had its current signature and a single `sorry` proof. The proof import
`Sheaf.Paper.ResolvingRepresentativeWhiskering` supported the old private uniqueness route.

## New

The three private signatures above are removed. The theorem is proved from proved private
helpers for units and transposes, chain composition and identity comparisons, tensor
generators, categorical pasting, and naturality descent. The new private definitions are
explicit constructions from the supplied adjunction and comparison data. Their data is
never supplied by an unfinished existence theorem.

The new proof environment commands are verbatim:

```lean
set_option autoImplicit false

set_option synthInstance.maxSize 2048

set_option backward.defeqAttrib.useBackward true

set_option backward.isDefEq.respectTransparency false

set_option backward.isDefEq.respectTransparency.types false

attribute [local instance] isMonoidal_W_independentCoefficients
  preservesZeroMorphisms_curriedTensor_independentCoefficients
  preservesZeroMorphisms_curriedTensor_obj_independentCoefficients

attribute [local irreducible] derivedInternalHomOfUniverses CoefficientClosedStructure.tensor

attribute [local irreducible] monoidalCategory
  Functor.mapHomologicalComplexUpToQuasiIso
  Functor.mapHomologicalComplexUpToQuasiIsoFactors

attribute [local instance] ScalarDerivedPair.extension_additive

attribute [local irreducible] chainAdj

attribute [local irreducible] pairComparison scalarPairComplexComparison coefficientTotalTensor
  coefficientTensorGenerator

attribute [local irreducible] scalarHomOrdinaryRestrictionComp

omit [∀ A : Sheaf J CommRingCat.{max c v r},
  HasDerivedCategory.{w} (scalarModules J A)] in

omit [∀ A : Sheaf J CommRingCat.{max c v r},
  HasDerivedCategory.{w} (scalarModules J A)] [HasSheafify J AddCommGrpCat.{max c v r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}] in

attribute [local irreducible] ordinaryComp

attribute [local irreducible] complexComp

attribute [local irreducible] scalarHomRestrictionComp

attribute [local irreducible] scalarHomExtensionComp

attribute [local semireducible] scalarHomOrdinaryRestrictionComp

attribute [local irreducible] scalarHomOrdinaryRestrictionId

omit [∀ A : Sheaf J CommRingCat.{max c v r},
  HasDerivedCategory.{w} (scalarModules J A)] in

omit [∀ A : Sheaf J CommRingCat.{max c v r},
  HasDerivedCategory.{w} (scalarModules J A)] in

attribute [local irreducible] scalarHomRestrictionId

attribute [local irreducible] scalarHomExtensionId

attribute [local semireducible] scalarHomOrdinaryRestrictionId

attribute [local irreducible] complexId

attribute [local irreducible] CoefficientTensorModels.iso
```

Every attribute above is local to this module or its private namespace. Each `omit ... in`
scopes only the immediately following private declaration. The existing two section-variable
blocks and the complete public theorem signature are unchanged. The new proof-only import
`Sheaf.CategoryTheory.DerivedCategory.ExactRestrictionComposition` provides the generic
factorization equations. The old resolving-whiskering import is removed. No declarations
from the adopted `WeilConjectures` tree are changed or removed.

## Users

`tools/downstream.py Sheaf.Algebra.Homology.ScalarHomTensorCoherence --uses ...` reports
1781 transitive importers. For `complexIso_unique` and `tensorIso_unique`, only the original
item itself matches. For `comparison_unique`, the three external textual matches below
are unrelated structure fields; none uses `CategoryTheory.ScalarHomTensor.comparison_unique`.
The only external textual user of the unchanged public `scalarHomTensorCoherence` is
`ScalarInternalHomTowerCoherence`. The quarantined Lean sources contain neither an import
of this item nor a use of its removed private helpers. No consumer needs adaptation.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Algebra.Homology.ScalarHomTensorCoherence | R6 | Complete proof; replace private route and local proof environment. |
| Sheaf.Paper.GeometricFrobeniusInternalHomComparison | unclaimed | Unrelated `comparison_unique` structure field; no change. |
| Sheaf.Paper.PointDerivedSectionsTensorDescent | unclaimed | Unrelated `comparison_unique` structure field and record assignment; no change. |
| Sheaf.Paper.PointFiniteFreeSectionsTensor | unclaimed | Unrelated `comparison_unique` structure field; no change. |
| Sheaf.Algebra.Homology.ScalarInternalHomTowerCoherence | unclaimed | Applies the unchanged public theorem; no change. |

## Status

landed 20261022T011919-L-3232331 2026-10-22 (merge of deliver/R6/Sheaf.Algebra.Homology.ScalarHomTensorCoherence)
