# standardSingleBaseChange_topRestriction_compatibility: local proof attributes

## Reason

The stage-3 static interface check classifies added attribute commands as an
interface change even when every attribute is local. This record documents the
local reducibility settings used by the new proof. They keep the pinned derived
functors and comparisons from repeatedly unfolding during normalization, and let
Lean identify the Scheme.Modules and SheafOfModules presentations consistently.
The private pullback and direct-image constructions have proved equations for
their maps. Every existing signature, visibility and definition body is unchanged.
The changes do not alter a target's meaning or require a downstream adaptation.

## Old

The original module had no attribute commands. Its common scope was:

```lean
@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry
```

## New

The common scope remains the same. The following local attribute commands are
added within the namespace, alongside the private constructions and proof APIs:

```lean
attribute [local irreducible] topRestriction_pullbackIso

attribute [local irreducible] topRestriction_imageIso

attribute [local irreducible] derivedPullback Scheme.Modules.tensorPullbackObj
  Scheme.picardTermwiseSingleMap Scheme.Modules.tensorPullbackCompositionIso

attribute [local irreducible] Adjunction.homEquiv relativeMVAdj relativeMVComp
  relativeMVImageComp singleComplexOpenPullbackIso Adjunction.leftAdjointUniq
  Scheme.Modules.restrictFunctorIsoPullback Scheme.Modules.overFunctorEquiv
  standardSingleBaseChangeMap standardSingleBaseChange_topRestriction_sourceIso relativeMVUnit

attribute [local instance_reducible] Scheme.Modules TopCat.Sheaf

attribute [local implicit_reducible] Scheme.Modules.Hom DerivedCategory
  Functor.mapHomologicalComplex HomotopyCategory Functor.mapHomotopyCategory
  HomotopyCategory.quotient DerivedCategory.Q DerivedCategory.Qh
  HomologicalComplexUpToQuasiIso.Qh
```

## Users

`tools/downstream.py Sheaf.AlgebraicGeometry.StandardSingleBaseChangeTopRestrictionAux
--uses AlgebraicGeometry.standardSingleBaseChange_topRestriction_compatibility`
reported 1425 transitive importers and two textual uses. Their statements and
proof interfaces are unchanged; all settings below are local to the item module.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.StandardSingleBaseChangeTopRestrictionAux | Y3 | Compatibility proof completed; local proof settings and private APIs added. |
| Sheaf.AlgebraicGeometry.StandardSingleBaseChangeTopRestriction | unclaimed | Not affected; existing compatibility signature remains identical. |

## Status

landed 20261014T063824-L-2816066 2026-10-14 (merge of deliver/Y3/Sheaf.AlgebraicGeometry.StandardSingleBaseChangeTopRestrictionAux)
