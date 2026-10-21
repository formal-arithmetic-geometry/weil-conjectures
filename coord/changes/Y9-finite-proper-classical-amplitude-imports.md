# AlgebraicGeometry.ProEtale.finiteProper_classical_amplitude

## Reason

The completed proof uses the canonical ordinary constant-ring module category,
not the unused finite-coefficient alternative presentation or alternate derived
functor. Remove their two public imports to prune the unused dependencies.
The theorem signature is unchanged verbatim; no definition is changed.
Private proof imports add the proved exact-product, completeness and coefficient
restriction APIs. The private Grothendieck instance supplies the intrinsic
module-category resolution instance. `attribute [local instance]
intrinsicHasDerivedCategory` selects the standard localization model within this
file; both definitional-equality options affect elaboration only. No instance,
helper, or changed command appears in a public theorem signature. The namespace
and public section remain as before.

## Old

The previous import/header block, verbatim:

```lean
/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q52
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import WeilConjectures.AlgebraicGeometry.BaseChangeConventions
public import Mathlib.Topology.KrullDimension
public import Sheaf.AlgebraicGeometry.ProEtaleFiniteModules
public import Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions
public import Sheaf.SixFunctors.ClassicalDefinition
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence
public import Sheaf.AlgebraicGeometry.ProEtaleConstantDerivedDirectImage
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
public import Mathlib.CategoryTheory.Limits.Shapes.Countable

import Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations
import Sheaf.CategoryTheory.RingedSiteModules
import Sheaf.Paper.FiniteDiscreteCondensedRing
import Sheaf.Paper.FiniteDiscreteSchemeRing
import Sheaf.Algebra.Homology.KInjectiveProductsTermwise
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility
import Sheaf.AlgebraicGeometry.ProperTorsionDirectImageBound
import WeilConjectures.AlgebraicGeometry.SmoothBaseChange.HigherDirectImageForgetComparison
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Sheaf.AlgebraicGeometry.ProEtaleClassicalSheavesModules
import Sheaf.AlgebraicGeometry.ProEtaleDirectImageComparison
import Sheaf.CategoryTheory.KInjectiveComputes
import WeilConjectures.CategoryTheory.DerivedCategory.CoproductsOfHomologyProperty
import Sheaf.CategoryTheory.TruncationsAndHomotopyColimits
import Sheaf.SixFunctors.FiniteProperClassicalTruncation
import Sheaf.AlgebraicGeometry.FiniteCohomologicalDimensionDirectImageCoproducts

```

## New

The replacement import/header block, verbatim:

```lean
/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q52
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import WeilConjectures.AlgebraicGeometry.BaseChangeConventions
public import Mathlib.Topology.KrullDimension
public import Sheaf.SixFunctors.ClassicalDefinition
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence
public import Sheaf.AlgebraicGeometry.ProEtaleConstantDerivedDirectImage
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
public import Mathlib.CategoryTheory.Limits.Shapes.Countable

import WeilConjectures.Algebra.Homology.HomotopyCategory.Products
import all Sheaf.AlgebraicGeometry.ProEtaleClassicalDirectImagePreservation
import Sheaf.AlgebraicGeometry.ProEtaleProductsExact
import Sheaf.CategoryTheory.Triangulated.LeftCompleteHeartUpperBound
import Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility
import WeilConjectures.Mathlib.CategoryTheory.Sites.Whiskering
import WeilConjectures.AlgebraicGeometry.TorsionSheafCharacterizations
import Sheaf.AlgebraicGeometry.ProperTorsionDirectImageBound
import WeilConjectures.AlgebraicGeometry.SmoothBaseChange.HigherDirectImageForgetComparison
import Sheaf.AlgebraicGeometry.ProEtaleClassicalSheavesModules
import Sheaf.AlgebraicGeometry.ProEtaleDirectImageComparison
import WeilConjectures.CategoryTheory.DerivedCategory.LeftComplete
import Sheaf.AlgebraicGeometry.FiniteCohomologicalDimensionDirectImageCoproducts

```

New file-local commands, verbatim:

```lean
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] intrinsicHasDerivedCategory
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.SixFunctors.FiniteProperClassicalAmplitude | Y9 | Complete the unchanged theorem; prune two unused public imports and add private proof APIs. |

A full source search of `lean/Sheaf` and `lean/WeilConjectures` found no current
Lean importer or user of this module/theorem. DAG parents with unfinished proofs
retain their existing node references; no parent statement, unit route or
attachment changes, and this module is not withdrawn. The removed public
imports contribute nothing to the theorem's signature. There are therefore no
consumer adaptations in this packet. No target statement or target-used
definition changes, and the target statement review is not reopened.

## Status

landed 20261021T121013-L-4040420 2026-10-21 (merge of deliver/Y9/Sheaf.SixFunctors.FiniteProperClassicalAmplitude)
