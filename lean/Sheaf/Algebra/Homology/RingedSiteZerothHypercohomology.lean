/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H1
-/
module

public import Sheaf.CategoryTheory.RingedSiteKInjectiveResolutions
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
public import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence

public import WeilConjectures.Algebra.Homology.RingedSiteZerothHypercohomology

/-!
# Zeroth hypercohomology on a small ringed site

Source: Stacks Project, Cohomology on Sites, Section 07A5 and Lemma 08JA
(blueprint: def-pur-ringed-site-zeroth-hypercohomology).

The source library provides the identical construction. Re-export that declaration
instead of declaring it twice, so consumers can combine this compatibility module
with the source library's derived internal Hom comparisons. All original public
infrastructure imports are retained.
-/

@[expose] public section
