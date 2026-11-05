/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.RingedSiteZerothHypercohomology
public import WeilConjectures.Algebra.Homology.HomComplex
public import Mathlib.CategoryTheory.Functor.Currying
import WeilConjectures.Algebra.Homology.KFlatResolution
import WeilConjectures.Algebra.Homology.KInjectiveHomComplex
import WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMap
import WeilConjectures.Algebra.Homology.HomComplexGlobalHomotopy
import Mathlib.Algebra.Category.Grp.EpiMono
import Mathlib.Algebra.Homology.DerivedCategory.KInjective

/-!
# Hypercohomology of a sheaf Hom complex with K-injective target

Source: Stacks Project, Tags 08JA, 0A95, and 0A96.
(blueprint: lem-pur-hom-complex-hypercohomology)
-/

@[expose] public section

universe u w
open CategoryTheory Opposite
namespace CategoryTheory

end CategoryTheory
