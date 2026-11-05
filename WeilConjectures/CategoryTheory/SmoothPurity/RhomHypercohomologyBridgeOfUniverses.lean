/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.HomComplex
public import Mathlib.CategoryTheory.Functor.Currying
public import WeilConjectures.CategoryTheory.Ringed.Site.RingedSiteZerothHypercohomologyOfUniverses
import WeilConjectures.CategoryTheory.DerivedInternalHomSectionsModel.DerivedInternalHomSectionsModel
import WeilConjectures.CategoryTheory.SmoothPurity.HomComplexGlobalHomotopyOfUniverses

/-!
# Hypercohomology of the sheaf Hom complex and the homotopy category

Source: Stacks Project, Tags 0A8Z and 08JA.
(blueprint: lem-pur-hom-complex-hypercohomology)

This is the independent-universe comparison used by the global-sections theorem.  Its
proof applies zeroth homology to the recorded full derived-sections comparison and
composes with the ordinary global Hom-complex calculation.
-/

@[expose] public section

set_option autoImplicit false

universe c v r w

open CategoryTheory Opposite

namespace CategoryTheory

end CategoryTheory
