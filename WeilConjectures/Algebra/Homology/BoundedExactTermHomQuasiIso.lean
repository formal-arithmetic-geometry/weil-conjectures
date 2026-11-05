/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.HomComplex
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.Algebra.Homology.QuasiIso
import WeilConjectures.Algebra.Homology.SingleDegreeExactTermHomQuasiIso
import WeilConjectures.Algebra.Homology.StupidTailHomShortExact
import WeilConjectures.FromJoel.Algebra.Homology.BicomplexColumns

/-! # Bounded Hom complexes with exact internal Hom in each source degree

Source: Stacks Project, Cohomology of Sheaves, Tag 08DM, bounded Hom calculation,
and Homology, Tag 0117, long exact cohomology sequence.
(blueprint: lem-pc-bounded-exact-term-hom-quasi-iso).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory

end CategoryTheory
