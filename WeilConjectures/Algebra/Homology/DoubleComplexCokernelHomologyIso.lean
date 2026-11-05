/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Homology.HomologicalBicomplex
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Algebra.Homology.ShortComplex.Exact
public import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import WeilConjectures.Algebra.Homology.RowCycleLiftsToZigzag
import WeilConjectures.Algebra.Homology.ZigzagToRowCokernel
import WeilConjectures.Algebra.Homology.ZigzagTrivialIfRowBoundary

/-!
# Homology of cokernel complexes of an exact double complex

Source: Stacks Project, Algebra, Lemma Tag 00M1 (lemma-no-spectral-sequence),
including its preceding cokernel-complex construction and functoriality paragraph
(blueprint: lem-weil-pbc-double-complex-cokernel-homology-iso).
-/

@[expose] public section

universe u v

open CategoryTheory

namespace HomologicalComplex₂

end HomologicalComplex₂
