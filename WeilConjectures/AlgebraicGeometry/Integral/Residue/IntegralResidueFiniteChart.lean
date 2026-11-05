/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Integral.Residue.IntegralResidueFiniteReduction
public import WeilConjectures.AlgebraicGeometry.Integral.IntegralStratifiedPerfectModelsSupplement
import Mathlib.RingTheory.Finiteness.Small
import Mathlib.Algebra.Module.Shrink
import WeilConjectures.AlgebraicGeometry.Integral.Residue.IntegralResidueFiniteSlice
import WeilConjectures.AlgebraicGeometry.Integral.Residue.IntegralResidueFiniteConstants
import WeilConjectures.CategoryTheory.Ringed.RingedDerivedRestrictionGeneralSupplement
import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheaf
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-! # Finite perfect charts under normalized residue coefficients

Source: Bhatt--Scholze, Lemma 6.5.8(1) and Proposition 6.6.11.
(blueprint: lem-weil-pbc-integral-residue-finite-chart).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.ProEtale
namespace AlgebraicGeometry.Scheme

end AlgebraicGeometry.Scheme
