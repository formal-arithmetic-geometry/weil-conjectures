/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AffineComparisonEtaleCechSystem
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
public import WeilConjectures.CategoryTheory.Sites.CechComplex
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Products
public import WeilConjectures.SixFunctors.ProEtale.Comparison.Defs
public import WeilConjectures.CategoryTheory.Sites.CechComplexFunctor
import WeilConjectures.SixFunctors.ProEtale.Comparison.Continuity
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Colim
import Mathlib.Algebra.Homology.ShortComplex.FunctorEquivalence
import WeilConjectures.Mathlib.Algebra.Homology.ShortComplex.Exact

/-! # Categorical finite Čech section systems

Source: Stacks Project, Tag 099U, the two finite Čech limit reductions.
-/

@[expose] public section

universe u' u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.ProEtale.AffineEtaleCechSystem

set_option backward.isDefEq.respectTransparency false

attribute [local instance] Over.ConstructProducts.over_finiteProducts_of_finiteWidePullbacks

variable {Y : Scheme.{u}} {V : Y.ProEt} {n : ℕ} {U : Fin n → Over V}
  {I : Type u} [SmallCategory I] (S : AffineEtaleCechSystem Y V U I)
  {A : Type u'} [Category.{u + 1} A] [Abelian A]
  [IsGrothendieckAbelian.{u + 1} A] (J : Sheaf Y.smallEtaleTopology A)

end AlgebraicGeometry.ProEtale.AffineEtaleCechSystem
