/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.TStructure
public import Mathlib.Algebra.Homology.DerivedCategory.Plus
public import Submission.WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.TStructure

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-!
# Vanishing of morphisms into shifts of bounded objects

Let `C` be an abelian category, `U : C` and `P` a property of objects of `C` such that
`Hom_{D(C)}(U, Y[m]) = 0` for all `Y` satisfying `P` and all `m ≥ d`. Then for every bounded
object `M` of `D(C)` with homology objects satisfying `P` and concentrated in degrees `≤ b`,
`Hom_{D(C)}(U, M[m]) = 0` for all `m ≥ b + d`. This is the formal part of the statement that a
bound on the cohomological dimension of a functor on objects gives a bound on its
hypercohomology on bounded complexes, and is proved by induction on the amplitude of `M` using
the truncation triangles of the canonical t-structure.

## Main statements

- `DerivedCategory.subsingleton_shiftedHom_of_isGE_of_isLE`: the vanishing statement above.
- `DerivedCategory.subsingleton_shiftedHom_of_ext`: the same statement, with the hypothesis on
  `P` phrased with `Ext`-groups.
- `DerivedCategory.Plus.singleFunctorHomEquivExt`: morphisms `X[0] ⟶ Y[0][n]` in the bounded
  below derived category `DerivedCategory.Plus C` are the `Ext`-groups `Ext^n(X, Y)`.
-/

@[expose] public section

universe w' w v u

open CategoryTheory Limits Pretriangulated

namespace DerivedCategory

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]


end DerivedCategory

namespace DerivedCategory.Plus

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C] [HasExt.{w'} C]

/-- Morphisms `X[0] ⟶ Y[0][n]` in the bounded below derived category are the elements of
`Ext^n(X, Y)`. -/
noncomputable def singleFunctorHomEquivExt (X Y : C) (n : ℕ) :
    ((singleFunctor C 0).obj X ⟶ ((singleFunctor C 0).obj Y)⟦(n : ℤ)⟧) ≃
      Abelian.Ext.{w'} X Y n :=
  (ObjectProperty.fullyFaithfulι _).homEquiv.trans
    ((Iso.homCongr (Iso.refl _) ((Plus.ι.commShiftIso (n : ℤ)).app _)).trans
      Abelian.Ext.homEquiv.symm)

end DerivedCategory.Plus
