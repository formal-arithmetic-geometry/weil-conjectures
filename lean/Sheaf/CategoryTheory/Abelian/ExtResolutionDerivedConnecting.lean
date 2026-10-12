/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H1
-/
module

public import Mathlib.CategoryTheory.Abelian.Injective.Ext
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
import Sheaf.CategoryTheory.Abelian.RHomDerivedConnecting
import Sheaf.CategoryTheory.Abelian.RightDerivedTriangleConnecting
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusSingle

/-!
# Injective-resolution and derived connecting morphisms agree

Source: Stacks Project, Derived Categories, Tags 05TE and 06XR
(blueprint: lem-sc-p1-ext-resolution-derived-connecting).
-/

@[expose] public section

universe v u

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory.InjectiveResolution

/-- The injective-resolution boundary, computed by lifting a cocycle and taking its
 differential, agrees with the boundary of the distinguished short-exact-sequence triangle.
Source: Stacks Project, Derived Categories, Tags 05TE and 06XR
(blueprint: lem-sc-p1-ext-resolution-derived-connecting).

Here `i`, `p`, `hιi`, `hιp`, and `hexact` describe any horseshoe resolution of `S`.
For a cocycle `c`, choose a lift `b` through `p`, and factor its differential as `a ≫ i`.
The resolution connecting map sends the class of `c` to the class of `a`. Degreewise
short exactness splits because the first resolution is injective, so all these lifts exist.
The constructor `extMk` is the inverse of the canonical Ext/cohomology-class comparison.
Thus the equation below is equality of the two connecting maps on every class, with
all choices of representatives and lifts allowed, including in degree zero.

Proof, Step 1: apply `lem-sc-p1-right-derived-triangle-connecting` to the additive left
exact functor `Hom(M,-)` and the triangle of `lem-sf-derived-ses-triangle`. Under
`lem-sp-derived-functor-single-identification`, the horseshoe connecting map is the
homology connecting map of the right-derived triangle.
Step 2: `lem-sc-p1-rhom-hom-derived-connecting` identifies that map with postcomposition
by the shifted boundary. Its comparison sends a cocycle to its derived-category roof;
`lem-weil-pbc-ext-via-injective-resolution` identifies this with the comparison used
by `extMk`. Finally `lem-sp-long-exact-of-triangle` gives the displayed homological
connecting map. Composing these comparisons proves the equality. -/
theorem extMk_resolution_connecting_eq_triangle
    {C : Type u} [Category.{v} C] [Abelian C] [EnoughInjectives C]
    {S : ShortComplex C} (hS : S.ShortExact) (M : C)
    (RA : InjectiveResolution S.X₁) (RB : InjectiveResolution S.X₂)
    (RC : InjectiveResolution S.X₃)
    (i : RA.cocomplex ⟶ RB.cocomplex) (p : RB.cocomplex ⟶ RC.cocomplex)
    (hip : i ≫ p = 0)
    (hιi : RA.ι ≫ i = (CochainComplex.single₀ C).map S.f ≫ RB.ι)
    (hιp : RB.ι ≫ p = (CochainComplex.single₀ C).map S.g ≫ RC.ι)
    (hexact : ∀ k : ℕ,
      ((ShortComplex.mk i p hip).map
        (HomologicalComplex.eval C (ComplexShape.up ℕ) k)).ShortExact)
    (n : ℕ) (c : M ⟶ RC.cocomplex.X n)
    (hc : c ≫ RC.cocomplex.d n (n + 1) = 0)
    (b : M ⟶ RB.cocomplex.X n) (hb : b ≫ p.f n = c)
    (a : M ⟶ RA.cocomplex.X (n + 1))
    (ha : a ≫ RA.cocomplex.d (n + 1) (n + 1 + 1) = 0)
    (hba : b ≫ RB.cocomplex.d n (n + 1) = a ≫ i.f (n + 1)) :
    letI := HasExt.standard C
    letI := HasDerivedCategory.standard C
    (preadditiveCoyoneda.obj (op ((DerivedCategory.singleFunctor C 0).obj M))).homologySequenceδ
        hS.singleTriangle (n : ℤ) ((n + 1 : ℕ) : ℤ) (by omega)
        (RC.extMk c (n + 1) rfl hc).hom =
      (RA.extMk a (n + 1 + 1) rfl ha).hom := by
  sorry

end CategoryTheory.InjectiveResolution
