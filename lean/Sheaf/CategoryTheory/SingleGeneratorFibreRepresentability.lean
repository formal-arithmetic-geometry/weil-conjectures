/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NJ
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.EssentiallySmall
public import Mathlib.CategoryTheory.Linear.LinearFunctor
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology

/-!
# Representability of a fibre functor with a single subquotient generator

Source: Milne, Algebraic Groups (2017), Section 9(d), Lemmas 9.33 and 9.34(a),
printed pp.175–176 (blueprint: lem-sfb-single-generator-fibre-representability).

The functor takes values in modules with finite-dimensional underlying vector spaces.
Finite categorical products in an abelian category are also finite direct sums; using
products here avoids choosing an additional biproduct instance.
-/

@[expose] public section

universe u v w r s

open CategoryTheory.Limits

namespace CategoryTheory

/-- An exact faithful linear fibre functor on a category generated under finite sums and
subquotients by one object has a representing pair of bounded fibre dimension.

Source: Milne, Algebraic Groups (2017), Lemmas 9.33 and 9.34(a), printed pp.175–176
(blueprint: lem-sfb-single-generator-fibre-representability).

Proof plan:
1. By `lem-sp-exact-functor-preserves-homology`, exactness preserves kernels, cokernels,
   images and finite sums. Faithfulness reflects isomorphisms: an invertible image makes
   a map mono and epi, hence invertible in the abelian category.
2. Apply `lem-sfb-fibre-generated-subobject` to a singleton. Its lifted vector generates
   the resulting subobject: every further subobject containing that vector is the whole.
3. For a monogenic pair, lift its generator through a quotient of a subobject of a finite
   sum of X, and generate a subobject by the lift. Its image is the whole original pair,
   so it suffices to bound monogenic subobjects of finite sums of X.
4. Put d = dim F(X). If a monogenic subobject embeds in X^m with m > d, a nonzero linear
   relation among the m coordinates of its generator gives a map X^m → X vanishing on
   the subobject. Solve for a coordinate with nonzero coefficient: the kernel is X^(m-1).
   Repeat to embed in X^r for r ≤ d. Thus every monogenic fibre has dimension at most d²,
   including d = 0 and the empty sum.
5. The zero pair is monogenic. Choose a monogenic (P,p) with largest fibre dimension,
   using the finite bound and an essentially small skeleton.
6. If two maps out of P agree on p after F, their difference has kernel containing p.
   Monogenicity makes this kernel all of P, so the maps coincide.
7. Given y in F(Y), generate Q inside P ⊕ Y by (p,y). Projection Q → P is onto because
   its image contains p. Maximality and surjectivity give equal fibre dimensions, so the
   projection is invertible after F and hence before F. Its inverse followed by Q → Y
   sends p to y. Evaluation is therefore bijective for every Y.
8. Linearity of F makes evaluation linear; functoriality gives naturality. Step 5 gives
   the bound. If X = 0, every fibre is zero and the same construction covers this case.
-/
theorem exists_singleGenerator_fibre_representing_pair
    (k : Type r) [Field k] (C : Type u) [Category.{v} C] [Abelian C]
    [Linear k C] [EssentiallySmall.{s} C]
    (F : C ⥤ ModuleCat.{w} k) [F.Additive] [F.Linear k] [F.Faithful]
    [∀ Y : C, FiniteDimensional k (F.obj Y)]
    (hF : ∀ S : ShortComplex C, S.ShortExact → (S.map F).ShortExact)
    (X : C)
    (hX : ∀ Y : C, ∃ (n : ℕ) (Z : C)
      (i : Z ⟶ ∏ᶜ fun _ : Fin n ↦ X) (q : Z ⟶ Y), Mono i ∧ Epi q) :
    ∃ (P : C) (p : F.obj P) (α : ∀ Y : C, (P ⟶ Y) ≃ₗ[k] F.obj Y),
      (∀ (Y : C) (h : P ⟶ Y), α Y h = (F.map h).hom p) ∧
      (∀ (Y Z : C) (a : Y ⟶ Z) (h : P ⟶ Y),
        α Z (h ≫ a) = (F.map a).hom (α Y h)) ∧
      Module.finrank k (F.obj P) ≤ (Module.finrank k (F.obj X)) ^ 2 := by
  sorry

end CategoryTheory
