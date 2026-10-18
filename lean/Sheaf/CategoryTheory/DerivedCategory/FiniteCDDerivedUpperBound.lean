/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF contributors
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.CategoryTheory.Functor.Derived.RightDerived
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.CategoryTheory.Preadditive.Injective.Resolution
import Mathlib.Algebra.Homology.HomotopyCategory.Triangulated
import Sheaf.CategoryTheory.Abelian.RightDerived.FullLongExactSequence
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import WeilConjectures.Mathlib.CategoryTheory.Abelian.RightDerived
import WeilConjectures.CategoryTheory.DerivedCategory.FiniteCohomologicalDimension
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic

/-!
# Finite cohomological dimension and unbounded right derived functors

Source: Stacks Project, `literature/stacks-project/derived.tex`, Tag 07K7,
lemma-unbounded-right-derived (1) and (4)(c) (blueprint: lem-sf-finite-cd-derived-upper-bound).
-/

@[expose] public section

universe u₁ v₁ u₂ v₂ w₁ w₂

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

/-- (blueprint: lem-sf-finite-cd-derived-upper-bound)
Finite cohomological dimension gives an unbounded total right derived functor and
raises an upper cohomological bound by at most the dimension.  This is the statement of
Stacks Project Tag 07K7, parts (1) and (4)(c), with the unbounded cochain derived
categories represented by Mathlib's `DerivedCategory` and the total derived functor
characterized by `Functor.IsRightDerivedFunctor`.

Proof:
1. Set `d(X) = max ({0} ∪ {q > 0 | R^q F(X) ≠ 0})`, which is at most `N`.
   Injectives have degree zero by `lem-weil-pbc-derived-functor-injective-vanishing`,
   so enough injectives gives degree-zero embeddings. For a short exact sequence
   `0 → X → Y → Z → 0`, `lem-weil-pbc-derived-functor-long-exact` gives
   `d(Z) ≤ max (d(X) - 1) (d(Y))`, with truncated subtraction. The split biproduct
   sequence likewise gives `d(X ⊕ Y) ≤ max (d(X)) (d(Y))`.
2. Apply `lem-sf-degree-zero-complex-replacement` (Tag 07K6) with this degree
   function and bound `N`. Every unbounded complex has a quasi-isomorphism into
   a complex of right `F`-acyclic objects. Denote this class of complexes by `I`.
3. Specialize `lem-kun-pointwise-finite-cd-exact-complex` to the singleton family
   consisting of the identity of `B`, with bound `N`. The identity preserves monos
   and detects zero objects, so `F` takes every exact complex in `I` to an exact
   complex. No Grothendieck or boundedness hypothesis is needed.
4. A quasi-isomorphism between complexes in `I` has exact cone by
   `lem-pur-quasi-iso-cone-acyclic`. Its terms are biproducts of right acyclic
   objects and are right acyclic by the long exact sequence. Step 3 makes its image
   exact. Additivity identifies the image of the cone differential matrix with
   the cone differential of the image map, including the minus sign. The cone
   criterion in `B` then says that the image map is a quasi-isomorphism.
5. Additivity carries cochain homotopies to homotopies, commutes with the signed
   shift, and preserves cone triangles. Thus termwise `F`, followed by localization
   in `B`, defines an exact functor on the homotopy category, using
   `lem-pur-homotopy-category-triangulated`. Steps 2 and 4 verify the hypotheses of
   `lem-sf-right-derived-from-adapted-complexes` (Tag 06XN). It supplies `RF` and
   its universal comparison, and identifies `RF(Q(L))` with `Q(F(L))` for `L ∈ I`.
   Equivalently this is the displayed right derived functor relative to the
   localization from cochain complexes.
6. Represent `E` by `L ∈ I`. Write `Z^r = ker(d_L^r)`. For `r ≥ t` the vanishing
   of `H^(r+1)(L)` gives `0 → Z^r → L^r → Z^(r+1) → 0`. The long exact sequence
   and right acyclicity of `L^r` give `R^p F(Z^(r+1)) ≅ R^(p+1) F(Z^r)` for
   `p ≥ 1`. Left exactness identifies the cycles of `F(L)` with `F(Z^i)`;
   `R^0 F ≅ F` from `lem-sp-derived-well-defined` identifies its degree `i > t`
   cohomology with `R^1 F(Z^(i-1))`. For `i > t + N`, iterate the connecting
   isomorphisms `N` times to identify this with `R^(N+1) F(Z^(i-N-1)) = 0`.
   Every sequence used has index at least `t`. If `N = 0`, the given vanishing
   of `R^1 F` already suffices. Step 5 transfers the bound to `RF(E)`.
-/
theorem finiteCDDerivedUpperBound
    {A : Type u₁} [Category.{v₁} A] [Abelian A] [EnoughInjectives A]
    {B : Type u₂} [Category.{v₂} B] [Abelian B]
    (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F]
    [HasDerivedCategory.{w₁} A] [HasDerivedCategory.{w₂} B]
    (N : ℤ)
    (hN0 : 0 ≤ N)
    (hN : ∀ (q : ℕ), N < (q : ℤ) → ∀ (X : A),
      IsZero ((F.rightDerived q).obj X)) :
    ∃ (RF : DerivedCategory A ⥤ DerivedCategory B)
      (α : (F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        (DerivedCategory.Q : CochainComplex B ℤ ⥤ DerivedCategory B)) ⟶
        (DerivedCategory.Q : CochainComplex A ℤ ⥤ DerivedCategory A) ⋙ RF),
      RF.IsRightDerivedFunctor α (HomologicalComplex.quasiIso A (ComplexShape.up ℤ)) ∧
        ∀ (t : ℤ) (E : DerivedCategory A),
          (∀ (i : ℤ), t < i →
            IsZero ((DerivedCategory.homologyFunctor A i).obj E)) →
          ∀ (i : ℤ), t + N < i →
            IsZero ((DerivedCategory.homologyFunctor B i).obj (RF.obj E)) := by
  sorry

end CategoryTheory
