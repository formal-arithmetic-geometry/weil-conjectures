module

public import Mathlib.Algebra.Category.ModuleCat.Algebra
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.EssentiallySmall
public import Mathlib.CategoryTheory.Linear.Yoneda
public import Mathlib.CategoryTheory.Linear.LinearFunctor
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs

import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
import Mathlib.CategoryTheory.Equivalence
import Mathlib.LinearAlgebra.Dimension.RankNullity

/-! # Finite projective generators and finite-dimensional modules

Source: Milne, Algebraic Groups (2017), Lemma 9.35, printed p.177
(blueprint: lem-sfb-finite-projective-generator-module-equivalence).

The target is the full subcategory of modules over the opposite endomorphism algebra whose
underlying vector spaces are finite-dimensional. Its inclusion identifies the forward functor
with Mathlib's actual `preadditiveCoyonedaObj`, fixing both its action and its morphism maps.
-/

@[expose] public section

universe u v w s

open CategoryTheory.Limits
open scoped ModuleCat

namespace CategoryTheory

/-- A finite projective generator identifies an essentially small linear abelian category with
finite-dimensional right modules over its endomorphism algebra.

Source: Milne, Algebraic Groups (2017), Lemma 9.35, printed p.177
(blueprint: lem-sfb-finite-projective-generator-module-equivalence).

Proof: (1) Composition gives the right action, and postcomposition gives the linear Hom functor.
The detection hypothesis applied to a difference of morphisms proves faithfulness.
(2) The injections and projections of a finite biproduct identify Hom(P,P^n) with End(P)^n.
Maps out of P^n correspond to module maps out of this free module by their values on its basis;
this includes n = 0. (3) Exactness on short exact sequences implies preservation of epis and
cokernels, by lem-sp-exact-functor-preserves-homology. (4) A finite vector-space spanning family
of a module gives a finite free surjection. Its kernel is finite-dimensional, by
lem-trf-vector-space-quotient-dimension, since End(P) is finite-dimensional. A finite spanning
family of the kernel gives a finite free presentation. (5) Lift the presentation matrix to a
map of finite sums of P and take its cokernel. Exactness identifies its Hom module with the
given module, proving essential surjectivity. (6) Present any X as a cokernel of a map between
finite sums of P, using the finite-generation hypothesis also on the kernel. Lift a module map
Hom(P,X) to Hom(P,Y) along that presentation; faithfulness kills its composite with the relation
map, so the cokernel property descends it to X. Surjectivity of Hom on the presentation epi
proves that this descended map gives the desired module map. Hence the functor is full.
(7) Apply lem-trf-fully-faithful-ess-surj-equivalence. The inverse maps on Hom spaces are linear,
so the quasi-inverse is linear too. The argument includes the zero generator and zero algebra:
finite sums then force every categorical object, and unitality every module, to be zero. -/
theorem finiteProjectiveGenerator_moduleEquivalence
    (k : Type w) [Field k] (C : Type u) [Category.{v} C] [Abelian C]
    [Linear k C] [EssentiallySmall.{s} C]
    [∀ X Y : C, FiniteDimensional k (X ⟶ Y)] (P : C)
    (hExact : ∀ S : ShortComplex C, S.ShortExact →
      (S.map ((linearCoyoneda k C).obj (Opposite.op P))).ShortExact)
    (hDetect : ∀ (Y Z : C) (f : Y ⟶ Z), (∀ h : P ⟶ Y, h ≫ f = 0) → f = 0)
    (hGenerate : ∀ Y : C, ∃ (n : ℕ) (B : Bicone (fun _ : Fin n ↦ P)),
      Nonempty B.IsBilimit ∧ ∃ q : B.pt ⟶ Y, Epi q) :
    ∃ e : C ≌ (ObjectProperty.FullSubcategory
      (fun M : ModuleCat.{v} (End P)ᵐᵒᵖ ↦ FiniteDimensional k M)),
      e.functor ⋙ ObjectProperty.ι
        (fun M : ModuleCat.{v} (End P)ᵐᵒᵖ ↦ FiniteDimensional k M) =
          preadditiveCoyonedaObj P ∧
      e.functor.Linear k ∧ e.inverse.Linear k := by
  sorry

end CategoryTheory
