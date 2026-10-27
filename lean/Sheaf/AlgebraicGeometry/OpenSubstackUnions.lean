module

public import Sheaf.AlgebraicGeometry.StablePointedModuliGroupoids
public import Sheaf.AlgebraicGeometry.AlgebraicModuliStack
public import Sheaf.AlgebraicGeometry.OpenModuliSubstack
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-! # Sets of open substacks and unions

Source: Stacks Project, stacks-properties.tex, Tags 06FJ and 05UQ
(blueprint: lem-sfb-open-substack-unions).

The existing full-substack predicates retain objects over the empty scheme.
Scheme pullbacks below are represented over the test scheme, including their projections.
-/

@[expose] public section

set_option autoImplicit false

universe u v w z

open AlgebraicGeometry CategoryTheory.Limits

namespace CategoryTheory

/-- The specified open subscheme represents the actual scheme pullback of a full open
substack, with the representing equivalence compatible with the projection to the test.
This abbreviates the existing `open_pullback` interface for an open subset of that test.
Source: Stacks Project, Tag 05UQ, the cartesian scheme-pullback diagrams
(blueprint: lem-sfb-open-substack-unions). -/
def OpenModuliSubstack.HasPullbackOpen {S : Scheme.{u}}
    {F : BasedCategory.{v, w} (Over S)} (U : OpenModuliSubstack F)
    (T : Over S) (t : BasedFunctor (discreteModuli (yoneda.obj T)) F)
    (V : T.left.Opens) : Prop :=
  ∃ e : BasedFunctor (discreteModuli (yoneda.obj (Over.mk (V.ι ≫ T.hom))))
      (moduliTwoFiberProduct t (fullModuliInclusion F U.property)),
    e.toFunctor.IsEquivalence ∧
      Nonempty (ModuliTwoIso
        (e.comp (moduliTwoFiberFst t (fullModuliInclusion F U.property)))
        (discreteModuliMap (yoneda.map
          (Over.homMk V.ι rfl : Over.mk (V.ι ≫ T.hom) ⟶ T))))

/-- Open substacks form a set, and every set-indexed family has an algebraic union,
with its least-upper-bound property, its scheme pullbacks, and its relative open cover.
The empty family gives precisely the empty open substack: all objects over the empty
scheme and no objects over any nonempty scheme.
Source: Stacks Project, Tags 06FJ and 05UQ
(blueprint: lem-sfb-open-substack-unions).

Proof:
1. Choose a smooth surjective scheme atlas P of F. By
   lem-sfb-invariant-open-substack-descent, full open substacks correspond to invariant
   opens in P. These form a subset of its power set, proving smallness in universe u.
   Strict fullness identifies equivalence over F with equality of object predicates.
2. For each input open pull back to V_i in P. The union V is invariant because inverse
   images commute with unions. Apply the same descent lemma to obtain W.
3. Its full inclusion identifies its diagonal tests with those of F. The open V in P
   gives a smooth surjective scheme atlas of W: after any scheme test it is the base
   change of P over F. Thus W is algebraic, including when V is empty.
4. The descent lemma's factorization criterion proves each input lies in W and W lies
   in every common upper bound. Strict fullness turns factorizations into predicate
   implications. Restricting the input predicates to W gives the relative open substacks.
5. For a scheme T mapping to F, pull back further to Q = T ×_F P. The inverse images
   of W_T and the union of the input opens agree by construction on P. The projection
   Q to T is surjective, so these open subsets of T agree, with their projections.
6. If T maps to W, this equality says the relative input opens cover T. If the family
   is empty every scheme pullback is empty. No object over a nonempty scheme can lie
   in W, since it would give a section of this empty pullback. Descent for the empty
   covering and the isomorphism-sheaf condition give a terminal fibre over the empty
   scheme, and strict fullness retains every ambient object in that fibre. -/
theorem openModuliSubstack_unions {S : Scheme.{u}}
    (F : BasedCategory.{v, w} (Over S)) (hF : IsAlgebraicModuliStack F) :
    Small.{u} (OpenModuliSubstack F) ∧
      ∀ (I : Type z) (U : I → OpenModuliSubstack F),
        ∃ (W : OpenModuliSubstack F) (A : I → OpenModuliSubstack W.category),
          IsAlgebraicModuliStack W.category ∧
          (∀ i : I, (U i).IsContainedIn W) ∧
          (∀ Z : OpenModuliSubstack F,
            (∀ i : I, (U i).IsContainedIn Z) → W.IsContainedIn Z) ∧
          (∀ (T : Over S) (t : BasedFunctor (discreteModuli (yoneda.obj T)) F),
            ∃ V : I → T.left.Opens,
              (∀ i : I, (U i).HasPullbackOpen T t (V i)) ∧
                W.HasPullbackOpen T t (⨆ i : I, V i)) ∧
          (∀ (i : I) (x : W.category.obj), (A i).property x ↔ (U i).property x.obj) ∧
          (∀ (T : Over S)
              (t : BasedFunctor (discreteModuli (yoneda.obj T)) W.category),
            ∃ V : I → T.left.Opens,
              (∀ i : I, (A i).HasPullbackOpen T t (V i)) ∧ (⨆ i : I, V i) = ⊤) ∧
          (IsEmpty I → ∀ x : F.obj, W.property x ↔ IsEmpty (F.p.obj x).left) := by
  sorry

end CategoryTheory
