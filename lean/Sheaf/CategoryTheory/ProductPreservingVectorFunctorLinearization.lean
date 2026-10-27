module

public import Mathlib.Algebra.Category.FGModuleCat.Limits
public import Mathlib.CategoryTheory.Linear.LinearFunctor

/-! # Linearization of a product-preserving set-valued vector-space functor

Source: Stacks Project, Tag 06I6, `formal-defos.tex`, lemma-linear-functor,
specialized to finite-dimensional vector spaces over a field
(blueprint: lem-sfb-product-preserving-vector-functor-linearization).

The lift has exactly the given underlying set-valued functor. Its linearity includes
both additivity and scalar linearity on morphisms. The displayed identification is
only transport along that equality, and introduces no choice of bijections.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v w

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

/-- The comparison induced by the two projections of a binary product.
Source: Stacks Project, Tag 06I6, lemma-linear-functor
(blueprint: lem-sfb-product-preserving-vector-functor-linearization). -/
def vectorFunctorProductComparison {k : Type u} [Field k]
    (L : FGModuleCat.{v} k ⥤ Type w) (U V : FGModuleCat.{v} k) :
    L.obj (U ⨯ V) → L.obj U × L.obj V :=
  fun t ↦ (L.map prod.fst t, L.map prod.snd t)

/-- The equality of the underlying functors identifies each lifted carrier with its
original set. This is equality transport, not an arbitrary natural isomorphism.
Source: Stacks Project, Tag 06I6, the commutative triangle in lemma-linear-functor
(blueprint: lem-sfb-product-preserving-vector-functor-linearization). -/
def vectorFunctorLiftIdentification {k : Type u} [Field k]
    {L : FGModuleCat.{v} k ⥤ Type w} (F : FGModuleCat.{v} k ⥤ ModuleCat.{w} k)
    (h : F ⋙ forget (ModuleCat.{w} k) = L) (V : FGModuleCat.{v} k) :
    F.obj V ≃ L.obj V :=
  Equiv.cast (congrArg (fun G : FGModuleCat.{v} k ⥤ Type w ↦ G.obj V) h)

/-- A product-preserving set-valued functor on finite-dimensional vector spaces has a
unique linear lift, with its zero, addition and scalar operations induced by the
corresponding linear maps. Binary product comparisons are linear isomorphisms.
Source: Stacks Project, Tag 06I6, lemma-linear-functor
(blueprint: lem-sfb-product-preserving-vector-functor-linearization).

Proof:
1. Every zero map factors through the zero space; its image is constant, since L(0)
is a singleton. Compare projections to obtain the pairing formula and the identity
L(f direct-sum g) q(x,y) = q(L(f)x,L(g)y), where q is the inverse comparison.
2. Define zero by L(0 to V), addition by L(+) q, and negation by L(-id).
The two inclusions give the zero laws, the interchange of coordinates gives
commutativity, and the pair (id,-id) gives additive inverses.
3. Lift (x,y,z) to L((V direct-sum V) direct-sum V). Its three projections identify
the two iterated sums with the images of the same linear map, proving associativity.
4. Define scalar multiplication by L(a id). Identity and composition give the unit
and multiplication laws. Pairing (a id,b id) and then adding proves (a+b)x=ax+bx.
5. The identity (a id) +_V = +_V ((a id) direct-sum (a id)) gives distributivity
across addition, and the zero-map calculation gives a0=0. These are all module laws.
6. The identities f +_U = +_V (f direct-sum f) and f (a id)=(a id) f show that each
L(f) is linear. Identities and composition remain those of the original functor.
7. Write f+g as addition after the pairing (f,g) and af as (a id) f. The pairing
formula gives additivity and scalar linearity on Hom, as in def-weil-linear-functor.
8. The comparison has linear components and is bijective. Its inverse is additive
and homogeneous by injectivity of the comparison, so it is a linear equivalence.
9. Any other linear lift has the same zero by L(0 to V), the same scalar operation
by Hom-linearity applied to a id, and the same addition by +_V=p1+p2. Its inverse
operation and all structural proofs are forced, and its arrow maps were already L.
Thus the vector-space structures, and hence the lift, are unique. -/
theorem productPreservingVectorFunctor_linearization {k : Type u} [Field k]
    (L : FGModuleCat.{v} k ⥤ Type w)
    (hzero : Unique (L.obj (FGModuleCat.of k PUnit.{v + 1})))
    (hprod : ∀ U V : FGModuleCat.{v} k,
      Function.Bijective (vectorFunctorProductComparison L U V)) :
    ∃ (F : FGModuleCat.{v} k ⥤ ModuleCat.{w} k)
      (h : F ⋙ forget (ModuleCat.{w} k) = L),
      F.Additive ∧ F.Linear k ∧
      (∀ G : FGModuleCat.{v} k ⥤ ModuleCat.{w} k,
        G ⋙ forget (ModuleCat.{w} k) = L → G.Additive → G.Linear k → G = F) ∧
      (∀ V : FGModuleCat.{v} k,
        vectorFunctorLiftIdentification F h V 0 =
          L.map (0 : FGModuleCat.of k PUnit.{v + 1} ⟶ V) hzero.default) ∧
      (∀ (V : FGModuleCat.{v} k) (x y : F.obj V),
        vectorFunctorLiftIdentification F h V (x + y) =
          L.map (prod.fst + prod.snd : V ⨯ V ⟶ V)
            ((Equiv.ofBijective (vectorFunctorProductComparison L V V) (hprod V V)).symm
              (vectorFunctorLiftIdentification F h V x,
                vectorFunctorLiftIdentification F h V y))) ∧
      (∀ (V : FGModuleCat.{v} k) (a : k) (x : F.obj V),
        vectorFunctorLiftIdentification F h V (a • x) =
          L.map (a • 𝟙 V) (vectorFunctorLiftIdentification F h V x)) ∧
      (∀ U V : FGModuleCat.{v} k,
        ∃ e : F.obj (U ⨯ V) ≃ₗ[k] (F.obj U × F.obj V),
          ∀ t : F.obj (U ⨯ V),
            e t = (F.map prod.fst t, F.map prod.snd t)) := by
  sorry

end CategoryTheory
