module

public import Sheaf.AlgebraicGeometry.ArtinCofinalFiltrationSystem
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem

/-! # Independence of formal objects from a cofinal ideal filtration

Source: Stacks Project, Formal Deformation Theory, Tag 06H6
(blueprint: lem-sfb-artin-formal-filtration-comparison).

The equivalence retains natural evaluation comparisons for every factorization
C → C/I_n → A. A single commuting-square equation expresses their compatibility
with transitions, changes of factorization and further test-algebra transport.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v w

open CategoryTheory

namespace AlgebraicGeometry.ArtinDeformation

/-- The groupoid of compatible systems over a cofinal filtration is equivalent to
the recorded groupoid of formal objects, compatibly with all evaluations.
Source: Stacks, Tag 06H6 (blueprint: lem-sfb-artin-formal-filtration-comparison).

Proof plan (the six steps of the DAG node):
1. Each quotient C/I_n is an Artinian local marked test, since it is a quotient of
   a Noetherian local ring by a proper ideal containing a positive maximal-ideal
   power (lem-weil-pbc-noetherian-local-quotient-artinian-local). Choose increasing
   cofinal reindexings p and q, both at least the original index, with
   I_{p(r)} ⊆ m^r and m^{q(n)} ⊆ I_n.
2. Send a system u to the formal system whose r-th component is the transport of
   u_{p(r)} to C/m^r. Transport the transition of u to define each transition and
   transport components to define the action on arrows. The cocycle for u and the
   associativity constraints of def-sfb-artin-deformation-test-category prove the
   formal-system equations and functor laws.
3. Conversely transport the q(n)-th formal component to C/I_n. The composite GE
   is naturally isomorphic to the identity by the transitions from p(q(n)) to n.
   Both paths in each square are the same iterated transition; naturality is the
   original arrow compatibility square.
4. Similarly EG is naturally isomorphic to the identity by transitions from
   q(p(r)) to r. These functors and natural isomorphisms give the equivalence.
   No predeformation, descent or lifting hypothesis is used.
5. To evaluate at C/I_n, choose r large enough that m^r ⊆ I_n and p(r) ≥ n.
   Composition of transports followed by the transition from p(r) to n identifies
   evaluation with u_n. Enlarging r changes neither comparison. The cocycle gives
   compatibility in n and the arrow square gives naturality in u.
6. For C → C/I_n → A, transport the preceding comparison to A. Pseudofunctor
   associativity identifies further transport with the comparison for the composite.
   Two different indices are compared at a common larger index and truncation;
   both composites are the same transition. This gives the final commuting-square
   equation, including its identity and equal-index cases. Evaluation here is the
   recorded least-nilpotence-index evaluation; evaluationFromHigher and
   evaluationRestriction identify it with the common large truncation used above.
-/
theorem formal_filtration_comparison
    {R k : Type u} [CommRing R] [IsNoetherianRing R] [Field k] [Algebra R k]
    [Algebra.FiniteType R k] (F : CofibredGroupoids.{u, v, w} R k)
    (C : CompleteLocalAlgebra R k) (I : CofinalIdealFiltration C) :
    ∃ E : FiltrationSystem I F ≌ FormalObject F C,
      ∃ e : ∀ (s : FiltrationSystem I F) (n : ℕ) (A : TestCategory R k)
        (f : filtrationTest I n ⟶ A),
        evaluate (E.functor.obj s) (filtrationLocalMap I n f) ≅
          (push F f).obj (s.obj n),
        (∀ (s t : FiltrationSystem I F) (a : s ⟶ t) (n : ℕ)
          (A : TestCategory R k) (f : filtrationTest I n ⟶ A),
          (push F (evaluationMap (filtrationLocalMap I n f))).map
              ((E.functor.map a).app (nilpotenceIndex A)) ≫ (e t n A f).hom =
            (e s n A f).hom ≫ (push F f).map (a.app n)) ∧
        (∀ (s : FiltrationSystem I F) (n m : ℕ) (h : m ≤ n)
          (A B : TestCategory R k) (f : filtrationTest I n ⟶ A)
          (f' : filtrationTest I m ⟶ B) (g : A ⟶ B)
          (hg : f ≫ g = filtrationMap I h ≫ f'),
          (push F g).map (e s n A f).hom ≫
              (filtrationTransportComparison I s h f f' g hg).hom =
            (evaluationRestriction (E.functor.obj s) g
              (filtrationLocalMap I m f') (filtrationLocalMap I n f)
              (filtrationLocalMap_comp I h f f' g hg)).hom ≫ (e s m B f').hom) :=
  sorry

end AlgebraicGeometry.ArtinDeformation
