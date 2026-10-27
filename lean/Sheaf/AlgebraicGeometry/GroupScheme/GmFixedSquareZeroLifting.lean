module

public import Sheaf.AlgebraicGeometry.GroupScheme.SplitTorusOverRing
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Mod
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import WeilConjectures.AlgebraicGeometry.Thickening

/-! # Fixed points of the multiplicative group lift across square-zero extensions

Source: Milne, Algebraic Groups (2017), Theorem 13.1, p.254, and Lemma 13.6, p.256,
as motivation for the relative assertion; Stacks Project, Tags 0EKK and 0EKJ,
for the coordinate grading used in the arbitrary-base argument.
(blueprint: lem-sfb-gm-fixed-square-zero-lifting).

The action is an actual internal action, using the Laurent Hopf group scheme over R.
Fixedness tests every algebra extension and every morphism to that group scheme;
these morphisms are exactly units of the test algebra. Points of Spec C are algebra maps,
converted to scheme morphisms by the fully faithful affine spectrum functor.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry

/-- A universally fixed point of a smooth affine R-scheme lifts across a surjective
R-algebra map with square-zero kernel, and the lift is universally fixed.

Source: the agent-written relative extension of Milne, Theorem 13.1, p.254, motivated
by the weight-splitting method of Lemma 13.6, p.256; the coordinate grading is Stacks
Project, Tags 0EKK and 0EKJ.
(blueprint: lem-sfb-gm-fixed-square-zero-lifting).

Proof plan:
1. Apply lem-sfb-gm-affine-action-grading: C is the direct sum of its integer weight
   R-submodules C_n, R lands in C_0, and the action on C_n evaluates as t^n.
2. Test fixedness of x_0 after adjoining a Laurent variable, at its universal unit z.
   For n nonzero the equality z^n*x_0(c_n)=x_0(c_n) forces x_0(c_n)=0 by uniqueness
   of Laurent coefficients. Conversely, killing every nonzero weight implies fixedness
   after every algebra extension by the homogeneous action formula and finite additivity.
3. Surjectivity identifies B_0 with B_1/J. The affine-spectrum correspondence and
   def-weil-closed-immersion identify Spec B_0 -> Spec B_1 with the first order
   thickening of def-sbc-first-order-thickening, since J^2=0. Smoothness supplies an
   ordinary algebra lift f:C -> B_1. Every nonzero weight has image in J.
4. Define h(c)=f(c_0). This is additive and R-linear, preserves 1, and is multiplicative:
   for weights m,n both zero this follows from f; for m+n nonzero both required
   products vanish; for m=-n nonzero the two images under f lie in J, so their product
   vanishes by J^2=0. Finite distributivity proves multiplicativity on arbitrary elements.
5. The equality p*h=x_0 follows because x_0 kills the nonzero weights. The map h also
   kills them, so step 2 proves universal fixedness of this lift. This uses no field,
   Noetherian, connectedness, reductivity or residue-characteristic hypothesis. -/
theorem exists_gm_fixed_lift_of_square_zero
    (R C : Type u) [CommRing R] [CommRing C] [Algebra R C]
    [Smooth (Spec.map (CommRingCat.ofHom (algebraMap R C)))]
    [ModObj (RingGroupSchemes.multiplicative R).X
      ((algSpec (.of R)).obj (op (CommAlgCat.of R C)))]
    (B₁ B₀ : Type u) [CommRing B₁] [CommRing B₀] [Algebra R B₁] [Algebra R B₀]
    (p : B₁ →ₐ[R] B₀) (hp : Function.Surjective p)
    (hJ : RingHom.ker p.toRingHom ^ 2 = ⊥)
    (x₀ : C →ₐ[R] B₀)
    (hx₀ : ∀ (B : Type u) [CommRing B] [Algebra R B] (q : B₀ →ₐ[R] B)
      (t : (algSpec (.of R)).obj (op (CommAlgCat.of R B)) ⟶
        (RingGroupSchemes.multiplicative R).X),
      t • (algSpec (.of R)).map (CommAlgCat.ofHom (q.comp x₀)).op =
        (algSpec (.of R)).map (CommAlgCat.ofHom (q.comp x₀)).op) :
    ∃ x₁ : C →ₐ[R] B₁, p.comp x₁ = x₀ ∧
      ∀ (B : Type u) [CommRing B] [Algebra R B] (q : B₁ →ₐ[R] B)
        (t : (algSpec (.of R)).obj (op (CommAlgCat.of R B)) ⟶
          (RingGroupSchemes.multiplicative R).X),
        t • (algSpec (.of R)).map (CommAlgCat.ofHom (q.comp x₁)).op =
          (algSpec (.of R)).map (CommAlgCat.ofHom (q.comp x₁)).op := by
  sorry

end AlgebraicGeometry
