module

public import Sheaf.AlgebraicGeometry.GroupScheme.SplitTorusOverRing
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Mod
public import Mathlib.LinearAlgebra.Finsupp.Defs

/-! # Integer grading of an affine scheme with a multiplicative-group action

Source: Stacks Project, Tags 0EKK and 0EKJ, relative to an arbitrary commutative ring.
(blueprint: lem-sfb-gm-affine-action-grading).

The internal action is over Spec R. A point t of the Laurent spectrum corresponds to
its unit coordinate t(z); thus t(z^n) in the formula below is exactly t(z)^n, including
negative n. Points of Spec C are R-algebra maps, via the fully faithful algSpec functor.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry

/-- A multiplicative-group action on Spec C determines integer weight submodules with
unique finite decompositions, homogeneous multiplication, and the prescribed point action.

Source: Stacks Project, Tag 0EKK, lemma-complete-reducibility-Gm, and Tag 0EKJ,
example-Gm-on-affine; the same coefficient proof works relative to any commutative ring.
(blueprint: lem-sfb-gm-affine-action-grading).

Proof plan:
1. Put L = C[z,z^-1]. The constant inclusion i:C -> L and universal unit z determine
   a point of G times_R X (def-weil-affine-spectrum and def-pc-fibre-product). Applying
   the action gives rho:C -> L. Naturality under Spec h gives h*rho = a_B(h(z),h*i).
   Substituting h(sum c_n z^n) = sum x(c_n)t^n gives the point-action formula.
2. Let p_n(c) be the coefficient of z^n in rho(c). The maps p_n are R-linear and
   have finite support on each c. Evaluating at z=1 and using the identity action
   gives sum_n p_n(c)=c.
3. In C[w,w^-1][z,z^-1], associativity of the action says that the expansions
   sum_n sum_m p_m(p_n(c))w^m z^n and sum_n p_n(c)w^n z^n agree. Comparing both
   coefficients gives p_m p_n=0 for m unequal to n, and p_n p_n=p_n.
4. Set W_n={c | rho(c)=c*z^n}. These are R-submodules by R-linearity, and step 3
   puts p_n(c) in W_n. Step 2 gives the finite decomposition. Applying rho to a
   finite homogeneous relation and comparing coefficients proves uniqueness.
5. Since rho is an R-algebra map, 1 and every algebraMap R C r have weight zero.
   Multiplicativity gives rho(cd)=cd*z^(m+n) for c in W_m and d in W_n.
6. Substitution in rho(c)=c*z^n gives a_B(t,x)(c)=t^n*x(c) on every test algebra.
   All expansions and coefficient comparisons are finite; no further ring hypothesis
   is used. For a scheme-valued t, pullback of LaurentPolynomial.T n is t(z)^n. -/
theorem exists_grading_of_gm_affine_action
    (R C : Type u) [CommRing R] [CommRing C] [Algebra R C]
    [ModObj (RingGroupSchemes.multiplicative R).X
      ((algSpec (.of R)).obj (op (CommAlgCat.of R C)))] :
    ∃ W : ℤ → Submodule R C,
      (∀ c : C, ∃! d : ℤ →₀ C,
        (∀ n : ℤ, d n ∈ W n) ∧ d.sum (fun _ v ↦ v) = c) ∧
      (1 : C) ∈ W 0 ∧
      (∀ r : R, algebraMap R C r ∈ W 0) ∧
      (∀ (m n : ℤ) (c d : C), c ∈ W m → d ∈ W n → c * d ∈ W (m + n)) ∧
      ∀ (B : Type u) [CommRing B] [Algebra R B] (x : C →ₐ[R] B)
        (t : (algSpec (.of R)).obj (op (CommAlgCat.of R B)) ⟶
          (RingGroupSchemes.multiplicative R).X) (n : ℤ) (c : C),
        c ∈ W n →
          (Spec.preimage (t • (algSpec (.of R)).map (CommAlgCat.ofHom x).op).left :
            CommRingCat.of C ⟶ CommRingCat.of B).hom c =
            (Spec.preimage t.left :
              CommRingCat.of (LaurentPolynomial R) ⟶ CommRingCat.of B).hom
                (LaurentPolynomial.T n) * x c := by
  sorry

end AlgebraicGeometry
