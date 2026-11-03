/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.PurTwistCanonicalMaps

/-! # Canonical integral root comparisons
Source: coefficient twists, canonical comparisons.
(blueprint: lem-pur-integral-root-comparisons)
-/
@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory MonoidalCategory Limits Opposite
open scoped CategoryTheory.Obj CategoryTheory.MonObj
namespace AlgebraicGeometry.ProEtale

/-- The prescribed integral cone lift and finite scalar-adjoints are isomorphisms.
Source: def-coefficient-twists-detailed, projection-induced integral comparisons;
companion local-freeness proof, step 3.
(blueprint: lem-pur-integral-root-comparisons).
Proof: choose the compatible-root cover and its finite cyclic bases. The free finite
bases commute with coefficient reductions and root powers. Consequently their
inverse-limit basis identifies the actual integral twist with the regular continuous
O_E module; the coefficient-limit theorem gives this basis with all projection
squares. Its n-th projection is quotient reduction to A_E,n+1. Extension of scalars
along that quotient sends the specified projection to the regular scalar-extension
isomorphism: its formula in these bases is b tensor a maps to bar(b)a. This proves
the finite comparison, without commuting tensor with an inverse limit.
The Tate residue basis identifies T_S with the regular Z_ell module and each Tate
projection with residue reduction. Scalar extension to O_E identifies the source of
the integral comparison with the regular O_E module. On every finite coordinate its
specified leg sends 1 tensor b to bar(b) times the chosen root; this follows from the
underlying tensor formula of coefficientFreeTensor_linear and the scalar adjunction
unit. The supplied compatibility makes these legs a cone. By the uniqueness of the
limit lift the resulting comparison is the identity in the two integral bases, so
it is an isomorphism. Pullback of these specified maps is identified using the
adjunction-unit formulas for scalar pullback. Detect both isomorphisms on the cover,
including the empty base. The choice of proof of compatibility is irrelevant. -/
theorem pur_integral_root_comparisons
    (S : Scheme.{u}) (ell : ℕ) [Fact ell.Prime]
    (E : Type u) [Field E] [Algebra (Padic ell) E]
    [FiniteDimensional (Padic ell) E]
    [∀ x : S, Invertible (ell : S.residueField x)]
    (hcompat : integralTateLegCompatibilityStatement S ell E) :
    (∀ (n : ℕ), IsIso (coefficientFiniteReduction S ell E n)) ∧
    IsIso (limit.lift (coefficientIntegralTwistSystem ell E S)
      (Cone.mk (integralTateLine S ell E)
        (NatTrans.ofOpSequence (integralTateLeg S ell E) (by
          intro n
          simp only [Functor.const_obj_map, coefficientIntegralTwistSystem,
            Functor.ofOpSequence_map_homOfLE_succ]
          apply Mod.hom_ext
          exact (hcompat n).symm)))) := by sorry

end AlgebraicGeometry.ProEtale
