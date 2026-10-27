/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N0
-/
module

public import Sheaf.RingTheory.CotangentResolutionCoherence
public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.TensorProduct.MvPolynomial

/-!
# Quotients of standard polynomial resolutions

Source: Stacks Project, Cotangent Complex, Tag 08SD, remark-triangle
(blueprint: lem-sfb-injective-standard-resolution-quotients).

The quotient is the pushout of simplicial commutative rings, hence the degreewise
algebra tensor product. Its augmentation is induced by the two given augmentations.
The standard objects and their map are specified by the recorded polynomial formulas,
without choosing new resolution data from an existence theorem.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite Simplicial

namespace Algebra.CotangentResolution

/-- The simplicial `B`-algebra `Q ⊗_P B` and its induced augmentation to `C`.
The pushout in commutative rings is the algebra tensor product, and functor-category
pushouts are pointwise. The augmentation sends `q ⊗ b` to `ε_Q(q) j(b)`.
Source: Stacks Project, Tag 08SD, remark-triangle
(blueprint: lem-sfb-injective-standard-resolution-quotients). -/
def quotientAugmentation {A B C : CommRingCat.{u}} (f : A ⟶ B) (j : B ⟶ C)
    (P : Augmentation (Arrow.mk f)) (Q : Augmentation (Arrow.mk (f ≫ j)))
    (h : AugmentedMap (Arrow.homMk' (𝟙 A) j (Category.id_comp (f ≫ j))) P Q) :
    Augmentation (Arrow.mk j) where
  algebra := pushout h.map P.augmentation
  base := pushout.inr h.map P.augmentation
  augmentation := pushout.desc Q.augmentation ((SimplicialObject.const CommRingCat).map j)
    (by
      apply NatTrans.ext
      funext n
      obtain ⟨n⟩ := n
      obtain ⟨n⟩ := n
      exact h.augmentation n)
  triangle := by
    intro n
    change (pushout.inr h.map P.augmentation ≫
      pushout.desc Q.augmentation ((SimplicialObject.const CommRingCat).map j) _).app
        (op ⦋n⦌) = j
    rw [pushout.inr_desc]
    rfl

/-- For an injective target map the quotient of the standard resolutions is a
polynomial resolution of `C` over `B`. The hypotheses `hP`, `hQ` and `hh` identify
exactly the standard objects and their functorial map, rather than arbitrary
polynomial resolutions or arbitrary comparison maps. The conclusion uses the
recorded resolution predicate: polynomial `B`-algebras, surjective augmentations,
and a quasi-isomorphism of the alternating complex in nonpositive degrees.
Its quasi-isomorphism condition is checked on underlying abelian groups; all
operators and the augmentation are `B`-linear, so this is equivalently a
quasi-isomorphism of `B`-module complexes.
Source: Stacks Project, Tag 08SD, remark-triangle
(blueprint: lem-sfb-injective-standard-resolution-quotients).

Proof:
1. By lem-trf-cotangent-resolution-coherence, P and Q resolve B and C, and
   their standard map commutes with the augmentations. The alternating complex
   of constant B has differentials zero in odd degrees and identity in positive
   even chain degrees. Its augmentation to B[0] is therefore a quasi-isomorphism,
   so the simplicial augmentation P → const B is a quasi-isomorphism too.
2. Induct on n, starting from the injectivity of j in degree -1. The standard
   map in degree n includes the polynomial variables indexed by P_(n-1) into
   those indexed by Q_(n-1). The complementary variables E_n exhibit Q_n as
   P_n[E_n], by def-weil-pbc-mv-polynomial-ring. Evaluating E_n at zero retracts
   this inclusion, giving the injectivity needed for the induction.
3. The monomials in E_n freely generate Q_n over P_n. Thus Q_n is flat by
   lem-weil-pbc-projective-module-flat, including infinite variable sets.
4. Polynomial scalar extension identifies Q_n ⊗_(P_n) B with B[E_n], using
   def-weil-pbc-module-tensor-product. The displayed pushout augmentation is
   balanced by augmentation compatibility. A lift q of c under Q_n → C gives
   q ⊗ 1 mapping to c, so each quotient augmentation is surjective.
5. Apply lem-sfb-simplicial-flat-base-change-quasi-iso with R=P, S=const B,
   and M=Q. Steps 1 and 3 show that Q → Q ⊗_P B is a quasi-isomorphism.
   Its composite with the quotient augmentation is the standard augmentation
   of Q, also a quasi-isomorphism. Two-out-of-three on cohomology proves the
   required assertion. Forgetting B-module structure preserves kernels, images
   and cohomology, and a bijective B-linear map has a B-linear inverse. -/
theorem isPolynomialResolution_quotient_of_injective
    {A B C : CommRingCat.{u}} (f : A ⟶ B) (j : B ⟶ C) (hj : Function.Injective j)
    (P : Augmentation (Arrow.mk f)) (Q : Augmentation (Arrow.mk (f ≫ j)))
    (hP : IsStandard P) (hQ : IsStandard Q)
    (h : AugmentedMap (Arrow.homMk' (𝟙 A) j (Category.id_comp (f ≫ j))) P Q)
    (hh : ∀ n : ℕ, HEq (h.map.app (op ⦋n⦌))
      (standardSquareMap (Arrow.homMk' (𝟙 A) j (Category.id_comp (f ≫ j))) n)) :
    IsPolynomialResolution (quotientAugmentation f j P Q h) := by
  sorry

end Algebra.CotangentResolution
