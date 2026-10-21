/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.RamifiedPullbackTowerData

/-! # Normalized ramified finite pullback comparison

Source: Stacks 093M, 03EK and 03EL; Bhatt--Scholze 6.8.2(1).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe t u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open scoped ChangeOfRings
namespace WeilConjectures.RamifiedPullback
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
variable (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L)

/-- Normalized finite pullback base change, with its adjacent tower square.
Source: Stacks 03EL and 03EK; Bhatt--Scholze 6.8.2(1).
(blueprint: lem-weil-ramified-finite-pullback-comparison).

Proof: The inverse-image tensor comparison identifies the finite pullback with
inverse image of P tensored over the inverse-image completed ring with the finite
coefficient ring on X. Tensor this expression with the completed L ring and
associate the two last factors. The supplied coefficient isomorphism on X identifies
them with the L coefficient quotient. On the other route, pullback of P tensor S_Y
is inverse image of P tensor inverse image of S_Y. Tensoring with the L quotient
cancels that intermediate ring. The inverse balanced maps insert one and multiply
coefficients, so give inverse natural maps for all modules, without flatness.
Naturality makes them commute with differentials and with chain maps. Evaluating
on the two adjunction-unit tensor generators gives the displayed formula. The
constant-ring pullback maps commute with quotient inclusions since their adjoints
preserve constant sections. The supplied coefficient transition equation then
makes the adjacent square commute on generators. The tensor and pullback
adjunction universal properties detect equality, proving the entire square.
-/
theorem finitePullbackComparison_exists {X Y : Scheme.{t}} (g : X ⟶ Y)
    (e : ℕ) (hmono : Monotone (index e))
    (j : ∀ n : ℕ, Padic.coefficientExtensionRing l E (n + 1) →+*
      Padic.coefficientExtensionRing l L (index e n + 1))
    (hj : ∀ (n : ℕ) (a : Padic.coefficientExtensionIntegers l E),
      j n (Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E (n + 1)) a) =
        Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l L (index e n + 1))
          (integralScalarIntegerInclusion l E L ι a))
    (source : Coefficients l E L ι e j Y) (target : Coefficients l E L ι e j X) :
    ∃ levelIso : ∀ n : ℕ,
    integralOperationsPullbackLevel l E g n ⋙ scalarCx.{t, u} target.completedMap ≅
      scalarCx.{t, u} source.completedMap ⋙
        integralOperationsPullbackLevel l L g (index e n),
      ( ∀ (n : ℕ) (P : CochainComplex (integralTowerModules l E Y) ℤ)
    (i : ℤ) (V : Y.ProEt)
    (a : (integralCoefficientCommRingSheaf l E Y n).obj.obj (op V))
    (b : (integralCoefficientCommRingSheaf l E X n).obj.obj
      (op ((Scheme.proEtaleBaseChange g).obj V)))
    (s : (completedIntegralCommRingSheafUnrestricted l L X).obj.obj
      (op ((Scheme.proEtaleBaseChange g).obj V))) (p : (P.X i).val.obj (op V)),
    (((levelIso n).hom.app P).f i).val.app _
      (tensor target.completedMap (((integralOperationsPullbackLevel l E g n).obj P).X i)
        _ s (pullTensor l E g n P i V a b p)) =
      pullTensor l L g (index e n) ((scalarCx.{t, u} source.completedMap).obj P) i V
        ((ramifiedMap l E L Y e n (j n)).hom.app (op V) a)
        ((ramifiedMap l E L X e n (j n)).hom.app _ b *
          (completedIntegralCommRingProjectionUnrestricted l L X (index e n)).hom.app _ s)
        (tensor source.completedMap (P.X i) (op V) 1 p)) ∧
      ( ∀ (n : ℕ) (P : CochainComplex (integralTowerModules l E Y) ℤ),
    (scalarCx.{t, u} target.completedMap).map
        ((integralOperationsPullbackTransition l E g n).app P) ≫
          (levelIso n).hom.app P =
      (levelIso (n + 1)).hom.app P ≫
        transition l L g (index e n) (index e (n + 1)) (hmono (Nat.le_succ n))
          ((scalarCx.{t, u} source.completedMap).obj P)) := by sorry

end WeilConjectures.RamifiedPullback
