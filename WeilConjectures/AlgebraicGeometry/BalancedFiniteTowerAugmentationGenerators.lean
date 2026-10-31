/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FinitePullbackStrictTowerData

/-! # Augmentation on normalized Koszul basis generators

Source: Stacks Project, sites-cohomology.tex, Tag 07A4 and sites-modules.tex, Tag 03EL.
(blueprint: lem-a1-balanced-finite-tower-augmentation-generators).

The proof is the two-generator calculation on the degree minus one and degree
zero free summands. Extension to all sections is proved in the square module. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe t u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open WeilConjectures.CompletedTowerIndependent
open WeilConjectures.FinitePullbackStrictTowerData
open WeilConjectures.CompletedPullbackUniverseTransportData
namespace WeilConjectures.BalancedFiniteTower

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
variable {X Y : Scheme.{t}} (g : X ⟶ Y)

/-- The two augmentation routes agree on each pulled Koszul basis tensor.
Source: Stacks 03EK and the principal augmentation calculation in step 7 of
lem-a1-balanced-finite-tower-generator-comparison.
(blueprint: lem-a1-balanced-finite-tower-augmentation-generators).

Proof: apply KoszulNormalization with outer coefficient 1. In degree zero,
the principal cone augmentation maps its basis to the quotient unit. Tensor
functoriality and BalancedNormalization identify the left route with the finite
pullback generator, since pi_n(1)=1. Naturality of the pullback adjunction unit
moves the augmentation through the generator on the right. Its degree-zero
value is the same quotient-unit tensor, so QuotientUnitNormalization with
outer coefficient 1 gives exactly the same finite generator. In degree minus
one the cone augmentation vanishes, hence so do both routes. No equality on
arbitrary sections is asserted here: extension to all sections is the separate
proved tensor, sheafification and adjunction extensionality argument. -/
theorem normalized_theta_augmentation_generators
    (lambda : G l E g ⋙ reductions l E X ≅ finite l E g)
    (c : reductions l E Y ⋙ diagramPull l E g ≅ finite l E g)
    (hlambda : ∀ P : CochainComplex (Modules l E Y) ℤ,
      BalancedNormalization l E g P (lambda.app P))
    (hc : QuotientUnitNormalization l E g c)
    (theta : koszuls l E Y ⋙ diagramPull l E g ≅ G l E g ⋙ koszuls l E X)
    (P : CochainComplex (Modules l E Y) ℤ)
    (htheta : KoszulNormalization l E g P (theta.app P)) (n : ℕ) (k : ℤ)
    (negative : Bool) (p : ℤ) (hp : p + koszulDegree negative = k)
    (V : Y.ProEt) (x : (P.X p).val.obj (op V)) :
    let z := generator l E g (((H l E Y P).obj (op n)).X k) V
      (tensorGenerator l E Y P (PrincipalKoszulStrictReplacement.koszul l E Y n)
        p (koszulDegree negative) k hp (op V) x
        ((koszulBasis l E Y n negative).val.app (op V)
          (1 : (completedIntegralCoefficientSheafUnrestricted l E Y).obj.obj (op V))))
    ((((theta.hom.app P) ≫ augmentation l E X ((G l E g).obj P) ≫
      lambda.hom.app P).app (op n)).f k).val.app
        (op ((Scheme.proEtaleBaseChange g).obj V)) z =
      ((((diagramPull l E g).map (augmentation l E Y P) ≫
        c.hom.app P).app (op n)).f k).val.app
          (op ((Scheme.proEtaleBaseChange g).obj V)) z := by sorry

end WeilConjectures.BalancedFiniteTower
