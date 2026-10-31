/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SfStrictDirectImageScalarData

/-! # Integral coherence required for rational scalar descent

Source: strict direct-image scalar comparison, Steps 4--7.
(blueprint: def-sf-strict-direct-image-integral-coherence)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe u v
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.SfStrictDirectImageScalar
variable (l : ℕ) [Fact l.Prime]
variable (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
open AlgebraicallyClosedCoefficients (Index Coefficient coefficientInclusion)
open GeneralAlgebraicallyClosedCoefficients (integralTransition)

/-- The integral scalar associator with the actual coefficient-inclusion transport.
Source: scalar-comparison proof, Step 4.
(blueprint: def-sf-strict-direct-image-integral-coherence) -/
def integralAssociator (W : Scheme.{u}) (E L M : Index l Ω) (h : E ≤ L) (j : L ≤ M) :
    integralTransition l Ω W E L h ⋙ integralTransition l Ω W L M j ≅
      integralTransition l Ω W E M (h.trans j) :=
  sfIntegralScalarComp l (Coefficient.{u} l Ω E) (Coefficient.{u} l Ω L)
    (coefficientInclusion l Ω E L h) W 0 (Nat.Prime.ne_zero (Fact.out : l.Prime))
    (Coefficient.{u} l Ω M) (coefficientInclusion l Ω L M j) ≪≫
    eqToIso (congrArg
      (fun ι ↦ sfConstructibleIntegralScalarExtension 0 l
        (Nat.Prime.ne_zero (Fact.out : l.Prime)) (Coefficient.{u} l Ω E)
        (Coefficient.{u} l Ω M) ι W)
      ((AlgebraicallyClosedCoefficients.coefficientInclusion_laws l Ω).2 E L M h j))

/-- The two integral laws needed when descending the comparisons to raw rational Hom groups.
Source: scalar-comparison proof, Steps 4--7.
(blueprint: def-sf-strict-direct-image-integral-coherence) -/
def HasIntegralCoherence {Z X : Scheme.{u}} (f : Z ⟶ X)
    (D : IntegralComparisons l Ω f) : Prop :=
  (∀ (E L : Index l Ω) (h : E ≤ L),
    NatTrans.CommShift (D.integralComparison E L h).hom ℤ) ∧
  (∀ (E L M : Index l Ω) (h : E ≤ L) (j : L ≤ M)
    (K : sfIntegralConstructibleCategory l (Coefficient.{u} l Ω E) Z),
    (D.integralComparison L M j).hom.app ((integralTransition l Ω Z E L h).obj K) ≫
        (integralTransition l Ω X L M j).map ((D.integralComparison E L h).hom.app K) ≫
        (integralAssociator l Ω X E L M h j).hom.app ((D.integral E).image.obj K) =
      (D.integral M).image.map ((integralAssociator l Ω Z E L M h j).hom.app K) ≫
        (D.integralComparison E M (h.trans j)).hom.app K)

end WeilConjectures.SfStrictDirectImageScalar
