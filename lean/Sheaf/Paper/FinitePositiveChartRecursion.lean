/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group R4
-/
module

public import Sheaf.Paper.FiniteFirstRootChart
public import Sheaf.Paper.FiniteSignedTwistProducts

/-! # Ordered ordinary positive charts

The charts are constructed by recursion from the zero chart, the given first chart,
and the existing signed products. Source: finite-reduction proof, Step 2, ordered
positive powers (expanded Step 8).
(blueprint: lem-pur-finite-positive-chart-recursion)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures.PurityFiniteSetting

/-- Construct the ordinary zero chart using the coefficient realization unit.
Source: finite-reduction proof Step 2, coefficient one at zero.
(blueprint: lem-pur-finite-positive-chart-recursion). -/
def finiteTensorOrdinaryZeroChart (P : PurityFiniteSetting.{u}) (T : Scheme.{u}) :
    P.finiteTensorFixedSheaf T 0 ≅
      𝟙_ (Sheaf (ProEt.topology T) (ModuleCat.{u + 1} P.Coefficient)) :=
  letI : Finite P.Ring := Padic.finite_coefficientExtensionRing
    P.coefficients.l P.extension P.level P.level_pos
  (sfIntrinsicModuleEquivalence T P.Ring).inverse.mapIso
      (proEtaleConstantModuleUnit T P.Ring).symm ≪≫
    (sfIntrinsicModuleEquivalence T P.Ring).unitIso.symm.app
      (proEtaleFixedConstantModule T P.Ring)

/-- Ordered tensor recursion on actual sheaf isomorphisms, with the given first chart.
No existence theorem is used to select the positive charts.
Source: finite-reduction proof Step 2, ordered positive powers, expanded Step 8.
(blueprint: lem-pur-finite-positive-chart-recursion). -/
def finiteTensorOrdinaryChartRecursion (P : PurityFiniteSetting.{u}) (T : Scheme.{u})
    [T.Over (Spec (.of P.field.k))]
    (e₁ : P.finiteTensorFixedSheaf T 1 ≅
      𝟙_ (Sheaf (ProEt.topology T) (ModuleCat.{u + 1} P.Coefficient))) :
    (d : ℕ) → P.finiteTensorFixedSheaf T d ≅
      𝟙_ (Sheaf (ProEt.topology T) (ModuleCat.{u + 1} P.Coefficient))
  | 0 => P.finiteTensorOrdinaryZeroChart T
  | 1 => e₁
  | n + 2 =>
    eqToIso (congrArg (P.finiteTensorFixedSheaf T)
      (show ((n + 2 : ℕ) : ℤ) = ((n + 1 : ℕ) : ℤ) + 1 by omega)) ≪≫
    (P.finiteTensorSheafProducts T ((n + 1 : ℕ) : ℤ) 1).symm ≪≫
    tensorIso (P.finiteTensorOrdinaryChartRecursion T e₁ (n + 1)) e₁ ≪≫
    λ_ _

/-- The explicit recursion sends every compatible ordered basis vector to one.
Source: literature/blueprint/latest/blueprint/sec-smooth-purity/sk-lem-sp-reduction/
thm-pur-finite-reduction-of-purity.proof.md, Step 2, compatibility with the
invertible twist by associativity; expanded Step 8 of the root-chart construction.
(blueprint: lem-pur-finite-positive-chart-recursion).
Proof: at zero the realization unit and counit identify the frame vector with the
coefficient-one section. At one the assertion is the hypothesis on the first chart.
For degree n+2 use the normalized signed product in degrees n+1 and 1. The positive
frame condition says its source basis tensor maps to the degree n+2 basis. Realization is an
isomorphism on section modules, so the inverse product takes the given basis to
that tensor. Apply the induction hypothesis and the first-chart hypothesis; tensor
naturality followed by the unit unitor sends the tensor of the two coefficient-one
sections to coefficient one. This works on every object of the site, including the
empty object, and proves the assertion by induction without choosing any frame. -/
theorem finiteTensorOrdinaryChartRecursion_normalized (P : PurityFiniteSetting.{u})
    (T : Scheme.{u}) [T.Over (Spec (.of P.field.k))]
    (e₁ : P.finiteTensorFixedSheaf T 1 ≅
      𝟙_ (Sheaf (ProEt.topology T) (ModuleCat.{u + 1} P.Coefficient)))
    (d : ℕ) (V : T.ProEt) (b : P.FiniteTensorFrame T V)
    (x₁ : (P.finiteTensorFixedSheaf T 1).obj.obj (Opposite.op V))
    (x : (P.finiteTensorFixedSheaf T d).obj.obj (Opposite.op V))
    (hx₁ : HEq (P.finiteTensorSection T 1 V x₁) (P.finiteTensorFrameBasis T V b 1))
    (he₁ : e₁.hom.hom.app (Opposite.op V) x₁ =
      (Functor.LaxMonoidal.ε (sheafToPresheaf (ProEt.topology T)
        (ModuleCat.{u + 1} P.Coefficient))).app (Opposite.op V) (1 : P.Coefficient))
    (hx : HEq (P.finiteTensorSection T d V x) (P.finiteTensorFrameBasis T V b d)) :
    (P.finiteTensorOrdinaryChartRecursion T e₁ d).hom.hom.app (Opposite.op V) x =
      (Functor.LaxMonoidal.ε (sheafToPresheaf (ProEt.topology T)
        (ModuleCat.{u + 1} P.Coefficient))).app (Opposite.op V) (1 : P.Coefficient) := by
  sorry

end WeilConjectures.PurityFiniteSetting
