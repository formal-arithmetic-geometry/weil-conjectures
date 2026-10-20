/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group ND
-/
module

public import Sheaf.Paper.FiniteReductionChartCalculus
public import Sheaf.Paper.IntrinsicCoefficientTwistsUnrestricted
public import Sheaf.Paper.SmoothTrace
public import Sheaf.AlgebraicGeometry.ProEtaleConstantOpenSquareExchange
public import Sheaf.Paper.FourCorners
public import Sheaf.Paper.StratumScalarExtension
public import Sheaf.Paper.SfCompactSupportRestrictionOfScalars
public import WeilConjectures.AlgebraicGeometry.Sites.RootsOfUnity

/-! # Reduction of the canonical finite-coefficient purity maps

Source: main-20261015, sec-smooth-purity/sk-thm-purity-transport,
def-pur-finite-reduction-root-charts (blueprint: def-pur-finite-reduction-root-charts).

## Main definitions

- `finiteReduction`: the actual quotient scalar extension.
- `finiteReductionRootTrivialization`: the section-normalized root-line chart.
- `finiteReductionSourceTrivialization`: the shifted purity-source chart.

-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 4096
universe u v w
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
namespace WeilConjectures.PurityFiniteSetting
/-- Change only the positive coefficient level, retaining the fixed field and extension.
Source: blueprint finite-reduction statement
(blueprint: def-pur-finite-reduction-root-charts). -/
abbrev finiteReductionSetting (P : PurityFiniteSetting.{u}) (m : ℕ) (hm : 1 ≤ m) :
    PurityFiniteSetting.{u} :=
  { P with level := m, level_pos := hm }



/-- The actual quotient homomorphism O_E/(varpi^n) → O_E/(varpi^m).
Source: blueprint finite-reduction statement
(blueprint: def-pur-finite-reduction-root-charts). -/
def finiteReductionRingHom (P : PurityFiniteSetting.{u}) (m : ℕ) (hm : 1 ≤ m)
    (hmn : m ≤ P.level) : P.Ring →+* (P.finiteReductionSetting m hm).Ring :=
  Ideal.Quotient.factor (S := Padic.coefficientExtensionIdeal P.coefficients.l P.extension P.level)
    (T := Padic.coefficientExtensionIdeal P.coefficients.l P.extension m)
    (Ideal.pow_le_pow_right hmn)



/-- Derived tensor with the smaller quotient, with its target scalar action retained.
Source: blueprint finite-reduction statement; Stacks 06YY
(blueprint: def-pur-finite-reduction-root-charts). -/
def finiteReduction (P : PurityFiniteSetting.{u}) (m : ℕ) (hm : 1 ≤ m)
    (hmn : m ≤ P.level) (T : Scheme.{u}) :
    Scheme.proEtaleDerivedCategory T P.Ring ⥤
      Scheme.proEtaleDerivedCategory T (P.finiteReductionSetting m hm).Ring :=
  Scheme.proEtaleRingDerivedExtension
    (Scheme.proEtaleConstantRingMap (T := T) (P.finiteReductionRingHom m hm hmn))



/-- Finite reduction has the stated finite-Tor constructible domain and codomain.
Source: blueprint proof Step 1 (blueprint: def-pur-finite-reduction-root-charts).
Proof: take a bounded flat model in the Tor interval by lem-sf-flat-model and reduce
it termwise using lem-sf-reduction-flat-model. Scalar tensor associativity preserves
that Tor interval without flatness of the quotient. On a finite constructible
stratification, the resulting cohomology is locally constant and finite; this is
scalarExtensionFunctor_preserves_constructible_tor. The boundedness and
constructibility clauses together give the recorded finiteTorConstructible predicate. -/
theorem finiteReduction_preserves_ctf (P : PurityFiniteSetting.{u}) (m : ℕ)
    (hm : 1 ≤ m) (hmn : m ≤ P.level) (T : Scheme.{u})
    (K : Scheme.proEtaleDerivedCategory T P.Ring)
    (hK : finiteTorConstructible P.coefficients.l P.extension P.level P.level_pos T K) :
    finiteTorConstructible P.coefficients.l P.extension m hm T
      ((P.finiteReduction m hm hmn T).obj K) := by
  sorry



/-- The canonical scalar-extension/restriction adjunction, including its tensor unit.
Source: Stacks 06YY, 07A6; blueprint Step 1
(blueprint: def-pur-finite-reduction-root-charts). -/
def finiteReductionAdjunction (P : PurityFiniteSetting.{u}) (m : ℕ) (hm : 1 ≤ m)
    (hmn : m ≤ P.level) (T : Scheme.{u}) :
    P.finiteReduction m hm hmn T ⊣
      (Scheme.proEtaleCoefficientRestrictScalars T
        (P.finiteReductionRingHom m hm hmn)).mapDerivedCategory :=
  Scheme.proEtaleRingDerivedExtensionAdjunction
    (Scheme.proEtaleConstantRingMap (T := T) (P.finiteReductionRingHom m hm hmn))



/-- The fixed annihilating exponent is positive.
Source: purity coefficient conventions
(blueprint: def-pur-finite-reduction-root-charts). -/
instance finiteReductionExponentNeZero (P : PurityFiniteSetting.{u}) :
    NeZero P.diagonalExponent :=
  ⟨ne_of_gt (pow_pos (Fact.out : P.coefficients.l.Prime).pos P.level)⟩



/-- The section represented by a primitive base-field root, with no root chosen.
Source: Stacks 03PK, constantZModIsoRootsOfUnitySheaf
(blueprint: def-pur-finite-reduction-root-charts). -/
def finiteReductionRootSection (P : PurityFiniteSetting.{u}) (T : Scheme.{u})
    [T.Over (Spec (.of P.field.k))] (ζ : P.field.k)
    (hζ : IsPrimitiveRoot ζ P.diagonalExponent) (W : T.Etaleᵒᵖ) :
    (T.rootsOfUnitySheaf P.diagonalExponent).obj.obj W :=
  (T.constantZModIsoRootsOfUnitySheaf P.diagonalExponent
    (T ↘ Spec (.of P.field.k)) hζ).hom.hom.app W
      ((toSheafify T.smallEtaleTopology
        ((Functor.const T.Etaleᵒᵖ).obj
          (AddCommGrpCat.of (ULift.{u + 1} (ZMod P.diagonalExponent))))).app W
            (ULift.up (1 : ZMod P.diagonalExponent)))



/-- The coefficient-root trivialization is uniquely fixed on constant scalar sections.
Source: Stacks 03PK and blueprint Step 1
(blueprint: def-pur-finite-reduction-root-charts).
Proof: tensor the primitive-root isomorphism Z/N ≅ mu_N with the coefficient ring,
then sheafify. The map sends a to a tensor ζ, which gives the displayed formula.
The constant-sheaf generators determine a sheaf morphism uniquely. Primitive-root
trivialization and scalar extension make it an isomorphism, also on the empty scheme. -/
theorem existsUnique_finiteReductionRootTrivialization (P : PurityFiniteSetting.{u})
    (T : Scheme.{u}) [T.Over (Spec (.of P.field.k))] (ζ : P.field.k)
    (hζ : IsPrimitiveRoot ζ P.diagonalExponent) :
    ∃! t : Etale.ordinaryFiniteConstant P.Coefficient T ≅
        Scheme.finiteEtaleTateLine T P.diagonalExponent P.Coefficient
          P.diagonalExponent_annihilates,
      ∀ (W : T.Etaleᵒᵖ) (a : P.Coefficient),
        t.hom.hom.app W
            ((toSheafify T.smallEtaleTopology
              ((Functor.const T.Etaleᵒᵖ).obj (ModuleCat.of P.Coefficient P.Coefficient))).app
                W a) =
          Scheme.finiteEtaleTateOneGenerator P.Coefficient P.diagonalExponent T
            P.diagonalExponent_annihilates W a (P.finiteReductionRootSection T ζ hζ W) := by
  sorry



/-- The primitive-root trivialization used only to characterize coefficient comparisons.
Its data are uniquely determined by the preceding section formula.
Source: Stacks 03PK (blueprint: def-pur-finite-reduction-root-charts). -/
def finiteReductionRootTrivialization (P : PurityFiniteSetting.{u})
    (T : Scheme.{u}) [T.Over (Spec (.of P.field.k))] (ζ : P.field.k)
    (hζ : IsPrimitiveRoot ζ P.diagonalExponent) :
    Etale.ordinaryFiniteConstant P.Coefficient T ≅
      Scheme.finiteEtaleTateLine T P.diagonalExponent P.Coefficient
        P.diagonalExponent_annihilates :=
  (P.existsUnique_finiteReductionRootTrivialization T ζ hζ).choose



/-- The root chart of the shifted degree-one coefficient.
Source: blueprint Step 1 (blueprint: def-pur-finite-reduction-root-charts). -/
def finiteReductionShiftedLineChart (P : PurityFiniteSetting.{u})
    (T : Scheme.{u}) [T.Over (Spec (.of P.field.k))] (ζ : P.field.k)
    (hζ : IsPrimitiveRoot ζ P.diagonalExponent) :
    (Etale.ordinaryFiniteLine P.Coefficient P.diagonalExponent
      P.diagonalExponent_annihilates T)⟦(2 : ℤ)⟧ ≅
        (Etale.ordinaryFiniteUnit P.Coefficient T)⟦(2 : ℤ)⟧ :=
  (shiftFunctor _ (2 : ℤ)).mapIso
    ((_root_.DerivedCategory.singleFunctor _ 0).mapIso
      (P.finiteReductionRootTrivialization T ζ hζ).symm)


/-- The ordered root-power chart is the actual zero/successor tensor recursion
applied to the section-normalized degree-one root chart.
Source: blueprint reduction Step 1
(blueprint: def-pur-finite-reduction-root-charts). -/
def finiteReductionEtalePowerTrivialization (P : PurityFiniteSetting.{u})
    (T : Scheme.{u}) [T.Over (Spec (.of P.field.k))] (ζ : P.field.k)
    (hζ : IsPrimitiveRoot ζ P.diagonalExponent) (d : ℕ) :=
  finiteReductionEtaleRootPowerChart P.Coefficient P.diagonalExponent
    P.diagonalExponent_annihilates T (P.finiteReductionShiftedLineChart T ζ hζ) d

/-- Root trivialization of the actual pro-etale shifted coefficient line.
Source: blueprint Step 1 (blueprint: def-pur-finite-reduction-root-charts). -/
def finiteReductionPowerTrivialization (P : PurityFiniteSetting.{u})
    (T : Scheme.{u}) [T.Over (Spec (.of P.field.k))] (ζ : P.field.k)
    (hζ : IsPrimitiveRoot ζ P.diagonalExponent) (d : ℕ) :
    P.diagonalTwist T d ≅
      ((ProEtale.comparisonUpperStar
              (ModuleCat.{u + 1} P.Coefficient) T).mapDerivedCategory.obj
        (Etale.ordinaryFiniteUnit P.Coefficient T))⟦2 * (d : ℤ)⟧ :=
  let F := ProEtale.comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) T
  F.mapDerivedCategory.mapIso (P.finiteReductionEtalePowerTrivialization T ζ hζ d) ≪≫
    (F.mapDerivedCategory.commShiftIso (2 * (d : ℤ))).app _



/-- Untwisted inverse image in the very same realization coordinates as gamma.
Source: blueprint Step 1 (blueprint: def-pur-finite-reduction-root-charts). -/
def finiteReductionPullback (P : PurityFiniteSetting.{u}) {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  (Scheme.sfIntrinsicDerivedEquivalence Y P.Ring).inverse ⋙ P.smoothPurityPullback f ⋙
    (Scheme.sfIntrinsicDerivedEquivalence X P.Ring).functor



/-- Intermediate objects of the root chart in the existing fixed-scalar presentation.
Source: blueprint reduction Step 1
(blueprint: def-pur-finite-reduction-root-charts). -/
def FiniteReductionFixedChartStage (P : PurityFiniteSetting.{u}) (X : Scheme.{u})
    (d : ℕ) (M : _root_.DerivedCategory
      (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} P.Coefficient))) :
    Fin 4 → _root_.DerivedCategory
      (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} P.Coefficient)) :=
  fun i ↦ match i with
  | 0 => (P.compositionTwistShift X d).obj M
  | 1 => ((smoothPurityTensor P.Coefficient X).obj M).obj (P.diagonalTwist X d)
  | 2 => ((smoothPurityTensor P.Coefficient X).obj M).obj
      ((𝟙_ (_root_.DerivedCategory
        (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} P.Coefficient))))⟦2 * (d : ℤ)⟧)
  | 3 => M⟦2 * (d : ℤ)⟧

/-- The three fixed-scalar factors are the actual reassociation, root chart and
native tensor-unit shift comparison, in this order.
Source: blueprint reduction Step 1
(blueprint: def-pur-finite-reduction-root-charts). -/
def FiniteReductionFixedChartNormalized (P : PurityFiniteSetting.{u})
    (X : Scheme.{u}) [X.Over (Spec (.of P.field.k))]
    (d : ℕ) (ζ : P.field.k) (hζ : IsPrimitiveRoot ζ P.diagonalExponent)
    (M : _root_.DerivedCategory
      (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} P.Coefficient)))
    (a : (P.compositionTwistShift X d).obj M ≅ M⟦2 * (d : ℤ)⟧) : Prop :=
  let S := P.FiniteReductionFixedChartStage X d M
  ∃ i₀ : S 0 ≅ S 1, ∃ i₁ : S 1 ≅ S 2, ∃ i₂ : S 2 ≅ S 3,
    HEq i₀ (P.smoothPurityReassociation X d M) ∧
    (∃ b : P.diagonalTwist X d ≅
        ((𝟙_ (_root_.DerivedCategory
          (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} P.Coefficient))))⟦2 * (d : ℤ)⟧),
      HEq b (P.finiteReductionPowerTrivialization X ζ hζ d ≪≫
        (shiftFunctor _ (2 * (d : ℤ))).mapIso
          (finiteReductionComparisonUnitChart P.Coefficient X)) ∧
      HEq i₁ (((smoothPurityTensor P.Coefficient X).obj M).mapIso b)) ∧
    HEq i₂ (finiteReductionTensorUnit
      (ModuleCat.{u + 1} P.Coefficient) X M (2 * (d : ℤ))) ∧
    HEq a (i₀ ≪≫ i₁ ≪≫ i₂)

/-- The independent root chart has precisely the three specified fixed-scalar factors.
Source: blueprint reduction Step 1
(blueprint: def-pur-finite-reduction-root-charts).
Proof: expand the four intermediate objects. The first factor is the existing
Tate reassociation. The root-power chart and the coefficient-unit chart give the
second factor. The third is the native tensor-unit shift map in its published
presentation. These three isomorphisms have exactly the displayed endpoints;
their composite gives existence. Each heterogeneous equality fixes its factor,
so every chart satisfying the normalization equals that same composite. -/
theorem existsUnique_finiteReductionFixedChart (P : PurityFiniteSetting.{u})
    (X : Scheme.{u}) [X.Over (Spec (.of P.field.k))]
    (d : ℕ) (ζ : P.field.k) (hζ : IsPrimitiveRoot ζ P.diagonalExponent)
    (M : _root_.DerivedCategory
      (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} P.Coefficient))) :
    ∃! a : (P.compositionTwistShift X d).obj M ≅ M⟦2 * (d : ℤ)⟧,
      P.FiniteReductionFixedChartNormalized X d ζ hζ M a := by
  sorry

/-- The unique fixed-scalar root chart, before intrinsic realization.
Source: blueprint reduction Step 1
(blueprint: def-pur-finite-reduction-root-charts). -/
def finiteReductionFixedChart (P : PurityFiniteSetting.{u})
    (X : Scheme.{u}) [X.Over (Spec (.of P.field.k))]
    (d : ℕ) (ζ : P.field.k) (hζ : IsPrimitiveRoot ζ P.diagonalExponent)
    (M : _root_.DerivedCategory
      (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} P.Coefficient))) :
    (P.compositionTwistShift X d).obj M ≅ M⟦2 * (d : ℤ)⟧ :=
  (P.existsUnique_finiteReductionFixedChart X d ζ hζ M).choose

/-- The canonical source chart, transported through the actual realization and its shift.
Source: blueprint reduction Step 1
(blueprint: def-pur-finite-reduction-root-charts). -/
def finiteReductionSourceTrivialization (P : PurityFiniteSetting.{u})
    {X Y : Scheme.{u}} [X.Over (Spec (.of P.field.k))]
    (f : X ⟶ Y) (d : ℕ) (ζ : P.field.k)
    (hζ : IsPrimitiveRoot ζ P.diagonalExponent)
    (K : Scheme.proEtaleDerivedCategory Y P.Ring) :
    (P.compositionShiftedPullback f d).obj K ≅
      ((P.finiteReductionPullback f).obj K)⟦2 * (d : ℤ)⟧ :=
  letI := Scheme.sfIntrinsicModuleEquivalence_functor_additive P.Ring X
  let M := (P.smoothPurityPullback f).obj
    ((Scheme.sfIntrinsicDerivedEquivalence Y P.Ring).inverse.obj K)
  let E := (Scheme.sfIntrinsicModuleEquivalence X P.Ring).functor.mapDerivedCategory
  E.mapIso (P.finiteReductionFixedChart X d ζ hζ M) ≪≫
    (E.commShiftIso (2 * (d : ℤ))).app M

end WeilConjectures.PurityFiniteSetting
