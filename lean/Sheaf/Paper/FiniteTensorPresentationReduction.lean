/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NX
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Braided
public import Sheaf.Paper.FiniteTensorFixedComparisons
public import Sheaf.Paper.FiniteTensorReductionData
public import Sheaf.Paper.FiniteTensorComparisonEquations
public import Sheaf.Paper.FiniteSignedTwistProducts
public import Sheaf.Paper.FiniteFirstRootChart
public import Sheaf.Paper.FinitePositiveRootCharts
public import Sheaf.Paper.FiniteRootTensorPresentation
public import Sheaf.Paper.FiniteTensorSignedReduction
public import Sheaf.Paper.PurityFiniteSetting
public import Sheaf.Paper.DerivedPullbackTensorHom
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Tensor
public import Sheaf.Paper.FiniteReductionRootCharts
public import Sheaf.Paper.FiniteReductionComparisons
public import Sheaf.Paper.IntrinsicCoefficientTwistsUnrestricted
public import Sheaf.Paper.FiniteCoefficientReductionFlatModel
public import Sheaf.SecSmoothPurity.SupportedEtaleTensorOrigin
public import Sheaf.Paper.SupportedCup
public import Sheaf.Paper.OrientationFiniteCoefficientTwists
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.Monoidal
public import WeilConjectures.SixFunctors.ProEtale.ScalarExtensionMonoidal


import Sheaf.Paper.FiniteTensorSymmetryCoherence
import Sheaf.Paper.FiniteTensorShiftCoherence
import Sheaf.Paper.FiniteTensorLineChartReduction
import Sheaf.Paper.FiniteTensorPullbackTensorReduction
import Sheaf.Paper.FiniteTensorPullbackCompositionReduction

/-! # Finite reduction of signed twists and tensor presentations

Source: main-20261015, thm-pur-finite-reduction-of-purity, proof Step 2;
Stacks Tags 07A4, 0FPT, 0FNH, 03EK and 03EM.
(blueprint: lem-pur-finite-tensor-presentation-reduction)

## Main declarations

- `finiteTensorStructuralCoherence`
- `finiteTensorTau_reduction`
- `finite_tensor_presentation_reduction`
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open AlgebraicGeometry.Scheme
open scoped TensorProduct
-- The native derived braiding is a definition, not a global instance.
attribute [local instance] _root_.DerivedCategory.braidedCategory'

namespace WeilConjectures.PurityFiniteSetting

/-- Scalar extension respects the native symmetry and simultaneous shift comparison.
Associativity and unit equations are fields of finiteTensorCore.
Source: blueprint proof Steps 2 and 6, Stacks 0FPT and 0FNH
(blueprint: lem-pur-finite-tensor-presentation-reduction).
Proof: on flat-term K-flat representatives the binary map distributes the quotient
scalar into the first tensor factor. Both symmetry routes multiply the same scalars
and carry the same Koszul sign. The shift routes agree degreewise since the ring
map preserves -1. Descend through K-flat localization; the native shift comparison
is defined by the same localization, for all integer shifts. -/
theorem finiteTensorStructuralCoherence (P : PurityFiniteSetting.{u}) (m : ℕ) (hm : 1 ≤ m)
    (hmn : m ≤ P.level) (T : Scheme.{u}) :
    (∀ U V, FiniteTensorSymmetrySquare
      (P.finiteTensorReduction m hm hmn T) (P.finiteTensorCore m hm hmn T) U V) ∧
    ∀ U V (a b : ℤ), FiniteTensorShiftSquare
      (P.finiteTensorReduction m hm hmn T) (P.finiteTensorScalarShift m hm hmn T)
      (P.finiteTensorCore m hm hmn T) U V a b
      (_root_.DerivedCategory.shiftTensorShiftIso _ U V a b)
      (_root_.DerivedCategory.shiftTensorShiftIso _
        ((P.finiteTensorReduction m hm hmn T).obj U)
        ((P.finiteTensorReduction m hm hmn T).obj V) a b) := by
  constructor
  · intro U V
    exact P.finiteTensorSymmetryCoherence m hm hmn T U V
  · intro U V a b
    exact P.finiteTensorShiftCoherence m hm hmn T U V a b

/-- Signed addition commutes with the normalized reduction of the actual lines.
Source: blueprint proof Step 5
(blueprint: lem-pur-finite-tensor-presentation-reduction).
Proof: reduce a coherent local basis of the integral-reduced first line. Its signed
powers reduce to their corresponding signed powers, and dual evaluation commutes
with reduction. The product equations agree on these bases and therefore as sheaf
maps. The normalized single-complex and K-flat comparisons give the displayed
derived equality. Tensoring with any L preserves this equality by functoriality. -/
theorem finiteTensorTwistAdditionCoherence (P : PurityFiniteSetting.{u}) (m : ℕ) (hm : 1 ≤ m)
    (hmn : m ≤ P.level) (T : Scheme.{u}) [T.Over (Spec (.of P.field.k))] (r t : ℤ) :
    (P.finiteTensorReduction m hm hmn T).map (P.finiteTensorProduct T r t).hom ≫
        (P.finiteTensorLineComparison m hm hmn T (r + t)).hom =
      ((P.finiteTensorCore m hm hmn T).μIso
        (P.finiteTensorFixedLine T r) (P.finiteTensorFixedLine T t)).inv ≫
        ((P.finiteTensorLineComparison m hm hmn T r).hom ⊗ₘ
          (P.finiteTensorLineComparison m hm hmn T t).hom) ≫
        ((P.finiteReductionSetting m hm).finiteTensorProduct T r t).hom := by
  sorry

/-- The recorded scalar mate respects tensor pullback and the exact-derived compositor.
Source: blueprint proof Step 7; Stacks 07A4
(blueprint: lem-pur-finite-tensor-presentation-reduction).
Proof: on K-flat cochains both pullback/scalar routes send a pulled-back section
tensor b to its inverse image tensor b. The ordinary tensor and composition
constraints are those of inverse image, and both composites use the same scalar
unit. Their representative equations descend through localization. The displayed
maps are exactly those adjuncts by the realization unit and counit identities. -/
theorem finiteTensorPullbackCoherence (P : PurityFiniteSetting.{u}) (m : ℕ) (hm : 1 ≤ m)
    (hmn : m ≤ P.level) {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (∀ K L,
      (P.finiteTensorReduction m hm hmn X).map
          (P.finiteTensorPullbackTensor f K L).hom ≫
        ((P.finiteTensorCore m hm hmn X).μIso
          ((P.smoothPurityPullback f).obj K) ((P.smoothPurityPullback f).obj L)).inv ≫
        ((P.finiteTensorPullbackComparison m hm hmn f K).hom ⊗ₘ
          (P.finiteTensorPullbackComparison m hm hmn f L).hom) =
      (P.finiteTensorPullbackComparison m hm hmn f (K ⊗ L)).hom ≫
        ((P.finiteReductionSetting m hm).smoothPurityPullback f).map
          ((P.finiteTensorCore m hm hmn Y).μIso K L).inv ≫
        ((P.finiteReductionSetting m hm).finiteTensorPullbackTensor f
          ((P.finiteTensorReduction m hm hmn Y).obj K)
          ((P.finiteTensorReduction m hm hmn Y).obj L)).hom) ∧
    ∀ K,
      (P.finiteTensorReduction m hm hmn X).map
          ((compositionFixedPullbackComp P.Ring f g).hom.app K) ≫
        (P.finiteTensorPullbackComparison m hm hmn f ((P.smoothPurityPullback g).obj K)).hom ≫
        ((P.finiteReductionSetting m hm).smoothPurityPullback f).map
          (P.finiteTensorPullbackComparison m hm hmn g K).hom =
      (P.finiteTensorPullbackComparison m hm hmn (f ≫ g) K).hom ≫
        (compositionFixedPullbackComp (P.finiteReductionSetting m hm).Ring f g).hom.app
          ((P.finiteTensorReduction m hm hmn Z).obj K) := by
  constructor
  · exact P.finiteTensorPullbackTensorReduction m hm hmn f
  · exact P.finiteTensorPullbackCompositionReduction m hm hmn f g

private theorem presentation_chart_reduction
    {C : Type*} [Category* C] [HasShift C ℤ]
    {D : Type*} [Category* D] [HasShift D ℤ]
    (F : C ⥤ D) (s : ℤ)
    (σ : shiftFunctor C s ⋙ F ≅ F ⋙ shiftFunctor D s)
    {A U Z : C} {B V Z' : D}
    (u : F.obj U ⟶ V) (b : F.obj A ≅ B) (a : A ≅ U) (a' : B ≅ V)
    (p : Z ≅ A⟦s⟧) (p' : Z' ≅ B⟦s⟧)
    (c : Z ≅ U⟦s⟧) (c' : Z' ≅ V⟦s⟧)
    (hp : p = c ≪≫ (shiftFunctor C s).mapIso a.symm)
    (hp' : p' = c' ≪≫ (shiftFunctor D s).mapIso a'.symm)
    (hc : b.hom ≫ a'.hom = F.map a.hom ≫ u) :
    (F.mapIso p ≪≫ σ.app A ≪≫ (shiftFunctor D s).mapIso b ≪≫ p'.symm).hom ≫
      c'.hom = F.map c.hom ≫ σ.hom.app U ≫ u⟦s⟧' := by
  subst p
  subst p'
  simp only [Iso.trans_hom, Iso.trans_inv, Functor.mapIso_hom,
    Functor.mapIso_inv, Iso.symm_hom, Iso.symm_inv, Iso.app_hom,
    Functor.map_comp, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have hn := σ.hom.naturality a.inv
  change F.map (a.inv⟦s⟧') ≫ σ.hom.app A =
    σ.hom.app U ≫ (F.map a.inv)⟦s⟧' at hn
  rw [reassoc_of% hn]
  have hk : F.map a.inv ≫ b.hom ≫ a'.hom = u := by
    rw [hc]
    simp only [← F.map_comp_assoc, Iso.inv_hom_id, F.map_id, Category.id_comp]
  simpa only [Functor.map_comp, Category.assoc] using
    congrArg (fun f ↦ F.map c.hom ≫ σ.hom.app U ≫ f⟦s⟧') hk


/-- The positive reduction constructed from the signed lines has the prescribed
compatible-root normalization. No level is required to be divisible by ramification.
Source: blueprint proof Step 8
(blueprint: lem-pur-finite-tensor-presentation-reduction).
Proof: lift a primitive root to a compatible infinite root sequence. Its integral
basis reduces to the specified finite root bases, and the balancing map takes
the A basis to the B basis. Recurse on ordered powers and use the same shift signs.
Changing the lift fixes these finite bases. The zero stage is the scalar unit.
The root transition is the indicated power map at every positive quotient level. -/
theorem finiteTensorPositiveReduction_chart (P : PurityFiniteSetting.{u}) (m : ℕ)
    (hm : 1 ≤ m) (hmn : m ≤ P.level) (T : Scheme.{u})
    [T.Over (Spec (.of P.field.k))] (d : ℕ)
    (ζ η : P.field.k) (hζ : IsPrimitiveRoot ζ P.diagonalExponent)
    (hη : IsPrimitiveRoot η (P.finiteReductionSetting m hm).diagonalExponent)
    (hroot : η = ζ ^ (P.coefficients.l ^ (P.level - m))) :
    (P.finiteTensorPositiveReduction m hm hmn T d).hom ≫
        ((P.finiteReductionSetting m hm).finiteTensorDiagonalChart T d η hη).hom =
      (P.finiteTensorReduction m hm hmn T).map
          (P.finiteTensorDiagonalChart T d ζ hζ).hom ≫
        (P.finiteTensorScalarShift m hm hmn T (2 * (d : ℤ))).hom.app _ ≫
        ((P.finiteTensorCore m hm hmn T).εIso.inv)⟦2 * (d : ℤ)⟧' := by
  have hs := (P.existsUnique_finiteTensorPositivePresentation T d).exists.choose_spec ζ hζ
  have ht := ((P.finiteReductionSetting m hm).existsUnique_finiteTensorPositivePresentation
    T d).exists.choose_spec η hη
  have hc := P.finiteTensorLineChart_reduction m hm hmn T d ζ hζ η hη hroot
  have hi := presentation_chart_reduction (P.finiteTensorReduction m hm hmn T)
    (2 * (d : ℤ)) (P.finiteTensorScalarShift m hm hmn T (2 * (d : ℤ)))
    (P.finiteTensorCore m hm hmn T).εIso.inv
    (P.finiteTensorLineComparison m hm hmn T d)
    (P.finiteTensorPositiveChart T ζ hζ d)
    ((P.finiteReductionSetting m hm).finiteTensorPositiveChart T η hη d)
    (P.finiteTensorPositivePresentation T d)
    ((P.finiteReductionSetting m hm).finiteTensorPositivePresentation T d)
    (P.finiteTensorDiagonalChart T d ζ hζ)
    ((P.finiteReductionSetting m hm).finiteTensorDiagonalChart T d η hη)
    (eq_of_heq hs) (eq_of_heq ht) hc
  simpa only [finiteTensorPositiveReduction] using hi

/-- The exact inverse second-factor tensor-shift comparison on the actual signed line.
Source: blueprint proof Step 9, Stacks 0FNH
(blueprint: lem-pur-finite-tensor-presentation-reduction). -/
@[irreducible] def finiteTensorTau (P : PurityFiniteSetting.{u}) (T : Scheme.{u})
    (M : _root_.DerivedCategory (Sheaf (ProEt.topology T) (ModuleCat.{u + 1} P.Coefficient)))
    (d : ℕ) :=
  (((curriedTensor _).obj M).commShiftIso (2 * (d : ℤ))).symm.app
    (P.finiteTensorFixedLine T d)

/-- Reduction commutes with this precise reassociation of every signed-line presentation.
Source: blueprint proof Steps 6 and 9, Stacks 07A4 and 0FNH
(blueprint: lem-pur-finite-tensor-presentation-reduction).
Proof: the native second-factor shift acts on a homogeneous tensor with the sign
(-1)^(2dp). Scalar reduction preserves that sign and the normalized binary map.
Apply the shift equation and then naturality in the line map. This proves the
square before localization on all K-flat representatives, hence in the derived category. -/
theorem finiteTensorTau_reduction (P : PurityFiniteSetting.{u}) (m : ℕ)
    (hm : 1 ≤ m) (hmn : m ≤ P.level) (T : Scheme.{u})
    [T.Over (Spec (.of P.field.k))]
    (M : _root_.DerivedCategory (Sheaf (ProEt.topology T) (ModuleCat.{u + 1} P.Coefficient)))
    (d : ℕ) :
    (P.finiteTensorReduction m hm hmn T).map (P.finiteTensorTau T M d).hom ≫
      ((P.finiteTensorCore m hm hmn T).μIso M
        ((P.finiteTensorFixedLine T d)⟦2 * (d : ℤ)⟧)).inv ≫
      (𝟙 _ ⊗ₘ
        ((P.finiteTensorScalarShift m hm hmn T (2 * (d : ℤ))).hom.app
            (P.finiteTensorFixedLine T d) ≫
          ((P.finiteTensorLineComparison m hm hmn T d).hom)⟦2 * (d : ℤ)⟧')) =
    (P.finiteTensorTwistShiftComparison m hm hmn T d (2 * (d : ℤ))).hom.app M ≫
      ((P.finiteReductionSetting m hm).finiteTensorTau T
        ((P.finiteTensorReduction m hm hmn T).obj M) d).hom := by
  sorry

/-- Finite reduction identifies the canonical purity reassociation through precisely
its recorded pullback, tensor, twist and shift comparisons.
Source: main-20261015, thm-pur-finite-reduction-of-purity, proof Step 2
(blueprint: lem-pur-finite-tensor-presentation-reduction).
Proof: first reduce on flat-term K-flat representatives, retaining the target
B-action and the original Tor interval. The scalar-first binary comparison
respects associators, units and signed symmetry by the cochain comparison equations.
The actual integral-reduced degree-one line reduces by balanced association;
positive powers follow by recursion and negative powers by dual evaluation.
The native scalar shift and second-variable tensor shift have the same cochain
sign before and after reduction. Pullback uses the recorded scalar-adjunction mate,
whose tensor and compositor equations follow on those same representatives.
In compatible primitive-root charts the actual positive line comparison is the
specified finite root transition. Hence the signed-line reassociation square is
also the square in the published purity presentation. The source comparison is
uniquely fixed by precisely these charts, so its transported version is the map
on the right. Naturality with the pullback mate gives the displayed square.
For d=0 use the unit and shift-zero equations; no coefficient flatness or
ramification-index divisibility enters any step. -/
theorem finite_tensor_presentation_reduction (P : PurityFiniteSetting.{u}) (m : ℕ)
    (hm : 1 ≤ m) (hmn : m ≤ P.level) {X Y : Scheme.{u}}
    [X.Over (Spec (.of P.field.k))] [Y.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
    [QuasiCompact (X ↘ Spec (.of P.field.k))] [IsSeparated (X ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y ↘ Spec (.of P.field.k))] [IsSeparated (Y ↘ Spec (.of P.field.k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of P.field.k))] [IsSeparated f]
    (d : ℕ) [SmoothOfRelativeDimension d f]
    (K : _root_.DerivedCategory (Sheaf (ProEt.topology Y) (ModuleCat.{u + 1} P.Coefficient)))
    (hK : finiteTorConstructible P.coefficients.l P.extension P.level P.level_pos Y
      ((sfIntrinsicDerivedEquivalence Y P.Ring).functor.obj K)) :
    (P.finiteTensorReduction m hm hmn X).map
        (P.smoothPurityReassociation X d ((P.smoothPurityPullback f).obj K)).hom ≫
      (P.finiteTensorPurityTargetComparison m hm hmn f d K).hom =
    (P.finiteTensorPuritySourceComparison m hm hmn f d K).hom ≫
      ((P.finiteReductionSetting m hm).smoothPurityReassociation X d
        (((P.finiteReductionSetting m hm).smoothPurityPullback f).obj
          ((P.finiteTensorReduction m hm hmn Y).obj K))).hom := by
  sorry

end WeilConjectures.PurityFiniteSetting
