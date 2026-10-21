/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NJ
-/
module

public import Sheaf.Paper.IntrinsicCompletionCompleted
public import Sheaf.Paper.PrincipalKoszulStrictReplacement
public import Sheaf.CategoryTheory.StrictRoosModel
public import Sheaf.Paper.DerivedCompleteOnSlices
public import Mathlib.Algebra.Homology.Monoidal
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses

/-! # Principal intrinsic completion with independent coefficient universes

Source: Stacks Project, Tags 099M and 0A0E; the explicit fiber in blueprint order 1247
(blueprint: def-a1-principal-intrinsic-completion).
This specializes the published fiber construction to the actual principal Koszul tower
of the completed local-field coefficients, without identifying coefficient and site sizes.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe t u
open CategoryTheory CategoryTheory.Limits Opposite
namespace WeilConjectures.PrincipalIntrinsicCompletion
open PrincipalKoszulStrictReplacement

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (W : AlgebraicGeometry.Scheme.{t})

/-- The existing principal Koszul tower, assembled degreewise.
Source: Stacks 099M (blueprint: def-a1-principal-intrinsic-completion). -/
abbrev tower (P : CochainComplex (Modules l E W) ℤ) :=
  koszulTowerComplex (completedIntegralCommRingSheafUnrestricted l E W) (sourceTower l E W P)

/-- The explicit intrinsic fiber, with coordinates (x,y) and differential (dx,(1-s)x-dy).
Source: Stacks 0A0E; blueprint order 1247
(blueprint: def-a1-principal-intrinsic-completion). -/
def fiber (P : CochainComplex (Modules l E W) ℤ) :=
  CochainComplex.mappingCocone (-roosU (tower l E W P))

/-- The total-tensor unit is the standard right unitor, without any choice of a map.
Source: Stacks 03EK (blueprint: def-a1-principal-intrinsic-completion). -/
def tensorUnit (P : CochainComplex (Modules l E W) ℤ) :
    (tensorWith l E W P).obj
      ((CochainComplex.singleFunctor (Modules l E W) 0).obj
        (SheafOfModules.unit (completedIntegralCoefficientSheafUnrestricted l E W))) ≅ P :=
  letI : MonoidalCategory (Modules l E W) := SheafOfModules.KFlatTotalTensorModel.monoidal
    (completedIntegralCommRingSheafUnrestricted l E W)
  letI : MonoidalPreadditive (Modules l E W) := SheafOfModules.cochainModulesPreadditive
    (completedIntegralCommRingSheafUnrestricted l E W)
  HomologicalComplex.rightUnitor P

/-- Degree-zero Koszul tensor inclusion, in the specified order P tensor Q_n.
Source: Stacks 099M (blueprint: def-a1-principal-intrinsic-completion). -/
def levelUnit (P : CochainComplex (Modules l E W) ℤ) (n : ℕ) :
    P ⟶ (sourceTower l E W P).obj (op n) :=
  (tensorUnit l E W P).inv ≫ (tensorWith l E W P).map
    (CochainComplex.mappingCone.inr
      ((CochainComplex.singleFunctor (Modules l E W) 0).map (multiplication l E W n)))

/-- The intrinsic unit is the unique map with product component the actual Koszul
units and zero shifted component. This is a predicate fixing a map, not extra data.
Source: Stacks 0A0E; blueprint order 1247
(blueprint: def-a1-principal-intrinsic-completion). -/
def UnitFormula (P : CochainComplex (Modules l E W) ℤ) (η : P ⟶ fiber l E W P) : Prop :=
  η ≫ CochainComplex.mappingCocone.fst (-roosU (tower l E W P)) =
      Pi.lift (levelUnit l E W P) ∧
    ∀ q : ℤ, η.f (q + 1) ≫
      (CochainComplex.mappingCocone.snd (-roosU (tower l E W P))).v
        (q + 1) q (add_neg_cancel_right q 1) = 0

end WeilConjectures.PrincipalIntrinsicCompletion
