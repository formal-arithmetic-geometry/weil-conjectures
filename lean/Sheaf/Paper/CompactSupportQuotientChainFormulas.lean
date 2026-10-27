/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.CompactSupportQuotientCocycleData
import Sheaf.Paper.CompactSupportQuotientModuleMaps

/-! # Chain-level quotient and balancing maps

Source: blueprint coefficient quotient proof, Steps 2 and 3; Stacks Tags 03EK and 06YY.
(blueprint: lem-coef-compact-support-quotient-chain-formulas).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [local irreducible] Padic.coefficientExtensionIdeal
  HasDerivedCategory.standard SheafOfModules.monoidalCategory
  WeilConjectures.completedIntegralCommRingSheafUnrestricted

attribute [local irreducible] WeilConjectures.scalarReductionExistence
  WeilConjectures.scalarReductionExtension

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- Concrete quotient chain maps with their section formulas.
Source: blueprint coefficient quotient proof, Steps 2--3; Stacks Tags 03EK and 06YY
(blueprint: lem-coef-compact-support-quotient-chain-formulas).
Proof: specialize the ordinary adjunction-composition construction to the completed
projection and the finite quotient. The projection composite is the final projection.
The normalized units are exactly the integral tensor sections. No K-flatness is needed. -/
theorem compactSupportQuotient_chain_formulas (W : Scheme.{u})
    (m n : ℕ) (h : n ≤ m)
    (P : CochainComplex (scalarReductionSource.{u, u} l E W) ℤ) :
    ∃ (a : (compactSupportQuotientComplex l E W m).obj P ⟶
        ((proEtaleCoefficientRestrictScalars W
          (compactSupportLevelQuotient l E m n h)).mapHomologicalComplex (.up ℤ)).obj
            ((compactSupportQuotientComplex l E W n).obj P))
      (b : ((pbcExtend.{u} (compactSupportLevelSheafQuotient l E W m n h)).mapHomologicalComplex
          (.up ℤ)).obj ((compactSupportQuotientComplex l E W m).obj P) ⟶
        (compactSupportQuotientComplex l E W n).obj P),
      (∀ (i : ℤ) (U : W.ProEtᵒᵖ)
        (s : (integralCoefficientCommRingSheaf.{u, u} l E W m).obj.obj U)
        (x : (P.X i).val.obj U),
        HEq ((a.f i).val.app U (compactSupportQuotientTensor l E W m (P.X i) U s x))
          (compactSupportQuotientTensor l E W n (P.X i) U
            ((compactSupportLevelSheafQuotient l E W m n h).hom.app U s) x)) ∧
      (∀ (i : ℤ) (U : W.ProEtᵒᵖ)
        (s : (integralCoefficientCommRingSheaf.{u, u} l E W m).obj.obj U)
        (t : (integralCoefficientCommRingSheaf.{u, u} l E W n).obj.obj U)
        (x : (P.X i).val.obj U),
        (b.f i).val.app U
          (pbcTensorSection (compactSupportLevelSheafQuotient l E W m n h)
            ((scalarReductionExtension.{u, u} l E W m).obj (P.X i)) U t
              (compactSupportQuotientTensor l E W m (P.X i) U s x)) =
          compactSupportQuotientTensor l E W n (P.X i) U
            (t * (compactSupportLevelSheafQuotient l E W m n h).hom.app U s) x) ∧
      IsIso b := by
  let α := compactSupportQuotientModuleMap l E W m n h
  let β := (compactSupportQuotientBalance l E W m n h).hom
  let a : (compactSupportQuotientComplex l E W m).obj P ⟶
      ((proEtaleCoefficientRestrictScalars W
        (compactSupportLevelQuotient l E m n h)).mapHomologicalComplex (.up ℤ)).obj
          ((compactSupportQuotientComplex l E W n).obj P) :=
    { f := fun i ↦ α.app (P.X i)
      comm' := fun i j _ ↦ (α.naturality (P.d i j)).symm }
  let b : ((pbcExtend
      (compactSupportLevelSheafQuotient l E W m n h)).mapHomologicalComplex (.up ℤ)).obj
      ((compactSupportQuotientComplex l E W m).obj P) ⟶
      (compactSupportQuotientComplex l E W n).obj P :=
    { f := fun i ↦ β.app (P.X i)
      comm' := fun i j _ ↦ (β.naturality (P.d i j)).symm }
  refine ⟨a, b, ?_, ?_, ?_⟩
  · intro i U s x
    exact compactSupportQuotientModuleMap_formula l E W m n h (P.X i) U s x
  · intro i U s t x
    exact compactSupportQuotientBalance_formula l E W m n h (P.X i) U s t x
  · have : ∀ i : ℤ, IsIso (b.f i) := fun i ↦ by
      change IsIso ((compactSupportQuotientBalance l E W m n h).hom.app (P.X i))
      infer_instance
    exact HomologicalComplex.Hom.isIso_of_components b

end WeilConjectures
