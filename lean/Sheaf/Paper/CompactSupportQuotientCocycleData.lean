/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.CompactSupportCoefficientPresentation
public import Sheaf.Paper.CompactSupportReductionTower
public import Sheaf.Paper.CompletedIntegralConstantMapOfUniverses
public import Sheaf.AlgebraicGeometry.ProEtaleOpenScalarRestrictionCoherence
public import Sheaf.Algebra.Homology.SheafRingDerivedCoefficientAdjunction
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite

/-! # Unit and cocycle for compact-support coefficient quotients

Source: the current blueprint, lem-coef-integral-compact-support.proof.md,
finite-level coefficient comparison; Stacks Tags 03EK, 06YS, 06YY and 07A6
(blueprint: lem-coef-compact-support-quotient-coordinates).

Index n denotes exponent n+1, so every positive coefficient exponent is included.
All reduction maps are the published normalized adjuncts of the actual quotient maps.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
-- Keep distinct quotient levels from unfolding their valuation-theoretic ideal data.
attribute [local irreducible] Padic.coefficientExtensionIdeal
  HasDerivedCategory.standard SheafOfModules.monoidalCategory
  WeilConjectures.completedIntegralCommRingSheafUnrestricted

universe u v
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- Equal-level quotients are identity maps.
Source: Stacks Tag 03EK; blueprint coefficient maps
(blueprint: lem-coef-compact-support-quotient-coordinates).
Proof: the quotient factor induced by the identity sends each residue class to itself. -/
theorem compactSupportQuotient_self (n : ℕ) :
    compactSupportLevelQuotient l E n n le_rfl = RingHom.id _ := by
  exact Ideal.Quotient.factor_eq

/-- Direct and successive quotient factors coincide.
Source: Stacks Tag 03EK; blueprint coefficient maps
(blueprint: lem-coef-compact-support-quotient-coordinates).
Proof: both homomorphisms send the class of a to the class of a in the final quotient. -/
theorem compactSupportQuotient_comp (r m n : ℕ) (hrm : m ≤ r) (hmn : n ≤ m) :
    (compactSupportLevelQuotient l E m n hmn).comp
        (compactSupportLevelQuotient l E r m hrm) =
      compactSupportLevelQuotient l E r n (hmn.trans hrm) := by
  unfold compactSupportLevelQuotient
  exact Ideal.Quotient.factor_comp
    (by unfold Padic.coefficientExtensionIdeal
        exact Ideal.pow_le_pow_right (Nat.add_le_add_right hrm 1))
    (by unfold Padic.coefficientExtensionIdeal
        exact Ideal.pow_le_pow_right (Nat.add_le_add_right hmn 1))

/-- The identity restriction identification, including the equal-level quotient cast.
Source: Stacks Tag 03DA; blueprint identity convention
(blueprint: lem-coef-compact-support-quotient-coordinates). -/
def compactSupportQuotientResId (W : Scheme.{u}) (n : ℕ) :
    (proEtaleCoefficientRestrictScalars W
      (compactSupportLevelQuotient l E n n le_rfl)).mapDerivedCategory ≅ 𝟭 _ :=
  compactSupportCoefficientResId W (Padic.coefficientExtensionRing l E (n + 1))
    (compactSupportLevelQuotient l E n n le_rfl) (compactSupportQuotient_self l E n)

/-- The canonical composition identification for all three quotient levels.
Source: Stacks Tag 03DA; blueprint restriction composition convention
(blueprint: lem-coef-compact-support-quotient-coordinates). -/
def compactSupportQuotientResComp (W : Scheme.{u})
    (r m n : ℕ) (hrm : m ≤ r) (hmn : n ≤ m) :
    (proEtaleCoefficientRestrictScalars W
        (compactSupportLevelQuotient l E m n hmn)).mapDerivedCategory ⋙
      (proEtaleCoefficientRestrictScalars W
        (compactSupportLevelQuotient l E r m hrm)).mapDerivedCategory ≅
      (proEtaleCoefficientRestrictScalars W
        (compactSupportLevelQuotient l E r n (hmn.trans hrm))).mapDerivedCategory :=
  compactSupportCoefficientResComp W
    (compactSupportLevelQuotient l E r m hrm)
    (compactSupportLevelQuotient l E m n hmn)
    (compactSupportLevelQuotient l E r n (hmn.trans hrm))
    (compactSupportQuotient_comp l E r m n hrm hmn)

/-- Termwise ordinary reduction on complexes, retaining its finite coefficient action.
Source: Stacks Tag 06YY; blueprint P tensor B_n
(blueprint: lem-coef-compact-support-quotient-coordinates). -/
def compactSupportQuotientComplex (W : Scheme.{u}) (n : ℕ) :
    CochainComplex (scalarReductionSource.{u, u} l E W) ℤ ⥤
      CochainComplex (scalarReductionTarget.{u, u} l E W n) ℤ :=
  letI := scalarReductionExtensionAdditive.{u, u} l E W n
  (scalarReductionExtension.{u, u} l E W n).mapHomologicalComplex (.up ℤ)

/-- A sheafified pure tensor s tensor x in the published ordinary integral reduction.
The ordinary adjunction unit is x maps to 1 tensor x; scalar multiplication supplies s.
Source: Stacks Tags 03EK and 07A6; blueprint tensor convention
(blueprint: lem-coef-compact-support-quotient-coordinates). -/
def compactSupportQuotientTensor (W : Scheme.{u}) (n : ℕ)
    (M : scalarReductionSource.{u, u} l E W) (U : W.ProEtᵒᵖ)
    (s : (integralCoefficientCommRingSheaf.{u, u} l E W n).obj.obj U) (x : M.val.obj U) :
    ((scalarReductionExtension.{u, u} l E W n).obj M).val.obj U :=
  s • @id (((scalarReductionExtension.{u, u} l E W n).obj M).val.obj U)
    ((((scalarReductionExtension_adjunction.{u, u} l E W n).choose).unit.app M).val.app U x)

/-- The canonical cochain computation map induced by the universal derived counit.
Source: Stacks Tag 06YY; blueprint resolution identifications
(blueprint: lem-coef-compact-support-quotient-coordinates). -/
def compactSupportQuotientComputation (W : Scheme.{u}) (n : ℕ)
    (P : CochainComplex (scalarReductionSource.{u, u} l E W) ℤ) :
    (scalarReductionDerivedExtension.{u, u} l E W n).obj (DerivedCategory.Q.obj P) ⟶
      DerivedCategory.Q.obj ((compactSupportQuotientComplex l E W n).obj P) :=
  letI := scalarReductionExtensionAdditive.{u, u} l E W n
  (scalarReductionDerivedExtension.{u, u} l E W n).map
      ((DerivedCategory.quotientCompQhIso _).inv.app P) ≫
    (scalarReductionCounit.{u, u} l E W n).app ((HomotopyCategory.quotient _ _).obj P) ≫
    DerivedCategory.Qh.map
      (((scalarReductionExtension.{u, u} l E W n).mapHomotopyCategoryFactors (.up ℤ)).hom.app P) ≫
    (DerivedCategory.quotientCompQhIso _).hom.app
      ((compactSupportQuotientComplex l E W n).obj P)

/-- A quotient formula for section functions, with all carriers abstract.
Source: the ordinary tensor quotient formula, Stacks Tag 03EK
(blueprint: lem-coef-compact-support-quotient-coordinates). -/
abbrev QuotientSectionFormula {S T X Y : Type*} {Z Z' : Type v}
    (q : S → T) (pm : S → X → Y) (pn : T → X → Z) (a : Y → Z') : Prop :=
  ∀ (s : S) (x : X), HEq (a (pm s x)) (pn (q s) x)

/-- The balancing formula for section functions, with all carriers abstract.
Source: ordinary tensor associativity, Stacks Tag 03EK
(blueprint: lem-coef-compact-support-quotient-coordinates). -/
abbrev BalancingSectionFormula {S T X Y Z H : Type*} [Mul T]
    (q : S → T) (pm : S → X → Y) (pn : T → X → Z)
    (tensor : T → Y → H) (b : H → Z) : Prop :=
  ∀ (s : S) (t : T) (x : X), b (tensor t (pm s x)) = pn (t * q s) x

/-- The quotient and balancing formulas for a single module. Separating the module
formula from its cochain indexing avoids normalizing the derived functor's chosen
construction when checking section types. The HEq clauses below identify these very
morphisms with the components of the chain maps, with no change in their actions.
Source: Stacks Tag 03EK; blueprint input quotient and balancing formulas
(blueprint: lem-coef-compact-support-quotient-coordinates). -/
def CompactSupportQuotientModuleSpec (W : Scheme.{u}) (m n : ℕ) (h : n ≤ m)
    (M : scalarReductionSource.{u, u} l E W)
    (Mm : scalarReductionTarget.{u, u} l E W m)
    (Mn : scalarReductionTarget.{u, u} l E W n)
    (em : (scalarReductionExtension.{u, u} l E W m).obj M ≅ Mm)
    (en : (scalarReductionExtension.{u, u} l E W n).obj M ≅ Mn)
    (a : Mm ⟶ (proEtaleCoefficientRestrictScalars W
      (compactSupportLevelQuotient l E m n h)).obj Mn)
    (b : (pbcExtend (compactSupportLevelSheafQuotient l E W m n h)).obj Mm ⟶ Mn) : Prop :=
  (∀ U : W.ProEtᵒᵖ, QuotientSectionFormula
    (fun s ↦ (compactSupportLevelSheafQuotient l E W m n h).hom.app U s)
    (fun s x ↦ em.hom.val.app U (compactSupportQuotientTensor l E W m M U s x))
    (fun t x ↦ en.hom.val.app U (compactSupportQuotientTensor l E W n M U t x))
    (fun y ↦ a.val.app U y)) ∧
  (∀ U : W.ProEtᵒᵖ, BalancingSectionFormula
    (fun s ↦ (compactSupportLevelSheafQuotient l E W m n h).hom.app U s)
    (fun s x ↦ em.hom.val.app U (compactSupportQuotientTensor l E W m M U s x))
    (fun t x ↦ en.hom.val.app U (compactSupportQuotientTensor l E W n M U t x))
    (pbcTensorSection (compactSupportLevelSheafQuotient l E W m n h) Mm U)
    (fun y ↦ b.val.app U y))

end WeilConjectures
