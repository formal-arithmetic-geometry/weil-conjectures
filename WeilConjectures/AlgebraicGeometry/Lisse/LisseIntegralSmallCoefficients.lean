/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Lisse.LisseAdicSheaves

/-! # Lisse integral systems with small coefficient fields

Source: Deligne, Weil II (1.1.1) b)-d); Bhatt--Scholze, Proposition 6.8.4(1)
(blueprint: def-pod-lisse-l-adic-sheaves).
The published categories and operations remain reexported. This is their integral-system
criterion for the canonical small finite fields, with the original module-size convention.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme

/-- Grothendieck abelian structure transported through the canonical coefficient lift.
Source: Weil II coefficient-size convention (blueprint: def-pod-lisse-l-adic-sheaves). -/
instance smallCoefficientModuleGrothendieck (R : Type u) [CommRing R] :
    IsGrothendieckAbelian.{u + 1} (ModuleCat.{u + 1} R) :=
  IsGrothendieckAbelian.of_equivalence
    (ModuleCat.restrictScalarsEquivalenceOfRingEquiv
      (ULift.ringEquiv : ULift.{u + 1} R ≃+* R)).symm

/-- The same inverse system, with coefficients allowed to have a smaller universe.
Source: Weil II (1.1.1) b) (blueprint: def-pod-lisse-l-adic-sheaves). -/
abbrev AdicIntegralDiagramOfUniverses (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (Y : Scheme.{u}) :=
  ℕᵒᵖ ⥤ Sheaf Y.smallEtaleTopology
    (ModuleCat.{u + 1} (Padic.coefficientExtensionIntegers l E))

/-- Finite local constancy, annihilation, and the stalk quotient condition, exactly as in
`IsLisseIntegralDiagram`, without requiring the coefficient field to have size u+1.
Source: Weil II (1.1.1) b), Bhatt--Scholze 6.8.4(1)
(blueprint: def-pod-lisse-l-adic-sheaves). -/
def IsLisseIntegralDiagramOfUniverses (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (Y : Scheme.{u}) (F : AdicIntegralDiagramOfUniverses l E Y) : Prop :=
  (∀ n : ℕ, IsFiniteLocallyConstantSheaf (F.obj (op n))) ∧
  (∀ (n : ℕ) (U : Y.Etale),
    Padic.coefficientExtensionIdeal l E (n + 1) •
      (⊤ : Submodule (Padic.coefficientExtensionIntegers l E)
        ((F.obj (op n)).obj.obj (op U))) = ⊥) ∧
  ∀ (κ : Type u) [Field κ] [IsAlgClosed κ] (x : Spec (.of κ) ⟶ Y) (n : ℕ),
    Function.Surjective
      ((((pointSmallEtale x).ulift.{u + 1}.sheafFiber
        (A := ModuleCat.{u + 1} (Padic.coefficientExtensionIntegers l E))).map
        (F.map (homOfLE (Nat.le_succ n)).op)).hom) ∧
    LinearMap.ker
      ((((pointSmallEtale x).ulift.{u + 1}.sheafFiber
        (A := ModuleCat.{u + 1} (Padic.coefficientExtensionIntegers l E))).map
        (F.map (homOfLE (Nat.le_succ n)).op)).hom) =
      Padic.coefficientExtensionIdeal l E (n + 1) •
        (⊤ : Submodule (Padic.coefficientExtensionIntegers l E)
          (((pointSmallEtale x).ulift.{u + 1}.sheafFiber
        (A := ModuleCat.{u + 1} (Padic.coefficientExtensionIntegers l E))).obj
            (F.obj (op (n + 1)))))

/-- The original full-subcategory construction for canonical small coefficient fields.
Morphisms remain natural transformations of exactly these inverse systems.
Source: Weil II (1.1.1) b) (blueprint: def-pod-lisse-l-adic-sheaves). -/
abbrev LisseIntegralSheafOfUniverses (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (Y : Scheme.{u}) [IsNoetherian Y] [Y.IsSeparated]
    [∀ x : Y, Invertible (l : Y.residueField x)] :=
  ObjectProperty.FullSubcategory (IsLisseIntegralDiagramOfUniverses l E Y)

/-- The integral fibre of the displayed system, with the unchanged inverse-limit definition.
Source: Weil II (1.1.1) b) (blueprint: def-pod-lisse-l-adic-sheaves). -/
def adicIntegralFiberOfUniverses (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (Y : Scheme.{u}) (F : AdicIntegralDiagramOfUniverses l E Y)
    (κ : Type u) [Field κ] [IsAlgClosed κ] (x : Spec (.of κ) ⟶ Y) :
    ModuleCat.{u + 1} (Padic.coefficientExtensionIntegers l E) :=
  limit (F ⋙ (pointSmallEtale x).ulift.{u + 1}.sheafFiber
        (A := ModuleCat.{u + 1} (Padic.coefficientExtensionIntegers l E)))

end AlgebraicGeometry.Scheme
