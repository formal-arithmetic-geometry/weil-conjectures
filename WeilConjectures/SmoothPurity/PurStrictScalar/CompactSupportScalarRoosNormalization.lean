/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurStrictScalar.CompactSupportScalarLimitFoundations
import WeilConjectures.CategoryTheory.Roos.RoosArithmeticNormalization

/-! # Arithmetic normalization for any unit-normalized support Roos comparison

Source: Stacks Tag 0941, the selection/block model for cofinal restriction.
(blueprint: lem-pur-compact-support-scalar-roos-normalization).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [-instance] WeilConjectures.SemilinearSections.moduleAbelian
attribute [-instance] WeilConjectures.SemilinearSections.abelianSheafify
  WeilConjectures.SemilinearSections.locallyBijective WeilConjectures.SemilinearSections.hasDerived
attribute [local irreducible] CategoryTheory.Functor.mapDerivedCategory
  CategoryTheory.Functor.rightDerivedFunctor
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme hiding Modules
open AlgebraicGeometry.ProEtale.StrictTower
namespace WeilConjectures.PurStrictScalar
variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
attribute [local irreducible] scalarRoosRestriction

/-- Arithmetic restriction is the selection/block map under every unit-normalized
Roos presentation, and preserves all compatible strict augmentations.
Source: Stacks Tag 0941; the arithmetic restriction normalization.
(blueprint: lem-pur-compact-support-scalar-roos-normalization).
Proof: the chosen cofinality map is a quasi-isomorphism with the specified
selection/block coordinates. Apply roosArithmeticNormalization to its coordinates
and the supplied unit equation to identify its derived map with scalarLimitRestriction.
A compatible family remains compatible after selection, by composition along the
original tower. Its augmentation has zero shifted-product coordinate, so the same
normalization theorem identifies the restricted augmentation with the selected
family's augmentation. This includes e=1 and the first positive coefficient level. -/
theorem scalarRoosNormalization_of_unit (W : Scheme.{u})
    (κ : roosF (A := Modules
      (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) W) ⋙
        DerivedCategory.Q ≅ DerivedCategory.Q ⋙ scalarLimit l E W)
    (hk : ∀ K : CochainComplex (Towers
        (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) W) ℤ,
      DerivedCategory.Q.map (roosι K) ≫ κ.hom.app K =
        DerivedCategory.Q.map
          (limit.isoLimitCone ⟨HomologicalComplex.coneOfHasLimitEval K.asFunctor,
            HomologicalComplex.isLimitConeOfHasLimitEval K.asFunctor⟩).hom ≫
        Functor.rightDerivedFunctorUnitQ
          (lim : Towers (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) W ⥤
            Modules (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) W) K)
    (K : CochainComplex (Towers
      (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) W) ℤ)
    (e : ℕ) (he : 1 ≤ e) :
    QuasiIso (scalarRoosRestriction l E W K e he) ∧
      (∀ p : ℤ,
        (scalarRoosRestriction l E W K e he).f (p + 1) ≫
            (strictRoosCoordinates ((CategoryTheory.StrictTowerArithmetic.complexRestriction
              (Modules (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) W) e).obj K)
                p).hom =
          (strictRoosCoordinates K p).hom ≫
            biprod.map ((CategoryTheory.StrictTowerArithmetic.block e K.asFunctor).f p)
              ((CategoryTheory.StrictTowerArithmetic.selection e K.asFunctor).f (p + 1))) ∧
      (DerivedCategory.Q.map (scalarRoosRestriction l E W K e he) ≫
          κ.hom.app
            ((CategoryTheory.StrictTowerArithmetic.complexRestriction
              (Modules (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) W) e).obj K) ≫
          (scalarLimit l E W).map
            ((ordinarySubsequence l E W e).mapDerivedCategoryFactors.inv.app K) =
        κ.hom.app K ≫
          (scalarLimitRestriction l E W e).app (DerivedCategory.Q.obj K)) ∧
      (∀ (P : CochainComplex
          (Modules (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) W) ℤ)
        (a : ∀ n : ℕ, P ⟶ K.asFunctor.obj (op n))
        (ha : ∀ n : ℕ, a (n + 1) ≫
          K.asFunctor.map (homOfLE (Nat.le_succ n)).op = a n),
        ∃ h : ∀ n : ℕ, a (e * (n + 2) - 1) ≫
            K.asFunctor.map
              ((CategoryTheory.StrictTowerArithmetic.index e).map
                (homOfLE (Nat.le_succ n)).op) = a (e * (n + 1) - 1),
          roosAugment a ha ≫ scalarRoosRestriction l E W K e he =
            roosAugment (fun n : ℕ ↦ a (e * (n + 1) - 1)) h) := by
  have hs := (compactSupportRoosCofinality.{u + 1, u, 0} (ProEt.topology W)
    (CommRingCat.of (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)))).choose_spec.1
  have hq : QuasiIso (scalarRoosRestriction l E W K e he) := by
    unfold scalarRoosRestriction
    exact (hs K e he).1
  have hc (L : CochainComplex (Towers
      (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) W) ℤ) (p : ℤ) :
      (scalarRoosRestriction l E W L e he).f (p + 1) ≫
          (strictRoosCoordinates ((CategoryTheory.StrictTowerArithmetic.complexRestriction
            (Modules (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) W) e).obj L)
              p).hom =
        (strictRoosCoordinates L p).hom ≫
          biprod.map ((CategoryTheory.StrictTowerArithmetic.block e L.asFunctor).f p)
            ((CategoryTheory.StrictTowerArithmetic.selection e L.asFunctor).f (p + 1)) := by
    unfold scalarRoosRestriction
    exact (hs L e he).2 p
  have hn := CategoryTheory.roosArithmeticNormalization e he
    (scalarLimitRestrictionOrdinary l E W e) (fun _ ↦ rfl)
    κ
    hk
    (fun L ↦ scalarRoosRestriction l E W L e he) hc K
  refine ⟨hq, hc K, hn.1, ?_⟩
  intro P a ha
  have h (n : ℕ) : a (e * (n + 2) - 1) ≫
      K.asFunctor.map ((CategoryTheory.StrictTowerArithmetic.index e).map
        (homOfLE (Nat.le_succ n)).op) = a (e * (n + 1) - 1) := by
    exact roos_compatible K.asFunctor a ha
      (Nat.sub_le_sub_right (Nat.mul_le_mul_left e (by omega : n + 1 ≤ n + 2)) 1)
  exact ⟨h, hn.2 P a ha h⟩

end WeilConjectures.PurStrictScalar
