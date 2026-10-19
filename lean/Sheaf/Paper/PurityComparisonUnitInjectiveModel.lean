/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q23
-/
module

public import Sheaf.AlgebraicGeometry.ProEtaleSiteComparisonDerived
public import Sheaf.AlgebraicGeometry.ProEtaleFiniteModules
public import Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus

set_option autoImplicit false

/-!
# Injective-resolution representative of the comparison unit

Source: literature/stacks-project/derived.tex, Lemma Tags 0DVC and 09T5
(blueprint: lem-pur-comparison-unit-injective-model).
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.ProEtale

variable (T : Scheme.{u}) (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
  [TopologicalSpace Λ] [DiscreteTopology Λ]

/-- The unit of the bounded-below etale/pro-etale comparison, evaluated on an
injective resolution, is represented by the ordinary termwise unit followed by
that resolution. Source: literature/stacks-project/derived.tex, Lemma Tags 0DVC
and 09T5 (blueprint: lem-pur-comparison-unit-injective-model).

Proof: apply the normalization formula `Adjunction.derivedPlus_unit_app_fac` for
this specified derived adjunction. Postcompose with the derived image of `j` and
use naturality of the right-derived comparison to obtain the displayed equality.
Localization inverts the quasi-isomorphism `j`, proving the first isomorphism
clause. The comparison is invertible on the termwise injective complex `J`,
proving the second clause. -/
theorem comparisonUnitInjectiveModel
    (M : CochainComplex.Plus
      (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (J : CochainComplex.Plus (FiniteCoefficientModules T Λ))
    (j : (finiteCoefficientComparison T Λ).mapCochainComplexPlus.obj M ⟶ J)
    (hj : HomologicalComplex.quasiIso (FiniteCoefficientModules T Λ) (.up ℤ) j.hom)
    (hJ : ∀ i : ℤ, Injective (J.obj.X i)) :
    IsIso
        ((finiteCoefficientDirectImage T Λ).rightDerivedFunctorPlus.map
          ((finiteCoefficientComparison T Λ).mapDerivedCategoryPlusFactorsh.hom.app
              ((HomotopyCategory.Plus.quotient
                  (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ))).obj M) ≫
            (DerivedCategory.Plus.Qh.map
              ((HomotopyCategory.Plus.quotient (FiniteCoefficientModules T Λ)).map j)))) ∧
      IsIso
        ((finiteCoefficientDirectImage T Λ).rightDerivedFunctorPlusUnit.app
          (((HomotopyCategory.Plus.quotient
              (FiniteCoefficientModules T Λ)).obj J))) ∧
      (finiteCoefficientDerivedComparisonAdjunction T Λ).unit.app
          (DerivedCategory.Plus.Qh.obj
            ((HomotopyCategory.Plus.quotient
              (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ))).obj M)) ≫
        (finiteCoefficientDirectImage T Λ).rightDerivedFunctorPlus.map
          ((finiteCoefficientComparison T Λ).mapDerivedCategoryPlusFactorsh.hom.app
            ((HomotopyCategory.Plus.quotient
                (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ))).obj M) ≫
            (DerivedCategory.Plus.Qh.map
              ((HomotopyCategory.Plus.quotient (FiniteCoefficientModules T Λ)).map j))) =
      DerivedCategory.Plus.Qh.map
          ((finiteCoefficientComparisonAdjunction T Λ).mapHomotopyCategoryPlus.unit.app
              ((HomotopyCategory.Plus.quotient
                (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ))).obj M) ≫
            (finiteCoefficientDirectImage T Λ).mapHomotopyCategoryPlus.map
              ((HomotopyCategory.Plus.quotient (FiniteCoefficientModules T Λ)).map j)) ≫
        (finiteCoefficientDirectImage T Λ).rightDerivedFunctorPlusUnit.app
          (((HomotopyCategory.Plus.quotient
              (FiniteCoefficientModules T Λ)).obj J)) := by
  let L := finiteCoefficientComparison T Λ
  let R := finiteCoefficientDirectImage T Λ
  let A := Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)
  let B := FiniteCoefficientModules T Λ
  let K : HomotopyCategory.Plus A := (HomotopyCategory.Plus.quotient A).obj M
  let qj : L.mapHomotopyCategoryPlus.obj K ⟶
      (HomotopyCategory.Plus.quotient B).obj J :=
    (HomotopyCategory.Plus.quotient B).map j
  have hqj : IsIso (DerivedCategory.Plus.Qh.map qj) := by
    apply Localization.inverts DerivedCategory.Plus.Qh (HomotopyCategory.Plus.quasiIso B) _
    exact (HomotopyCategory.quotient_map_mem_quasiIso_iff _).2 hj
  have hfirst : IsIso
      (R.rightDerivedFunctorPlus.map (L.mapDerivedCategoryPlusFactorsh.hom.app K ≫
        DerivedCategory.Plus.Qh.map qj)) := by
    have : IsIso (L.mapDerivedCategoryPlusFactorsh.hom.app K) := inferInstance
    infer_instance
  have hsecond : IsIso
      (R.rightDerivedFunctorPlusUnit.app ((HomotopyCategory.Plus.quotient B).obj J)) := by
    let : ∀ i : ℤ, Injective (J.obj.X i) := hJ
    infer_instance
  refine ⟨hfirst, hsecond, ?_⟩
  change (finiteCoefficientComparisonAdjunction T Λ).derivedPlus.unit.app
      (DerivedCategory.Plus.Qh.obj K) ≫
      R.rightDerivedFunctorPlus.map (L.mapDerivedCategoryPlusFactorsh.hom.app K ≫
        DerivedCategory.Plus.Qh.map qj) =
    DerivedCategory.Plus.Qh.map
      ((finiteCoefficientComparisonAdjunction T Λ).mapHomotopyCategoryPlus.unit.app K ≫
        R.mapHomotopyCategoryPlus.map qj) ≫
      R.rightDerivedFunctorPlusUnit.app ((HomotopyCategory.Plus.quotient B).obj J)
  have hfac := (finiteCoefficientComparisonAdjunction T Λ).derivedPlus_unit_app_fac K
  have hnat := R.rightDerivedFunctorPlusUnit.naturality qj
  dsimp only [Functor.comp_map] at hnat
  rw [Functor.map_comp, ← Category.assoc, hfac, Category.assoc, ← hnat,
    ← Category.assoc, ← Functor.map_comp]

end AlgebraicGeometry.ProEtale
