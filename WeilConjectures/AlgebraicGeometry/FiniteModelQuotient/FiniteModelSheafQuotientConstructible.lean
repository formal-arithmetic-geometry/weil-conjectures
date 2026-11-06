/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteModelQuotient.FiniteModelSheafQuotientData
import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
import Mathlib.RingTheory.Ideal.Quotient.Index
import WeilConjectures.NumberTheory.Padics.IntegersCosetBasis
import Mathlib.Topology.Bases
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
import Mathlib.RingTheory.Finiteness.Cardinality
import Mathlib.Topology.Algebra.Group.Quotient
import WeilConjectures.AlgebraicGeometry.FiniteModelQuotient.FiniteModelQuotientChartComparison
import WeilConjectures.AlgebraicGeometry.FiniteModelQuotient.FiniteModelQuotientCohomologyDescent
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-! # Finite reductions of integral scalar-model constructible sheaves -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory ZeroObject
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.FiniteModelQuotient
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

attribute [local instance] quotientModuleCategory quotientModuleAbelian quotientModuleDerived

private theorem finiteTopology_discrete (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (n : ℕ) :
    let := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
    DiscreteTopology (Padic.coefficientExtensionRing l E (n + 1)) := by
  let := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
  have hm : (spectralNorm.normedField (Padic l) E).toPseudoMetricSpace =
      (Padic.coefficientExtensionAbsoluteValue l E).toNormedField.toPseudoMetricSpace :=
    PseudoMetricSpace.ext (by
      ext x y
      change spectralNorm (Padic l) E (x - y) = spectralNorm (Padic l) E (-x + y)
      rw [neg_add_eq_sub, ← neg_sub x y,
        spectralNorm_neg (Algebra.IsAlgebraic.isAlgebraic _)])
  have ht := congrArg (fun m : PseudoMetricSpace E ↦
    m.toUniformSpace.toTopologicalSpace) hm
  have hti := congrArg (fun t : TopologicalSpace E ↦
    TopologicalSpace.induced (fun x : Padic.coefficientExtensionIntegers l E ↦ (x : E)) t) ht
  apply QuotientAddGroup.discreteTopology
  apply AddSubgroup.isOpen_of_mem_nhds (g := 0)
  have hb := (Padic.coefficientExtension_integers_coset_basis l E 0).mem_of_mem
    (i := n) trivial
  change @Membership.mem (Set (Padic.coefficientExtensionIntegers l E)) _ _
    (@nhds _ (TopologicalSpace.induced _ _) 0) _ at hb
  change @Membership.mem (Set (Padic.coefficientExtensionIntegers l E)) _ _
    (@nhds _ (TopologicalSpace.induced _ _) 0) _
  rw [← hti]
  have he : {y : Padic.coefficientExtensionIntegers l E |
      Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E (n + 1)) y =
        Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E (n + 1)) 0} =
      (Padic.coefficientExtensionIdeal l E (n + 1)).toAddSubgroup := by
    ext y
    change _ = _ ↔ y ∈ Padic.coefficientExtensionIdeal l E (n + 1)
    rw [map_zero, Ideal.Quotient.eq_zero_iff_mem]
  rw [he] at hb
  exact hb

private def double_homology_kernel
    {C : Type*} [Category C] [Abelian C] {X Y : C} (f : X ⟶ Y) :
    (HomologicalComplex.double f (c := ComplexShape.up ℤ)
      (i₀ := -1) (i₁ := 0) (by decide)).homology (-1) ≅ kernel f := by
  let K := HomologicalComplex.double f (c := ComplexShape.up ℤ)
    (i₀ := -1) (i₁ := 0) (by decide)
  let S : ShortComplex C := ShortComplex.mk (0 : (0 : C) ⟶ X) f (by simp)
  let e : K.sc' (-2) (-1) 0 ≅ S := ShortComplex.isoMk
    (eqToIso (by simp [K, S, HomologicalComplex.double]))
    (HomologicalComplex.doubleXIso₀ f (c := ComplexShape.up ℤ) (by decide))
    (HomologicalComplex.doubleXIso₁ f (c := ComplexShape.up ℤ) (by decide) (by decide))
    (by simp [K, S, HomologicalComplex.double])
    (by simp [K, S, HomologicalComplex.double_d, Category.assoc])
  exact ShortComplex.homologyMapIso
    (K.isoSc' (-2) (-1) 0 (by simp) (by simp) ≪≫ e) ≪≫
    (S.asIsoHomologyπ rfl).symm ≪≫ S.cyclesIsoKernel

private def double_homology_cokernel
    {C : Type*} [Category C] [Abelian C] {X Y : C} (f : X ⟶ Y) :
    (HomologicalComplex.double f (c := ComplexShape.up ℤ)
      (i₀ := -1) (i₁ := 0) (by decide)).homology 0 ≅ cokernel f := by
  let K := HomologicalComplex.double f (c := ComplexShape.up ℤ)
    (i₀ := -1) (i₁ := 0) (by decide)
  let S : ShortComplex C := ShortComplex.mk f (0 : Y ⟶ (0 : C)) (by simp)
  let e : K.sc' (-1) 0 1 ≅ S := ShortComplex.isoMk
    (HomologicalComplex.doubleXIso₀ f (c := ComplexShape.up ℤ) (by decide))
    (HomologicalComplex.doubleXIso₁ f (c := ComplexShape.up ℤ) (by decide) (by decide))
    (eqToIso (by simp [K, S, HomologicalComplex.double]))
    (by simp [K, S, HomologicalComplex.double_d, Category.assoc])
    (by simp [K, S, HomologicalComplex.double])
  exact ShortComplex.homologyMapIso
    (K.isoSc' (-1) 0 1 (by simp) (by simp) ≪≫ e) ≪≫
    S.asIsoHomologyι rfl ≪≫ S.opcyclesIsoCokernel

private theorem differential_finite (n a b : ℕ)
    (v : Matrix (Fin b) (Fin a) (A l E)) [Finite (R l E n)] :
    Finite ↥(kernel (differential l E n a b v)) ∧
      Finite ↥(cokernel (differential l E n a b v)) := by
  constructor
  · exact Finite.of_equiv _
      (ModuleCat.kernelIsoKer (differential l E n a b v)).symm.toLinearEquiv.toEquiv
  · let : Finite ((Fin b → ULift.{u + 1} (R l E n)) ⧸
        (differential l E n a b v).hom.range) :=
      Finite.of_surjective _ (Submodule.mkQ_surjective _)
    exact Finite.of_equiv _
      (ModuleCat.cokernelIsoRangeQuotient (differential l E n a b v)).symm.toLinearEquiv.toEquiv

private def ordinary_homology_kernel (T : Scheme.{u}) (n a b : ℕ)
    (v : Matrix (Fin b) (Fin a) (A l E)) :
    (DerivedCategory.homologyFunctor _ (-1)).obj (ordinaryComplex l E T n a b v) ≅
      (constantSheaf (Scheme.ProEt.topology T)
        (ModuleCat.{u + 1} (ULift.{u + 1} (R l E n)))).obj
          (kernel (differential l E n a b v)) := by
  let F := constantSheaf (Scheme.ProEt.topology T)
    (ModuleCat.{u + 1} (ULift.{u + 1} (R l E n)))
  let K := scalarComplex l E n a b v
  exact (DerivedCategory.homologyFunctorFactors _ (-1)).app _ ≪≫
    (K.sc (-1)).mapHomologyIso F ≪≫
    F.mapIso (double_homology_kernel (differential l E n a b v))

private def ordinary_homology_cokernel (T : Scheme.{u}) (n a b : ℕ)
    (v : Matrix (Fin b) (Fin a) (A l E)) :
    (DerivedCategory.homologyFunctor _ 0).obj (ordinaryComplex l E T n a b v) ≅
      (constantSheaf (Scheme.ProEt.topology T)
        (ModuleCat.{u + 1} (ULift.{u + 1} (R l E n)))).obj
          (cokernel (differential l E n a b v)) := by
  let F := constantSheaf (Scheme.ProEt.topology T)
    (ModuleCat.{u + 1} (ULift.{u + 1} (R l E n)))
  let K := scalarComplex l E n a b v
  exact (DerivedCategory.homologyFunctorFactors _ 0).app _ ≪≫
    (K.sc 0).mapHomologyIso F ≪≫
    F.mapIso (double_homology_cokernel (differential l E n a b v))

private theorem bounded_from_vanishing
    {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
    (K : DerivedCategory C)
    (h : ∀ q : ℤ, q ≠ -1 → q ≠ 0 →
      IsZero ((DerivedCategory.homologyFunctor _ q).obj K)) :
    DerivedCategory.TStructure.t.bounded K := by
  refine ⟨⟨-1, (DerivedCategory.isGE_iff K (-1)).2 ?_⟩,
    ⟨0, (DerivedCategory.isLE_iff K 0).2 ?_⟩⟩
  · intro q hq
    exact h q (by omega) (by omega)
  · intro q hq
    exact h q (by omega) (by omega)

end AlgebraicGeometry.ProEtale.FiniteModelQuotient
