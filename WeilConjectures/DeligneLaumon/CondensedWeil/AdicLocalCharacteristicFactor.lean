/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.DeligneLaumon.AdicHeartIntrinsicFibres
public import WeilConjectures.DeligneLaumon.LocalFrobeniusTrace
public import WeilConjectures.DeligneLaumon.WeilIndSheafCategory
public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import WeilConjectures.SmoothPurity.GeneralAlgebraicallyClosedCoefficients.GeneralAlgebraicallyClosedCoefficients
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
public import WeilConjectures.DeligneLaumon.CondensedWeil.CondensedWeilReality
public import WeilConjectures.Mathlib.LinearAlgebra.Charpoly.ToMatrix

import WeilConjectures.DeligneLaumon.ImmersionWeilPullbackLocalBehavior
import WeilConjectures.DeligneLaumon.AdicHeartIntrinsicFibres
import WeilConjectures.DeligneLaumon.LocalFrobeniusTrace
import WeilConjectures.CategoryTheory.DerivedCategory.Field.FieldCohomologyScalarExtension
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import WeilConjectures.SixFunctors.Supporting.FrobeniusPointTransportNatural
import WeilConjectures.SmoothPurity.Point.PointSectionsScalarExtension
import WeilConjectures.SmoothPurity.Integral.IntegralOperationsScalarComparisons
import WeilConjectures.PoincareDuality.Integral.IntegralPullbackComparisonRealization
import WeilConjectures.CategoryTheory.DerivedCategory.PerfectCategoricalTrace
import WeilConjectures.CategoryTheory.DerivedCategory.Point.PointFdQbarCategory
import WeilConjectures.Algebra.Homology.FilteredComplexSubquotients
import WeilConjectures.CategoryTheory.PBCFiltration
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.Algebra.Homology.Homotopy
import Mathlib.CategoryTheory.Quotient
import Mathlib.CategoryTheory.Localization.Construction
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import WeilConjectures.FromJoel.Algebra.Homology.BicomplexColumns
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Trace
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
import WeilConjectures.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral
import WeilConjectures.CategoryTheory.Abelian.Filtration
import WeilConjectures.CategoryTheory.FiniteFiltrationInductionExtension
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.Algebra.Module.Projective
import Mathlib.LinearAlgebra.FreeModule.Basic
import Mathlib.CategoryTheory.Localization.Predicate
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.CategoryTheory.DerivedCategory.Perfect.PerfectRingTriangleClosure
import WeilConjectures.Algebra.Homology.KFlatScalarExtensionCounit
import WeilConjectures.Algebra.Homology.BoundedFlatKFlat
import WeilConjectures.CategoryTheory.DerivedCategory.TraceLaws
import WeilConjectures.CategoryTheory.DerivedCategory.TraceScalarExtension
import Mathlib.RingTheory.LocalRing.Module
import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
import Mathlib.Algebra.Homology.Double
import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
import WeilConjectures.CategoryTheory.DerivedCategory.Field.FieldComplexCohomologySplitting
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.KProjective
import WeilConjectures.DeligneLaumon.SfWeilSheafComplex
import WeilConjectures.SmoothPurity.GeneralAlgebraicallyClosedCoefficients.GeneralAlgebraicallyClosedCoefficients
import WeilConjectures.Mathlib.Algebra.Polynomial.Reverse
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FinitelyPresentedStalk
import Mathlib.Algebra.Category.ModuleCat.Biproducts

/-!
# Local characteristic factors on actual condensed Weil modules

Source: Deligne, Weil II (1.2.13), and the latest blueprint,
def-wf-iota-real (blueprint: def-wf-iota-real).

The condensed interface uses the actual scalar stalk and its local Frobenius.
Constructibility supplies finite-dimensionality. The determinant agrees with every
finite-basis calculation and the product over roots with algebraic multiplicities;
its reality is equivalent to conjugation invariance of the embedded root multiset.
The earlier sf-prefixed common-stage interface is retained for existing consumers.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 4096
universe u v w
open CategoryTheory AlgebraicGeometry
namespace WeilConjectures

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (Ω : Type v) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
  (Y₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]
  [IsSeparated Y₀.hom]

end WeilConjectures

namespace WeilConjectures.CondensedWeil

set_option backward.isDefEq.respectTransparency true
open scoped CategoryTheory.Obj
open AlgebraicGeometry.ProEtale Polynomial CategoryTheory.Limits

private theorem polynomial_real_iff_fixed (p : Polynomial ℂ) :
    (∀ j : ℕ, (p.coeff j).im = 0) ↔ p.map (starRingEnd ℂ) = p := by
  constructor
  · intro h
    ext j
    simpa only [Polynomial.coeff_map] using Complex.conj_eq_iff_im.mpr (h j)
  · intro h j
    apply Complex.conj_eq_iff_im.mp
    simpa only [Polynomial.coeff_map] using
      congrArg (fun q : Polynomial ℂ ↦ q.coeff j) h

private theorem reverse_real_iff_roots (p : Polynomial ℂ) (hp : p.Monic) :
    (∀ j : ℕ, (p.reverse.coeff j).im = 0) ↔
      p.roots.map (star : ℂ → ℂ) = p.roots := by
  rw [polynomial_real_iff_fixed]
  have hrev : p.reverse.map (starRingEnd ℂ) = p.reverse ↔
      p.map (starRingEnd ℂ) = p := by
    constructor
    · intro h
      rw [← Polynomial.reverse_map (starRingEnd ℂ).injective] at h
      have h' := congrArg (Polynomial.reflect p.natDegree) h
      simpa only [Polynomial.reverse,
        Polynomial.natDegree_map_eq_of_injective (starRingEnd ℂ).injective,
        Polynomial.reflect_reflect] using h'
    · intro h
      rw [← Polynomial.reverse_map (starRingEnd ℂ).injective, h]
  rw [hrev]
  have hroots : (p.map (starRingEnd ℂ)).roots = p.roots.map (star : ℂ → ℂ) :=
    (IsAlgClosed.splits p).roots_map_of_injective (starRingEnd ℂ).injective
  constructor
  · intro h
    rw [← hroots, h]
  · intro h
    calc
      p.map (starRingEnd ℂ) =
          (((p.map (starRingEnd ℂ)).roots).map (fun a ↦ X - C a)).prod :=
        (IsAlgClosed.splits _).eq_prod_roots_of_monic (hp.map _)
      _ = (p.roots.map (fun a ↦ X - C a)).prod := by rw [hroots, h]
      _ = p := ((IsAlgClosed.splits p).eq_prod_roots_of_monic hp).symm

private theorem finite_evaluation_of_presentation
    {K : Type u} [Field K] {C : Type v} [Category.{w} C] [Preadditive C]
    [HasFiniteColimits C] [HasFiniteBiproducts C]
    (F : C ⥤ ModuleCat.{w} K) [F.Additive] [PreservesFiniteColimits F]
    (R N : C) [Module.Finite K (F.obj R)]
    (hN : ∃ (n m : ℕ)
      (f : (⨁ fun _ : Fin m ↦ R) ⟶ (⨁ fun _ : Fin n ↦ R)),
      Nonempty (N ≅ cokernel f)) :
    Module.Finite K (F.obj N) := by
  have hfree (n : ℕ) : Module.Finite K (F.obj (⨁ fun _ : Fin n ↦ R)) := by
    let e : F.obj (⨁ fun _ : Fin n ↦ R) ≃ₗ[K] (Fin n → F.obj R) :=
      (F.mapBiproduct (fun _ : Fin n ↦ R) ≪≫ ModuleCat.biproductIsoPi _).toLinearEquiv
    have : Module.Finite K (Fin n → F.obj R) := inferInstance
    exact Module.Finite.equiv e.symm
  obtain ⟨n, m, f, ⟨e⟩⟩ := hN
  have := hfree n
  have : Module.Finite K (cokernel (F.map f) : ModuleCat K) :=
    Module.Finite.of_surjective (cokernel.π (F.map f)).hom
      ((ModuleCat.epi_iff_surjective _).mp inferInstance)
  exact Module.Finite.equiv (F.mapIso e ≪≫ PreservesCokernel.iso F f).toLinearEquiv.symm

private theorem module_basis_factor
    {K : Type u} [Field K] (V : ModuleCat.{v} K) [FiniteDimensional K V]
    (f : V ⟶ V) (n : ℕ) (b : Module.Basis (Fin n) K V) :
    (LinearMap.toMatrix b b f.hom).charpoly.reverse = f.hom.charpolyRev :=
  congrArg Polynomial.reverse (LinearMap.charpoly_toMatrix f.hom b)

private theorem monic_reverse_eq_prod_roots
    {K : Type u} [Field K] [IsAlgClosed K] (p : Polynomial K) (hp : p.Monic) :
    p.reverse = (p.roots.map (fun a ↦ 1 - C a * X)).prod := by
  conv_lhs => rw [(IsAlgClosed.splits p).eq_prod_roots_of_monic hp]
  exact Polynomial.reverse_multiset_prod_X_sub_C _

private theorem map_reverse_real_iff_roots
    {K : Type u} [Field K] [IsAlgClosed K] (p : Polynomial K) (hp : p.Monic)
    (iota : K →+* ℂ) :
    (∀ j : ℕ, (iota (p.reverse.coeff j)).im = 0) ↔
      (p.roots.map iota).map (star : ℂ → ℂ) = p.roots.map iota := by
  have h := reverse_real_iff_roots (p.map iota) (hp.map iota)
  rw [(IsAlgClosed.splits p).roots_map_of_injective iota.injective,
    Polynomial.reverse_map iota.injective] at h
  simpa only [Polynomial.coeff_map] using h

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
  (X₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]

/-- Constructibility gives finite-dimensional actual scalar stalks, without a finite
coefficient presentation. Pullback to the algebraically closed point is finitely
presented; evaluation is right exact, and sends each finite free module to a finite
power of the scalar field. A cokernel of a map between such powers is finite dimensional.
Source: latest blueprint def-wf-iota-real, constructible stalk convention
(blueprint: def-wf-iota-real). -/
theorem closedFiber_finite (M : WeilModule D l X₀)
    (hM : IsConstructibleModuleObject
      (condensedRingObj (Profinite.padicAlgClRingObj l) (D.geometricFiber X₀).left) M.carrier)
    (x : {x : X₀.left // x ∈ closedPoints X₀.left})
    (i : X₀.left.residueField x.val →+* D.k)
    (hi : i.comp (X₀.hom.residueFieldAlgebraMap x.val) = algebraMap D.k₀ D.k) :
    FiniteDimensional (PadicAlgCl l) (closedFiber D l X₀ M x i hi) := by
  let A := condensedRingObj (Profinite.padicAlgClRingObj l) (Spec (.of D.k))
  let F := CondensedQbarGeometricEvaluation.fieldFiber D.k l
  have : Module.Finite (PadicAlgCl l) (F.obj (Mod.regular A)) :=
    Module.Finite.equiv (CondensedQbarGeometricEvaluation.fieldRegularCoordinates D.k l).symm
  exact finite_evaluation_of_presentation F (Mod.regular A)
    ((CondensedRing.upperStar (Profinite.padicAlgClRingObj l)
      (localClosedPoint D X₀ x i hi)).obj M.carrier)
    (CondensedRing.isFinitelyPresented_upperStar_of_isConstructibleModuleObject
      (Profinite.padicAlgClRingObj l) (Field.toIsField D.k) IsField.isSepClosed_toField
      hM (localClosedPoint D X₀ x i hi))

/-- The local determinant on a constructible actual condensed Weil module. This is the
existing intrinsic determinant, with finite-dimensionality supplied by constructibility.
Source: latest blueprint def-wf-iota-real, displayed P_x(T)
(blueprint: def-wf-iota-real). -/
abbrev constructibleLocalFactor (M : WeilModule D l X₀)
    (hM : IsConstructibleModuleObject
      (condensedRingObj (Profinite.padicAlgClRingObj l) (D.geometricFiber X₀).left) M.carrier)
    (x : {x : X₀.left // x ∈ closedPoints X₀.left})
    (i : X₀.left.residueField x.val →+* D.k)
    (hi : i.comp (X₀.hom.residueFieldAlgebraMap x.val) = algebraMap D.k₀ D.k) :
    Polynomial (PadicAlgCl l) :=
  letI := closedFiber_finite D l X₀ M hM x i hi
  localFactor D l X₀ M x i hi

/-- Computing the actual local determinant in a finite basis gives its intrinsic value.
Source: latest blueprint def-wf-iota-real, displayed determinant
(blueprint: def-wf-iota-real). -/
theorem localFactorInBasis_eq (M : WeilModule D l X₀)
    (x : {x : X₀.left // x ∈ closedPoints X₀.left})
    (i : X₀.left.residueField x.val →+* D.k)
    (hi : i.comp (X₀.hom.residueFieldAlgebraMap x.val) = algebraMap D.k₀ D.k)
    [FiniteDimensional (PadicAlgCl l) (closedFiber D l X₀ M x i hi)]
    (n : ℕ) (b : Module.Basis (Fin n) (PadicAlgCl l) (closedFiber D l X₀ M x i hi)) :
    localFactorInBasis D l X₀ M x i hi n b = localFactor D l X₀ M x i hi := by
  exact module_basis_factor (closedFiber D l X₀ M x i hi)
    (closedOperator D l X₀ M x i hi) n b

/-- The local determinant is the product over the characteristic roots, with their
algebraic multiplicities. Zero-dimensional stalks give the empty product.
Source: latest blueprint def-wf-iota-real, displayed product
(blueprint: def-wf-iota-real). -/
theorem localFactor_eq_prod_roots (M : WeilModule D l X₀)
    (x : {x : X₀.left // x ∈ closedPoints X₀.left})
    (i : X₀.left.residueField x.val →+* D.k)
    (hi : i.comp (X₀.hom.residueFieldAlgebraMap x.val) = algebraMap D.k₀ D.k)
    [FiniteDimensional (PadicAlgCl l) (closedFiber D l X₀ M x i hi)] :
    localFactor D l X₀ M x i hi =
      (((closedOperator D l X₀ M x i hi).hom.charpoly.roots).map
        (fun a ↦ 1 - C a * X)).prod := by
  exact monic_reverse_eq_prod_roots
    (closedOperator D l X₀ M x i hi).hom.charpoly
    (LinearMap.charpoly_monic (closedOperator D l X₀ M x i hi).hom)

/-- Reality in finite bases is exactly reality of the intrinsic determinant on every
closed-point scalar stalk. Finiteness is the constructible-fibre property; no basis is data.
Source: latest blueprint def-wf-iota-real, reality paragraph
(blueprint: def-wf-iota-real). -/
theorem real_iff_localFactor (M : WeilModule D l X₀) (iota : PadicAlgCl l →+* ℂ)
    (hfinite : ∀ (x : {x : X₀.left // x ∈ closedPoints X₀.left})
      (i : X₀.left.residueField x.val →+* D.k)
      (hi : i.comp (X₀.hom.residueFieldAlgebraMap x.val) = algebraMap D.k₀ D.k),
      FiniteDimensional (PadicAlgCl l) (closedFiber D l X₀ M x i hi)) :
    Real D l X₀ M iota ↔
      ∀ (x : {x : X₀.left // x ∈ closedPoints X₀.left})
        (i : X₀.left.residueField x.val →+* D.k)
        (hi : i.comp (X₀.hom.residueFieldAlgebraMap x.val) = algebraMap D.k₀ D.k),
        letI := hfinite x i hi
        ∀ j : ℕ, (iota ((localFactor D l X₀ M x i hi).coeff j)).im = 0 := by
  constructor
  · intro h x i hi j
    let := hfinite x i hi
    let b := Module.finBasis (PadicAlgCl l) (closedFiber D l X₀ M x i hi)
    have e := localFactorInBasis_eq D l X₀ M x i hi _ b
    exact (congrArg (fun p : Polynomial (PadicAlgCl l) ↦ (iota (p.coeff j)).im) e).symm.trans
      (h x i hi _ b j)
  · intro h x i hi n b j
    let := hfinite x i hi
    have e := localFactorInBasis_eq D l X₀ M x i hi n b
    exact (congrArg (fun p : Polynomial (PadicAlgCl l) ↦ (iota (p.coeff j)).im) e).trans
      (h x i hi j)

/-- A local determinant is real under any complex field embedding exactly when the
embedded characteristic-root multiset is stable under conjugation. No surjectivity of
that embedding, invertibility or semisimplicity is needed in this linear-algebra identity.
Source: latest blueprint def-wf-iota-real, equivalent eigenvalue formulation
(blueprint: def-wf-iota-real). -/
theorem localFactor_real_iff_roots (M : WeilModule D l X₀)
    (x : {x : X₀.left // x ∈ closedPoints X₀.left})
    (i : X₀.left.residueField x.val →+* D.k)
    (hi : i.comp (X₀.hom.residueFieldAlgebraMap x.val) = algebraMap D.k₀ D.k)
    [FiniteDimensional (PadicAlgCl l) (closedFiber D l X₀ M x i hi)]
    (iota : PadicAlgCl l →+* ℂ) :
    (∀ j : ℕ, (iota ((localFactor D l X₀ M x i hi).coeff j)).im = 0) ↔
      (((closedOperator D l X₀ M x i hi).hom.charpoly.roots).map iota).map
          (star : ℂ → ℂ) =
        ((closedOperator D l X₀ M x i hi).hom.charpoly.roots).map iota := by
  exact map_reverse_real_iff_roots
    (closedOperator D l X₀ M x i hi).hom.charpoly
    (LinearMap.charpoly_monic (closedOperator D l X₀ M x i hi).hom) iota

/-- On constructible actual Weil modules, the basis-free reality predicate says exactly
that each embedded local factor has real coefficients. No finiteness hypothesis is added.
Source: latest blueprint def-wf-iota-real, reality clause
(blueprint: def-wf-iota-real). -/
theorem constructible_real_iff (M : WeilModule D l X₀)
    (hM : IsConstructibleModuleObject
      (condensedRingObj (Profinite.padicAlgClRingObj l) (D.geometricFiber X₀).left) M.carrier)
    (iota : PadicAlgCl l →+* ℂ) :
    Real D l X₀ M iota ↔
      ∀ (x : {x : X₀.left // x ∈ closedPoints X₀.left})
        (i : X₀.left.residueField x.val →+* D.k)
        (hi : i.comp (X₀.hom.residueFieldAlgebraMap x.val) = algebraMap D.k₀ D.k)
        (j : ℕ),
        (iota ((constructibleLocalFactor D l X₀ M hM x i hi).coeff j)).im = 0 :=
  real_iff_localFactor D l X₀ M iota (closedFiber_finite D l X₀ M hM)

end WeilConjectures.CondensedWeil
