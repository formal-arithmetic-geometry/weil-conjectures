/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CompactSupportIntrinsicTensorComparison
public import WeilConjectures.AlgebraicGeometry.IntrinsicFiniteTorsionConstructibility
public import WeilConjectures.AlgebraicGeometry.CompactSupportReductionTowerData
public import WeilConjectures.SecSmoothPurity.IntrinsicCompactSupportRestriction
public import WeilConjectures.Algebra.Homology.SheafRingDerivedCoefficientAdjunction
public import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
public import Mathlib.CategoryTheory.Adjunction.Additive
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
public import WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex
public import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
public import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.RingTheory.Flat.CategoryTheory
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.SiteTensorFunctorialitySupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
public import WeilConjectures.Algebra.Homology.SheafRingCoefficientOrdinaryAdjunction
public import WeilConjectures.Algebra.Homology.SheafRingDerivedHomComparison
public import WeilConjectures.CategoryTheory.DerivedCategory.ResolvingClassEssentialConstancy
public import WeilConjectures.CategoryTheory.DerivedCategory.DerivedAdjunctionCompatibility
public import Mathlib.CategoryTheory.MorphismProperty.Comma
public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
public import Mathlib.CategoryTheory.Functor.Derived.RightDerived
public import WeilConjectures.CategoryTheory.DerivedCategory.EssentiallyConstantInd
public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.CategoryTheory.Limits.Cones
public import WeilConjectures.CategoryTheory.DerivedCategory.EssentiallyConstantPro
public import Mathlib.Algebra.Homology.DerivedCategory.Fractions
public import Mathlib.CategoryTheory.Functor.Derived.Adjunction
public import Mathlib.CategoryTheory.Functor.KanExtension.Preserves
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedPointwiseKanBridge
public import WeilConjectures.Algebra.Homology.QuasiIsoSaturatedTriangulated
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseRightDerived
import WeilConjectures.AlgebraicGeometry.FiniteCompactSupportScalarComparison
import WeilConjectures.AlgebraicGeometry.ProEtaleBoundedConstructibleTriangulated

/-! # The adjoint of a finite compact-support reduction transition

Source: blueprint lem-coef-integral-compact-support, proof paragraph 2;
Stacks Tags 07A6, 0GL5 and 0GL6
(blueprint: lem-coef-compact-support-reduction-adjoint).

Positive coefficient levels are indexed by successors, as in the published tower data.
The comparison is the specified tensor-unit mate, with the same compactification.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory WeilConjectures
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry.Scheme

/-- The actual compact-support transition has the specified invertible tensor adjoint.
Here the levels called m and n in the source are indexed by `m + 1` and `n + 1`.
The first equality is the unit formula equivalent to identifying its adjoint with
compact support of beta after the canonical tensor comparison.

Source: blueprint lem-coef-integral-compact-support, proof paragraph 2, specified
coefficient maps; Stacks Tags 07A6, 0GL5 and 0GL6
(blueprint: lem-coef-compact-support-reduction-adjoint).

Proof: (1) Beta identifies every cohomology sheaf of the actual derived reduction of V
with that of W, so boundedness and each finite constructible stratification transfer
from W to that reduction (def-weil-finite-torsion-constructibility).
(2) Apply lem-finite-compact-support-scalar-comparison to V and its actual reduction
on the fixed compactification. Its scalar-adjunction transpose is precisely
intrinsicCompactSupportCoefficientComparison, by its defining Hom-bijection formula.
Thus this particular gamma is invertible, without a Tor-amplitude or flatness assumption.
(3) Expand gamma's unit equation. Naturality of sfCompactSupportRestriction at beta
moves restriction of F_n(beta) past sigma, and functoriality combines the resulting
F_m(Res(beta)) with F_m(eta_X). This gives exactly sigma_W F_m(rho), the actual tau.
(4) The scalar adjunction sends an arrow a to eta_Y followed by Res_Y(a); injectivity
of its Hom bijection therefore identifies the adjunct of tau with gamma followed by
F_n(beta). Finally functoriality sends beta's inverse to an inverse of F_n(beta).
These are the four proof steps of the node, using its recorded scalar adjunction,
restriction comparison, tensor comparison and finite-comparison invertibility theorem. -/
theorem coefCompactSupportReductionAdjoint
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E]
    (k : Type u) [Field k] (_hl : IsUnit (l : k))
    (m n : ℕ) (hmn : n ≤ m)
    {X Y : Scheme.{u}}
    [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (c : Compactification f)
    (V : proEtaleDerivedCategory X (Padic.coefficientExtensionRing l E (m + 1)))
    (W : proEtaleDerivedCategory X (Padic.coefficientExtensionRing l E (n + 1)))
    (_hV : intrinsicFiniteTorsionConstructible l E (m + 1) (Nat.le_add_left 1 m) X V)
    (_hW : intrinsicFiniteTorsionConstructible l E (n + 1) (Nat.le_add_left 1 n) X W)
    (β : (pbcDerivedExtend (compactSupportLevelSheafQuotient l E X m n hmn)).obj V ≅ W) :
    ((pbcDerivedScalarAdjunction (compactSupportLevelSheafQuotient l E Y m n hmn)).unit.app
        ((sfIntrinsicCompactSupport c (Padic.coefficientExtensionRing l E (m + 1))).obj V) ≫
      (pbcDerivedRestrict (compactSupportLevelSheafQuotient l E Y m n hmn)).map
        (intrinsicCompactSupportCoefficientComparison
            (compactSupportLevelQuotient l E m n hmn) c V ≫
          (sfIntrinsicCompactSupport c (Padic.coefficientExtensionRing l E (n + 1))).map
            β.hom) =
      (sfIntrinsicCompactSupport c (Padic.coefficientExtensionRing l E (m + 1))).map
          ((pbcDerivedScalarAdjunction
              (compactSupportLevelSheafQuotient l E X m n hmn)).unit.app V ≫
            (pbcDerivedRestrict (compactSupportLevelSheafQuotient l E X m n hmn)).map
              β.hom) ≫
        (sfCompactSupportRestriction c (compactSupportLevelQuotient l E m n hmn)).hom.app W) ∧
    IsIso (intrinsicCompactSupportCoefficientComparison
      (compactSupportLevelQuotient l E m n hmn) c V) ∧
    IsIso ((sfIntrinsicCompactSupport c (Padic.coefficientExtensionRing l E (n + 1))).map
      β.hom) := by
  have hred : intrinsicFiniteTorsionConstructible l E (n + 1)
      (Nat.le_add_left 1 n) X
      ((pbcDerivedExtend (compactSupportLevelSheafQuotient l E X m n hmn)).obj V) := by
    have hc := (proEtale_bounded_constructible_isTriangulated X
      (Padic.coefficientExtensionRing l E (n + 1))).1
    exact hc.of_iso β.symm _hW
  refine ⟨?_, ?_, inferInstance⟩
  · let φ := compactSupportLevelQuotient l E m n hmn
    let ax := pbcDerivedScalarAdjunction (compactSupportLevelSheafQuotient l E X m n hmn)
    let ay := pbcDerivedScalarAdjunction (compactSupportLevelSheafQuotient l E Y m n hmn)
    let F := sfIntrinsicCompactSupport c (Padic.coefficientExtensionRing l E (m + 1))
    let G := sfIntrinsicCompactSupport c (Padic.coefficientExtensionRing l E (n + 1))
    let R := pbcDerivedRestrict (compactSupportLevelSheafQuotient l E Y m n hmn)
    let σ := (sfCompactSupportRestriction c φ).hom
    have hunit := ay.homEquiv _ _ |>.apply_symm_apply
      (F.map (ax.unit.app V) ≫ σ.app _)
    rw [Adjunction.homEquiv_unit] at hunit
    change ay.unit.app (F.obj V) ≫ R.map
      (intrinsicCompactSupportCoefficientComparison φ c V) = _ at hunit
    have hnat := σ.naturality β.hom
    change F.map
        ((pbcDerivedRestrict (compactSupportLevelSheafQuotient l E X m n hmn)).map β.hom) ≫
        σ.app W = σ.app _ ≫ R.map (G.map β.hom) at hnat
    rw [Functor.map_comp, ← Category.assoc, hunit, Category.assoc, ← hnat]
    simp only [← Category.assoc, ← Functor.map_comp]
    rfl
  · exact finiteCompactSupportScalarComparison l E k _hl
      (m + 1) (Nat.le_add_left 1 m) (n + 1) (Nat.le_add_left 1 n)
      (Nat.add_le_add_right hmn 1) f c V _hV hred

end AlgebraicGeometry.Scheme
