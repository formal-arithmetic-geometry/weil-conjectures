/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q121
-/
module

public import Sheaf.Paper.CompactSupportIntrinsicTensorComparison
public import Sheaf.Paper.IntrinsicFiniteTorsionConstructibility
public import Sheaf.Paper.CompactSupportReductionTowerData
public import Sheaf.SecSmoothPurity.IntrinsicCompactSupportRestriction
public import Sheaf.Algebra.Homology.SheafRingDerivedCoefficientAdjunction
import Sheaf.Paper.FiniteCompactSupportScalarComparison
import Sheaf.Paper.ProEtaleBoundedConstructibleTriangulated

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
