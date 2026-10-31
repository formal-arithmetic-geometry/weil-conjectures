/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProjectiveBundleQuotientGeometry.LineQuotientChartInverseData
import WeilConjectures.AlgebraicGeometry.ProjectiveBundleQuotientGeometry.LineQuotientFractionKernelSections
import WeilConjectures.AlgebraicGeometry.Line.LineQuotientFractionKernelCategorical

/-! # LineQuotientFractionKernel

Source: Stacks Project, Constructions, Tags 01OA and 01O4.
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProjectiveBundleQuotientGeometry
open Scheme.Modules

/-- A fraction-chart morphism identifies the kernels of the original quotient and the
pulled tautological quotient.
Source: Stacks Project, Constructions, Tag 01OA, inverse quotient construction.
(blueprint: lem-trf-line-quotient-fraction-kernel).

Proof: on an affine base U and a line-trivializing affine W, cover W by D(b_m).
The chart formula sends iota(v)/iota(m) to b_v/b_m. The normalized tautological
quotient therefore sends v tensor 1 to (b_v/b_m)e, while q sends it to b_v l.
Multiplication by the unit b_m identifies these two linear maps on pure tensors;
pure tensors generate the affine pullback module. Thus their kernels agree on
these opens. For any r, the equality r;q=0 is local on its source sections, and
the same local isomorphism gives r;q_F=0 in both directions. The D(b_m) cover
by the fraction-chart hypothesis, so sheaf separatedness proves the global
biconditional. This needs no finite generation and works for empty charts. -/
theorem lineQuotient_fraction_kernel {S T : Scheme.{u}} (h : T ⟶ S)
    (E : S.Modules) [E.IsQuasicoherent] (D : TautologicalQuotient E)
    (L : T.Modules) [L.IsInvertible] (q : (tensorPullback h).obj E ⟶ L) [Epi q]
    (ψ : RelativeGradedLineMap h (SymmetricAlgebraSheaf.gradedAlgebraData E) L)
    (F : T ⟶ (SymmetricAlgebraSheaf.gradedAlgebraData E).relProj)
    (hψ : ψ.ExtendsLineQuotient h E L q)
    (hcharts : ψ.HasQuotientFractionCharts h E L q F) :
    ∀ (N : T.Modules) (r : N ⟶ (tensorPullback h).obj E),
      r ≫ pulledQuotient D h F hcharts.1 = 0 ↔ r ≫ q = 0 := by
  intro N r
  have hsec := lineQuotient_fraction_kernel_sections h E D L q ψ F hψ hcharts
  rw [comp_zero_iff_forall_section_zero, comp_zero_iff_forall_section_zero]
  constructor
  · intro h U x
    exact (hsec U (r.app U x)).mp (h U x)
  · intro h U x
    exact (hsec U (r.app U x)).mpr (h U x)

end AlgebraicGeometry.ProjectiveBundleQuotientGeometry
