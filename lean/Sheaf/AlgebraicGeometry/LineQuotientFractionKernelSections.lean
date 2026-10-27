/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group R2
-/
module

public import Sheaf.AlgebraicGeometry.LineQuotientChartInverseData
import Sheaf.TraceFormula.LineQuotientHomogeneousFractionMap

/-! # Sectionwise fraction-kernel comparison

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

/-- The fraction-chart calculation identifies the two quotient maps on every section.
Source: Stacks Project, Constructions, Tags 01OA and 01O4, affine fraction-chart
calculation and localization by a degree-one generator.
(blueprint: lem-trf-line-quotient-fraction-kernel-sections).

Proof: on an affine base and a line-trivializing affine, the fraction chart indexed by
`m` identifies the pulled tautological frame with the scalar multiple `b_m • l`. The
degree-one chart equation then sends the image of every generator `v` to `b_v • l`,
which is exactly its image under `q`. The opens `D(b_m)` cover the affine, so the two
sections have the same zero locus after restriction; sheaf separatedness gives the
displayed equivalence on each open. Empty charts satisfy the same statement.
-/
theorem lineQuotient_fraction_kernel_sections {S T : Scheme.{u}} (h : T ⟶ S)
    (E : S.Modules) [E.IsQuasicoherent] (D : TautologicalQuotient E)
    (L : T.Modules) [L.IsInvertible] (q : (tensorPullback h).obj E ⟶ L) [Epi q]
    (ψ : RelativeGradedLineMap h (SymmetricAlgebraSheaf.gradedAlgebraData E) L)
    (F : T ⟶ (SymmetricAlgebraSheaf.gradedAlgebraData E).relProj)
    (hψ : ψ.ExtendsLineQuotient h E L q)
    (hcharts : ψ.HasQuotientFractionCharts h E L q F) :
    ∀ (U : T.Opens) (x : Γ((tensorPullback h).obj E, U)),
      (pulledQuotient D h F hcharts.1).app U x = 0 ↔ q.app U x = 0 := by
  sorry

end AlgebraicGeometry.ProjectiveBundleQuotientGeometry
