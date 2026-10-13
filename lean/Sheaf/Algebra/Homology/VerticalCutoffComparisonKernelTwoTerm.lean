/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C2
-/
module

public import Sheaf.Algebra.Homology.DoubleComplexVerticalTowerMaps

/-!
# Endpoint calculation for the strict vertical cutoff comparison

Source: Stacks Project, Homology Tag 0118 (homology-section-truncations),
canonical truncations and the two-term kernel argument.
-/

@[expose] public section

universe v u
open CategoryTheory CategoryTheory.Limits
namespace HomologicalComplex₂
variable {C : Type u} [Category.{v} C] [Abelian C]

/-- The kernel of the strict cutoff comparison is a two-term complex
with invertible differential.
Source: Stacks Project, Homology Tag 0118 (homology-section-truncations),
canonical truncations; the kernel identification is agent-written.
(blueprint: lem-sp-vertical-cutoff-comparison-kernel-two-term)

Proof: write E for L extended by zero and I for image of E.d (a - 1) a.
Monicity of the upper cutoff inclusion identifies g with the nested inclusion.
Evaluation preserves cokernels. Thus cokernel g is zero below a - 1, is I
in degree a - 1, and agrees with the upper cutoff from degree a onward.
By hq, the comparison is zero in degree a - 1. At degree a it is the
opcycles quotient when a < b - 1, and the cycles-to-homology quotient when
a = b - 1. Both have kernel I. Above a, q is invertible on the nonzero
components; beyond the upper cutoff both sides are zero. Evaluation preserves
kernels, so the kernel has I in degrees a - 1 and a and zero elsewhere.
The chain map equation for the kernel inclusion identifies its differential
with the identity on I, using the image factorization of E.d (a - 1) a.
It is therefore invertible. Since 0 < a, both indices are nonnegative and
restriction preserves them: they are a.toNat - 1 and a.toNat. For a = 1
these are 0 and 1; for b = a + 1 the image lies in cycles because d squared
is zero. Zero I gives the invertible zero-to-zero differential as required. -/
theorem verticalCutoff_comparison_kernel_twoTerm
    (L : CochainComplex C ℕ) (a b : ℤ) (hab : a < b) (ha : 0 < a)
    (g : (verticalCutoff a).obj L ⟶ (verticalCutoff b).obj L)
    (hg : g ≫ (verticalCutoffι b).app L = (verticalCutoffι a).app L)
    (q : cokernel g ⟶ (verticalWindow a b).obj L)
    (hq : cokernel.π g ≫ q = HomologicalComplex.restrictionMap
      (CochainComplex.truncLEMap
        (CochainComplex.πTruncGE (L.extend ComplexShape.embeddingUpNat) a) (b - 1))
      ComplexShape.embeddingUpNat) :
    (∀ n, n ≠ a.toNat - 1 → n ≠ a.toNat → IsZero ((kernel q).X n)) ∧
      IsIso ((kernel q).d (a.toNat - 1) a.toNat) := by sorry

end HomologicalComplex₂
