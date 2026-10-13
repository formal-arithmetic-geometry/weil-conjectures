/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group U3
-/
module

public import Sheaf.Algebra.Homology.DoubleComplexVerticalTowerMaps

/-!
# Boundary universal properties of nested vertical cutoffs

Source: Stacks Project, Homology Tag 0118 (homology-section-truncations),
canonical truncations (3) and (4).
-/

@[expose] public section

universe v u
open CategoryTheory CategoryTheory.Limits
namespace HomologicalComplex₂
variable {C : Type u} [Category.{v} C] [Abelian C]

/-- The boundary inclusion is a kernel, and the boundary comparison is a cokernel.
Source: Stacks Project, Tag 0118 (homology-section-truncations), canonical
truncations (3) and (4); the specialization to the upper cutoff is agent-written.
(blueprint: lem-sp-vertical-cutoff-endpoint-forks)

Proof: put E = L extended by zero, B = tau-le-(b-1) E, and m = a-1.
The inclusion of tau-le-m E into B in degree m is the kernel of B.d m a:
B agrees with E in degree m, and its inclusion into E is mono in degree a.
The cycles object of E at m is the kernel of E.d m a. Naturality and the
factorization equation for g give precisely this kernel inclusion, so transport
that kernel fork through the invertible degree-m inclusion of B. Restriction
preserves the coordinates because a>0.
For the cokernel fork, if a<b-1 then B agrees with E in degree a. The comparison
at a is the opcycles projection, the cokernel of E.d m a, conjugated by the
canonical truncation isomorphisms. If a=b-1, B.X a is cycles of E at a and the
window component is homology of E at a. Its comparison is cycles to homology,
the cokernel of the differential into cycles. The chain condition puts the
image of E.d m a in cycles. Transport these cokernel forks through the
truncation isomorphisms. The equations of both forks follow from chain-map
compatibility and the zero terms of the lower cutoff and window, respectively.
For a=1 the surviving indices are 0 and 1. For zero differential both forks
are the usual kernel of zero and cokernel of zero, so no nonzero-object
hypothesis is needed. -/
theorem verticalCutoff_endpoint_forks
    (L : CochainComplex C ℕ) (a b : ℤ) (hab : a < b) (ha : 0 < a)
    (g : (verticalCutoff a).obj L ⟶ (verticalCutoff b).obj L)
    (hg : g ≫ (verticalCutoffι b).app L = (verticalCutoffι a).app L) :
    (∃ h : g.f (a.toNat - 1) ≫
        ((verticalCutoff b).obj L).d (a.toNat - 1) a.toNat = 0,
      Nonempty (IsLimit (KernelFork.ofι (g.f (a.toNat - 1)) h))) ∧
    (∃ h : ((verticalCutoff b).obj L).d (a.toNat - 1) a.toNat ≫
        (HomologicalComplex.restrictionMap
          (CochainComplex.truncLEMap
            (CochainComplex.πTruncGE (L.extend ComplexShape.embeddingUpNat) a) (b - 1))
          ComplexShape.embeddingUpNat).f a.toNat = 0,
      Nonempty (IsColimit (CokernelCofork.ofπ
        ((HomologicalComplex.restrictionMap
          (CochainComplex.truncLEMap
            (CochainComplex.πTruncGE (L.extend ComplexShape.embeddingUpNat) a) (b - 1))
          ComplexShape.embeddingUpNat).f a.toNat) h))) := by sorry

end HomologicalComplex₂
