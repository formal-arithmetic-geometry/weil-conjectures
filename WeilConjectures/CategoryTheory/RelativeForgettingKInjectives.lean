/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.RelativeDerivedInvariants

/-! # K-injectives under forgetting a commuting profinite action

Source: the relative invariant-forgetting construction, paragraph (3), step 6.
(blueprint: lem-sfb-relative-forgetting-kinjectives)
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.CondensedBar
namespace CategoryTheory.RelativeCyclic

/-- Forgetting the first factor preserves K-injective complexes for every topological
retained group.

Source: paragraph (3), step 6 of the relative invariant-forgetting construction;
the exact free-induction construction in `ProductActionExactForgetting`.
(blueprint: lem-sfb-relative-forgetting-kinjectives)

Proof: form the free internal module R[G] on the represented profinite sheaf G.
For a J-action M, give R[G] tensor M the action
(a,j)([g] tensor m) = [ag] tensor jm. Balancing, the two group laws and restriction
naturality hold on pure tensors, hence on the sheafified tensor. Apply a morphism
of J-actions to the second tensor factor to obtain an additive induction functor.
Evaluation at [1] tensor m and the map [g] tensor m to g f(m) are mutually inverse
natural transposes, so induction is left adjoint to restriction along j to (1,j).
The represented free module R[G] is flat, as follows from its extension-by-zero
presentation, already supplied by the product-forgetting datum with trivial retained
group. Consequently induction preserves kernels and cokernels, computed on underlying
internal modules. None of these constructions requires compactness of J.
If I is K-injective and C is acyclic, transpose any map C to U(I) to a map
Ind(C) to I. Exactness makes Ind(C) acyclic. A null homotopy of this transpose
transports back through the termwise adjunction to a null homotopy of the original
map. This is precisely K-injectivity of U(I), with no boundedness assumption. -/
theorem forgetResidual_preservesKInjectiveComplexes
    (A : CondensedBar.Ring.{u}) (G J : Type u)
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    [Group J] [TopologicalSpace J] [IsTopologicalGroup J] :
    (forgetResidual A G J).PreservesKInjectiveComplexes := by sorry

end CategoryTheory.RelativeCyclic
