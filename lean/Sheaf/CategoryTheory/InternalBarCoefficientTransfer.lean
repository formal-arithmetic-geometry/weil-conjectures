/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F4
-/
module

public import Sheaf.CategoryTheory.CondensedEquivariantBarData
public import Mathlib.Topology.Algebra.OpenSubgroup
public import Mathlib.GroupTheory.Index
public import Mathlib.Algebra.Homology.Homotopy

/-! # Finite-index transfer for a single internal coefficient module

The coefficient-level part of the internal bar transfer argument. There is no coefficient
complex or second differential in this statement.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace CategoryTheory.CondensedBar

/-- Restriction, transfer and a natural homotopy for the bar cochains of individual
coefficient modules. This is the finite-coset construction before application to a complex.

Source: blueprint direct-image proof paragraph (3), internal finite-index transfer
argument, steps 1--4 (blueprint: lem-sfb-internal-bar-coefficient-transfer).
Proof: choose a finite right-coset transversal S containing 1, with continuous H-equivariant
retraction rho. In homogeneous coordinates define transfer on generalized functions by
sum over s in S of s inverse acting on F(rho(s x_0),...,rho(s x_p)). The coset permutation
reindexes this finite sum and proves homogeneity; for variable group sections partition the
test set into the finite clopen fibers of that permutation. The formula commutes with
alternating deletion. The composite with restriction is the sum of pullbacks along
x ↦ s inverse rho(s x). Sum the vertex prisms from the identity to these maps. Their
boundary is this composite minus the number of cosets times the identity. The same coset
reindexing proves that the sum of prisms preserves homogeneous sections. Conjugate by the
homogeneous/inhomogeneous coordinate isomorphisms. Substitution, addition and action
commute with every equivariant coefficient morphism; hence both chain maps and all homotopy
components are natural in the coefficient. The coordinate restriction formula gives the
stated evaluation. These are internal module morphisms, so the formulas hold over the
whole profinite slice. In degree zero use the prism boundary F(v(x))-F(x); there is no
negative-degree term. For H=G choose the identity transversal and zero homotopy. No scalar
is inverted, so zero coefficients and the zero ring are included. -/
theorem internal_bar_coefficient_transfer (A : Ring.{u}) (G : Type u)
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    [TotallyDisconnectedSpace G] (H : OpenSubgroup G) [CompactSpace H.toSubgroup]
    (F : InternalFunctions A) (B : BarDiagram (G := G) F)
    (BH : BarDiagram (G := H.toSubgroup) F) :
    let v : H.toSubgroup →ₜ* G :=
      { H.toSubgroup.subtype with continuous_toFun := continuous_subtype_val }
    ∃ r : cochains B ⟶ Profinite.CondensedAction.inflate (R := A.toMon) v ⋙ cochains BH,
    ∃ t : Profinite.CondensedAction.inflate (R := A.toMon) v ⋙ cochains BH ⟶ cochains B,
    ∃ h : ∀ N : Equivariant A G,
      Homotopy (r.app N ≫ t.app N) (H.toSubgroup.index • 𝟙 ((cochains B).obj N)),
      (∀ (N : Equivariant A G) (p : ℕ) (S : Profinite.{u})
        (x : sections A ((F.functor (power G p)).obj N.module) S)
        (T : Profinite.{u}) (f : T ⟶ S) (g : C(T, power H.toSubgroup p)),
        (F.evaluate (power H.toSubgroup p) S N.module
          (((B.term N p).inv ≫ (r.app N).f p ≫
            (BH.term
              ((Profinite.CondensedAction.inflate (R := A.toMon) v).obj N) p).hom).hom.hom.app
              (op S) x)).val T f g =
        (F.evaluate (power G p) S N.module x).val T f
          (ContinuousMap.comp
            ⟨fun x i ↦ (x i : G), continuous_pi fun i ↦
              continuous_subtype_val.comp (continuous_apply i)⟩ g)) ∧
      (∀ (N P : Equivariant A G) (f : N ⟶ P) (i j : ℕ),
        ((cochains B).map f).f i ≫ (h P).hom i j =
          (h N).hom i j ≫ ((cochains B).map f).f j) := by sorry

end CategoryTheory.CondensedBar
