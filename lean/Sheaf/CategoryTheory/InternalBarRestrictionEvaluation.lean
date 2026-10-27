/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group T3
-/
module

public import Sheaf.CategoryTheory.InternalHomogeneousCochainCoordinateData

/-! # Restriction of internal bar cochains

Source: the internal sheaf adaptation of the displayed bar differential of Stacks 0DVG.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace CategoryTheory.CondensedBar

/-- Precomposition by a continuous group homomorphism gives an internal cochain
restriction map with its specified evaluation on every profinite slice.
Source: Stacks 0DVG, internal adaptation, restriction calculation
(blueprint: lem-sfb-internal-bar-restriction-evaluation).

Proof: for each coefficient object and degree, precompose the evaluation family by the
map on tuples induced by v. This is natural under every further base change. The
internal-function evaluation equivalence constructs the section; its additivity and
scalar laws give linear maps, natural in the test object. Lift them through the
section-module equivalence and conjugate by the recorded bar-term isomorphisms.
Coefficient naturality is the bar-term map law and evaluation map law. For the cochain
identity, precomposition commutes with each face: the initial action is the inflated
action by v(g₀), interior faces use v(gh)=v(g)v(h), and the final face just omits the
last entry. Thus it commutes with the alternating sum of faces. The identity holds also
in degree zero, for the trivial group, and on empty profinite test objects. -/
theorem exists_internalBarRestrictionEvaluation {A : Ring.{u}} (F : InternalFunctions A)
    (K J : ProfiniteGrp.{u}) (v : K →ₜ* J)
    (BJ : BarDiagram (G := J) F) (BK : BarDiagram (G := K) F) :
    ∃ r : cochains BJ ⟶ Profinite.CondensedAction.inflate v ⋙ cochains BK,
      ∀ (M : Equivariant A J) (n : ℕ) (S : Profinite.{u})
        (x : sections A (((cochains BJ).obj M).X n) S)
        (T : Profinite.{u}) (f : T ⟶ S) (g : Fin n → C(T, K)),
        inhomogeneousCoordinateValue BK ((Profinite.CondensedAction.inflate v).obj M)
            n S (((r.app M).f n).hom.hom.app (op S) x) T f g =
          inhomogeneousCoordinateValue BJ M n S x T f
            (fun i ↦ v.toContinuousMap.comp (g i)) := by sorry

end CategoryTheory.CondensedBar
