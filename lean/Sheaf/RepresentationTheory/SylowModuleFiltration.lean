/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF worker K1
-/
module

public import Sheaf.RepresentationTheory.DiscreteContinuousRep
public import Mathlib.GroupTheory.PGroup
public import Mathlib.GroupTheory.Index
public import Mathlib.Topology.Algebra.OpenSubgroup
public import Mathlib.Topology.Connected.TotallyDisconnected
import Sheaf.RepresentationTheory.DiscreteContinuousCohomology
import WeilConjectures.Mathlib.RepresentationTheory.Invariants

/-!
# Sylow reduction of finite primary discrete modules

Source: blueprint `sec-curve-estimates/sk-prop-h2/lem-sc-sylow-module-filtration`;
Stacks Project, Tags 0A3R, 0GIZ and 0GJ0 (blueprint: lem-sc-sylow-module-filtration).
-/

@[expose] public section

universe u v

namespace Rep

/-- A finite `ℓ`-primary discrete continuous module admits an open subgroup of index
prime to `ℓ` and an invariant finite filtration with trivial `𝔽_ℓ` successive quotients.
The quotient clauses are expressed without choosing scalar structures: `ℓ • x` lies in
the preceding term, so that the quotient is canonically a `ZMod ℓ`-module, and `g x - x`
lies in the preceding term, so that the induced action is trivial. There is no rank
condition on the quotients. Repeated terms, including the zero module's one-term chain,
are allowed.

Proof: (1) Intersect the finitely many open stabilizers supplied by
`def-exc-continuous-cohomology` to obtain the open normal kernel of the action.
Compactness makes its quotient finite, including when the module is zero.
(2) Choose an `ℓ`-Sylow subgroup of that quotient using
`lem-weil-pbc-sylow-subgroup-prime-index`. Its inverse image is open and has the same
prime-to-`ℓ` index; the restricted action factors through a finite `ℓ`-group.
(3) Finiteness and primary torsion give an exponent `ℓ^n` annihilating the module.
The annihilators of successive powers form an invariant filtration with quotients
killed by `ℓ`, hence finite-dimensional `𝔽_ℓ` representations.
(4) Apply `lemma-weil-pbc-finite-l-group-filtration` to each nonzero quotient.
Pull back its invariant filtration and concatenate the resulting chains. Each
successive quotient is killed by `ℓ` and has trivial action. Zero intermediate
quotients need no refinement; for the zero module use the one-term chain.

Source: blueprint `sec-curve-estimates/sk-prop-h2/lem-sc-sylow-module-filtration`;
Stacks Project, Tags 0A3R, 0GIZ and 0GJ0 (blueprint: lem-sc-sylow-module-filtration). -/
theorem exists_openSubgroup_primary_module_filtration
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (ℓ : ℕ) (hℓ : ℓ.Prime) (M : DiscreteContinuousRep.{0, u, v} ℤ G)
    [Finite M.obj.V] (hM : IsPGroup ℓ (Multiplicative M.obj.V)) :
    ∃ H : OpenSubgroup G, H.toSubgroup.index.Coprime ℓ ∧
      ∃ (n : ℕ) (F : Fin (n + 1) → AddSubgroup M.obj.V),
        Monotone F ∧ F 0 = ⊥ ∧ F (Fin.last n) = ⊤ ∧
        (∀ (i : Fin (n + 1)) (g : H) (x : M.obj.V),
          x ∈ F i → M.obj.ρ (g : G) x ∈ F i) ∧
        (∀ (i : Fin n) (x : M.obj.V), x ∈ F i.succ →
          ℓ • x ∈ F i.castSucc ∧
            ∀ g : H, M.obj.ρ (g : G) x - x ∈ F i.castSucc) := by
  sorry

end Rep
