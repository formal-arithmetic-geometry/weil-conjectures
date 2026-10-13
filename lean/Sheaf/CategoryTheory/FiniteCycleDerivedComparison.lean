/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K3
-/
module

public import Sheaf.CategoryTheory.ExactCoupleConvergence

/-!
# The original-g comparison with a finite derived couple

Source: blueprint thm-sp-half-plane-convergence, proof paragraph 2;
Stacks Project, Tags 011R and 0AMJ.
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.BigradedExactCouple

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- The lift of the alpha iterate into the recursively included derived D term,
followed by derived g, is original g followed by the canonical cycle projection.

Proof: First construct canonical image epimorphisms e_n recursively, starting with
identity and endpoint transport. At n+1 compose e_n with the image epimorphism of
incoming alpha on page n, with source (p-n,q+n) and target (p-n-1,q+n+1).
Induction on hIs, using DerivedMaps.alpha_comm, gives I_n compatibility with original
alpha. Therefore e_n followed by I_n is the n-fold outgoing alpha iterate. The
appended-alpha recurrence equals alphaIter's prepended-alpha recurrence by induction
and associativity. Monicity of I_n shows any e satisfying he equals this e_n.
Induct on n to compare g. The base is hI0, projection_zero and factorThru_arrow.
At a successor, Z_decreasing gives the factorization of initialG through Z_n from
its factorization through Z_(n+1). The latter lift followed by ofLE equals the former
lift: compose with the monic arrow of Z_n and use ofLE_arrow and factorThru_arrow.
DerivedMaps.g_comm expresses e_(n+1) followed by g_(n+1) as e_n followed by the
transported gToCycles and derivedEProjection. The induction hypothesis identifies
e_n followed by g_n with the former cycle lift followed by projection n.
The latter cycle lift followed by cycleLift has the same composite with kernel.ι:
use cycleLift_comm and the equality of the two lifts just proved. Cancel this monic
kernel inclusion to identify it with e_n followed by gToCycles. Finish by composing
with derivedEProjection and using projection_succ. Endpoint transports are eqToHom
maps; associativity and eqToHom composition identify the resulting target with (p,q).
Finally cancel I_n to replace the recursive image epimorphism by the supplied e.
No vanishing, positivity or colimit hypothesis is needed. At n=0 this is the initial
projection identity; the zero category satisfies the same equations.
Source: blueprint thm-sp-half-plane-convergence, proof paragraph 2, original-g
projection through successive images; Stacks Tags 011R and 0AMJ. The induction is
an agent-written expansion of these sources' induced-g construction.
(blueprint: lem-sp-finite-cycle-derived-comparison) -/
theorem finiteCycle_derived_comparison (X : BigradedExactCouple C 0)
    (I : ∀ (n : ℕ) (p q : ℤ), (X.pageCouple n).D p q ⟶ X.D p q)
    (hI0 : ∀ p q : ℤ, I 0 p q = 𝟙 _)
    (hIs : ∀ (n : ℕ) (p q : ℤ), I (n + 1) p q =
      (X.pageCouple n).derivedDInclusion p q ≫ I n p q)
    (hImono : ∀ (n : ℕ) (p q : ℤ), Mono (I n p q))
    (r : ℕ) (p q : ℤ)
    (hg : (X.cycleBoundaryTower.Z r p q).Factors (X.initialG p q))
    (e : X.D p q ⟶ (X.pageCouple r).D (p - r) (q + r))
    (he : e ≫ I r (p - r) (q + r) = X.alphaIter r p q) :
    e ≫ (X.pageCouple r).g (p - r) (q + r) ≫
        eqToHom (by congr 1 <;> omega) =
      (X.cycleBoundaryTower.Z r p q).factorThru (X.initialG p q) hg ≫
        X.cycleBoundaryTower.projection r p q := by sorry

end CategoryTheory.BigradedExactCouple
