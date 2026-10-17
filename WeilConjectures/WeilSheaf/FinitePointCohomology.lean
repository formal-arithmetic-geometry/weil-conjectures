/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import WeilConjectures.WeilSheaf.Cohomology
public import WeilConjectures.WeilSheaf.StalkFrobenius

/-!
# Weil sheaves on a finite étale `k₀`-scheme

Let `P` be a finite étale `k₀`-scheme, for instance the spectrum of the residue field of a closed
point of a `k₀`-scheme of finite type. Its geometric fiber `P̄ = P ⊗ k̄` is a finite disjoint union
of copies of `Spec k̄`. For a Weil sheaf `G` on `P`:

- the global sections `Γ(P̄, G)` surject onto every geometric stalk, Frobenius-equivariantly for
  the local Frobenius `F_x = Fr^{deg x}` at a closed point `x`, so every eigenvalue of `F_x` is the
  `deg x`-th power of an eigenvalue of the Frobenius of `Γ(P̄, G)`
  (`AlgebraicGeometry.WeilSheaf.exists_hasEigenvalue_globalSections_of_hasEigenvalue_stalk`);
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.WeilSheaf

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
  {P : Scheme.{u}} [P.Over (Spec (CommRingCat.of k₀))]
  [IsFinite (P ↘ Spec (CommRingCat.of k₀))] [Etale (P ↘ Spec (CommRingCat.of k₀))]

/-- On a finite étale `k₀`-scheme `P`, every eigenvalue `β` of the local Frobenius `F_x` of a
Weil sheaf `G` at a closed point `x` is `α ^ deg x` for an eigenvalue `α` of the Frobenius of the
global sections `Γ(P̄, G)`: the restriction `Γ(P̄, G) ⟶ G_x̄` is surjective, `x̄` being a clopen
point of the finite discrete scheme `P̄`, and it intertwines `Fr^{deg x}` with `F_x`. -/
theorem exists_hasEigenvalue_globalSections_of_hasEigenvalue_stalk (G : WeilSheaf k₀ l P)
    (x : P.finitePoints) {β : PadicAlgCl l} (hβ : (G.stalk x).frobeniusEnd.HasEigenvalue β) :
    ∃ α : PadicAlgCl l, G.globalSections.frobeniusEnd.HasEigenvalue α ∧
      α ^ (P ↘ Spec (CommRingCat.of k₀)).degreeOver x.1 = β :=
  sorry

/-- On a finite étale `k₀`-scheme `P`, if the global sections `Γ(P̄, G)` of a Weil sheaf are
`ι`-pure of weight `w` over `k₀`, then `G` is punctually `ι`-pure of weight `w`: an eigenvalue of
`F_x` is `α ^ deg x` with `|ι α| = q^{w/2}`, and `q_x = q ^ deg x`. -/
theorem isPunctuallyPureOfWeight_of_isPureOfWeightOver_globalSections {ι : PadicAlgCl l →+* ℂ}
    {G : WeilSheaf k₀ l P} {w : ℝ} (h : G.globalSections.IsPureOfWeightOver k₀ ι w) :
    G.IsPunctuallyPureOfWeight ι w :=
  sorry

end AlgebraicGeometry.WeilSheaf
