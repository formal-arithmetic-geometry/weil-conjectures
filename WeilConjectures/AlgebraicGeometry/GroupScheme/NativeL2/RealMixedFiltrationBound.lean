/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.GroupScheme.NativeL2.L2NativePunctualWeights
import Mathlib.Data.Set.Finite.Lattice

/-! # A common bound for a finite pure Weil filtration

Source: latest blueprint, `thm-zl-real-mixed-by-curves.proof.md`, paragraphs 4 and 9.
(blueprint: lem-zl-real-mixed-filtration-bound)
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj

namespace WeilConjectures.NativeL2

/-- A finite constructible Weil filtration whose quotients each have a real pure weight
has one common real upper weight bound. This includes the length-zero filtration.

Source: latest blueprint, `thm-zl-real-mixed-by-curves.proof.md`, paragraphs 4 and 9.
(blueprint: lem-zl-real-mixed-filtration-bound)

Proof: choose a pure weight for each of the finitely many quotients. The finite image of
these real weights is bounded above, including when it is empty. Use this upper bound
in the definition of mixedness, retaining the given terms, arrows and endpoint. -/
theorem exists_mixed_of_pure_quotients
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
    (X₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    (M : WeilModule D l X₀) (iota : PadicAlgCl l →+* ℂ)
    (n : ℕ) (G : Fin (n + 1) → WeilModule D l X₀)
    (φ : ∀ i : Fin n, G i.castSucc ⟶ G i.succ)
    (hc : ∀ i, IsConstantModelConstructible (Profinite.padicAlgClRingObj l)
      (D.geometricFiber X₀).left (G i).carrier)
    (hz : IsZero (G 0)) (he : Nonempty (G (Fin.last n) ≅ M))
    (hm : ∀ i, Mono (φ i))
    (hp : ∀ i : Fin n, ∃ v : ℝ, Pure D l X₀ (cokernel (φ i)) iota v) :
    ∃ w : ℝ, Mixed D l X₀ M iota w := by
  classical
  choose v hv using hp
  obtain ⟨w, hw⟩ := (Set.finite_range v).bddAbove
  refine ⟨w, n, G, φ, hc, hz, he, hm, ?_⟩
  intro i
  exact ⟨v i, hw (Set.mem_range_self i), hv i⟩

end WeilConjectures.NativeL2
