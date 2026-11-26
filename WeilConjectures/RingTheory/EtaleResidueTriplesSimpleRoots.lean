/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleResidueTriples
public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.FieldTheory.IsSepClosed
import WeilConjectures.RingTheory.EtaleResidueTriplesSimpleRootsConstruction

/-!
# Simple roots lift in the pointed etale colimit

For a colimit of pointed étale residue triples with residue map `ψ` to a separable closure `K`,
every simple root in `K` of a monic polynomial over the colimit lifts to a root in the colimit.

## Implementation details

The coefficients and the root are carried to a single finite stage by
`etaleResidueTriples_simple_root_stage`, where a universal root is adjoined via the standard
étale algebra `S[T, 1/Q']/(Q)`.

## References

* [Stacks, Tag 04GN], last paragraph
* [Stacks, Tag 04GP]
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- Let `c` be a colimit of pointed étale residue triples with compatible map `ψ : c.pt → K`.
Every monic polynomial `f` over `c.pt` with a simple root `a₀` in `K` under `ψ` has a root `a`
in `c.pt` with `ψ a = a₀`. -/
theorem etaleResidueTriples_colimit_simple_roots
    (R : CommRingCat.{u}) (p : Spec R) (K : Type u) [Field K]
    [Algebra ((Spec R).residueField p) K] [IsSepClosure ((Spec R).residueField p) K]
    (c : Cocone (etaleResidueTriplesRingDiagram R p K
      (CommRingCat.ofHom (algebraMap ((Spec R).residueField p) K))))
    (hc : IsColimit c)
    (ψ : c.pt →+* K)
    (hψ : ∀ t, ψ.comp (c.ι.app t).hom =
      ((ΓSpecIso t.B).inv ≫ (Spec t.B).Γevaluation t.q ≫ t.φ).hom) :
    ∀ f : Polynomial c.pt, f.Monic → ∀ a₀ : K,
      f.eval₂ ψ a₀ = 0 → f.derivative.eval₂ ψ a₀ ≠ 0 →
        ∃ a : c.pt, f.IsRoot a ∧ ψ a = a₀ := by
  intro f hf a₀ hfa hdfa
  obtain ⟨t, x, hx, hψx⟩ :=
    etaleResidueTriples_simple_root_stage R p K c hc ψ hψ f hf a₀ hfa hdfa
  exact ⟨c.ι.app t x, hx, hψx⟩

end AlgebraicGeometry.Scheme
