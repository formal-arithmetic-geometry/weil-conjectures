/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleResidueTriples
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.FieldTheory.IsSepClosed
import WeilConjectures.RingTheory.EtaleResidueTriplesPolynomialLift

/-!
# The residue map of the pointed etale colimit is surjective

If the residue map `ψ` from a colimit of pointed étale residue triples to a separable closure `K`
detects units and simple roots lift along it, then `ψ` is surjective.

## Implementation details

The image of `ψ` is a field containing the image of `κ(p)`. Each `α` in `K` is a simple root of
its separable minimal polynomial over `κ(p)`, whose coefficients are lifted to a monic polynomial
over the colimit; the root-lifting hypothesis then produces a preimage of `α`. Injectivity of
`R → c.pt` is not used, and the prime `p` need not be maximal.

## References

* [Stacks, Tag 04GW], last paragraph
* [Stacks, Tag 00UH]
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- Let `c` be a colimit of pointed étale residue triples with compatible map `ψ : c.pt → K`.
If every element with nonzero image under `ψ` is a unit and every simple root in `K` of a monic
polynomial over `c.pt` lifts to a root in `c.pt`, then `ψ` is surjective. -/
theorem etaleResidueTriples_colimit_surjective
    (R : CommRingCat.{u}) (p : Spec R) (K : Type u) [Field K]
    [Algebra ((Spec R).residueField p) K] [IsSepClosure ((Spec R).residueField p) K]
    (c : Cocone (etaleResidueTriplesRingDiagram R p K
      (CommRingCat.ofHom (algebraMap ((Spec R).residueField p) K))))
    (hc : IsColimit c)
    (ψ : c.pt →+* K)
    (hψ : ∀ t, ψ.comp (c.ι.app t).hom =
      ((ΓSpecIso t.B).inv ≫ (Spec t.B).Γevaluation t.q ≫ t.φ).hom)
    (hunit : ∀ x : c.pt, ψ x ≠ 0 → IsUnit x)
    (hroot : ∀ f : Polynomial c.pt, f.Monic → ∀ a₀ : K,
      f.eval₂ ψ a₀ = 0 → f.derivative.eval₂ ψ a₀ ≠ 0 →
        ∃ a : c.pt, f.IsRoot a ∧ ψ a = a₀) :
    Function.Surjective ψ := by
  intro a₀
  obtain ⟨f, hf, hfa, hfd⟩ :=
    etaleResidueTriples_polynomial_lift R p K c hc ψ hψ hunit a₀
  obtain ⟨a, ha, hₐ⟩ := hroot f hf a₀ hfa hfd
  exact ⟨a, hₐ⟩

end AlgebraicGeometry.Scheme
