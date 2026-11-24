/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleResidueTriples
public import Mathlib.RingTheory.Localization.AtPrime.Basic

/-! # Compatible cocone legs across prime localization

The compatibility relation between cocones on the pointed étale ring diagrams over `(R, p)`
and over the localization `R_p`.

## References

* [Stacks: Tag 04GW](https://stacks.math.columbia.edu/tag/04GW)
* [Stacks: Tag 00CR](https://stacks.math.columbia.edu/tag/00CR)
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme
/-- A cocone `η` over `(R, p)` and a cocone `θ` over `R_p` with the same vertex are compatible
if `β ≫ θ.app t = η.app s` for every pointed `R`-algebra map `β` from a triple `s` over
`(R, p)` to a triple `t` over `R_p`. -/
def etaleResidueTriples_primeLocalization_coconeRelation
    (R : CommRingCat.{u}) (p : Spec R) (K : Type u) [Field K]
    (χ : (Spec R).residueField p ⟶ CommRingCat.of K)
    (q : Spec (CommRingCat.of (Localization.AtPrime p.asIdeal)))
    (ψ : (Spec (CommRingCat.of (Localization.AtPrime p.asIdeal))).residueField q ⟶
      CommRingCat.of K)
    (V : CommRingCat.{u})
    (η : etaleResidueTriplesRingDiagram R p K χ ⟶ (Functor.const _).obj V)
    (θ : etaleResidueTriplesRingDiagram
      (CommRingCat.of (Localization.AtPrime p.asIdeal)) q K ψ ⟶
        (Functor.const _).obj V) : Prop :=
  ∀ (s : EtaleResidueTriples R p K χ)
    (t : EtaleResidueTriples (CommRingCat.of (Localization.AtPrime p.asIdeal)) q K ψ)
    (β : s.B ⟶ t.B),
    s.α ≫ β = CommRingCat.ofHom (algebraMap R (Localization.AtPrime p.asIdeal)) ≫ t.α →
    β ≫ (ΓSpecIso t.B).inv ≫ (Spec t.B).Γevaluation t.q ≫ t.φ =
      (ΓSpecIso s.B).inv ≫ (Spec s.B).Γevaluation s.q ≫ s.φ →
    β ≫ θ.app t = η.app s

end AlgebraicGeometry.Scheme
