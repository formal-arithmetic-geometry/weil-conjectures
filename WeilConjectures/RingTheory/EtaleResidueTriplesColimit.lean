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
import WeilConjectures.RingTheory.EtaleResidueTriplesFiltered
import WeilConjectures.RingTheory.EtaleResidueTriplesExistsColimit

/-!
# Filtered colimit of pointed etale algebras

The category of pointed étale residue triples over `(R, p)` with values in a separable closure
`K` of the residue field is filtered, and its ring diagram has a colimit with compatible maps
from `R` and to `K`.

## Implementation details

Tensor products supply common successors; for parallel maps `S → S'` the ring
`(S' ⊗[S] S') ⊗[S' ⊗[R] S'] S'` equalizes them. The category of triples is essentially
small, since affine étale `R`-schemes form an essentially small category, so the colimit exists.

## References

* Stacks Project, Algebra, Tags 04GW, 00D5
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- The category of étale residue triples with values in a separable closure `K` is filtered,
and its ring diagram has a colimit `c` with a map `ρ : R ⟶ c.pt` compatible with the structure
maps and a map `ψ : c.pt →+* K` compatible with the residue maps of the triples. -/
theorem etaleResidueTriples_filtered_colimit
    (R : CommRingCat.{u}) (p : Spec R) (K : Type u) [Field K]
    [Algebra ((Spec R).residueField p) K] [IsSepClosure ((Spec R).residueField p) K] :
    IsFiltered (EtaleResidueTriples R p K
      (CommRingCat.ofHom (algebraMap ((Spec R).residueField p) K))) ∧
    ∃ c : Cocone (etaleResidueTriplesRingDiagram R p K
      (CommRingCat.ofHom (algebraMap ((Spec R).residueField p) K))),
      Nonempty (IsColimit c) ∧ ∃ (ρ : R ⟶ c.pt) (ψ : c.pt →+* K),
        (∀ t, t.α ≫ c.ι.app t = ρ) ∧
        (∀ t, ψ.comp (c.ι.app t).hom =
          ((ΓSpecIso t.B).inv ≫ (Spec t.B).Γevaluation t.q ≫ t.φ).hom) := by
  exact ⟨etaleResidueTriples_filtered_part R p K
      (CommRingCat.ofHom (algebraMap ((Spec R).residueField p) K)),
    etaleResidueTriples_exists_colimit_part R p K⟩

end AlgebraicGeometry.Scheme
