/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E2
-/
module

public import Sheaf.AlgebraicGeometry.EtaleResidueTriples
public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.FieldTheory.IsSepClosed

/-! Construction of a finite etale stage carrying a prescribed simple root.

Source: Stacks Project, Algebra, Tags 04GN and 04GP.
(blueprint: lem-weil-pbc-etale-triples-colimit-simple-roots-construction)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- The finite stage construction in the proof of the simple-root lifting lemma.
The polynomial and its root descend to one pointed etale residue triple; the
universal root in that stage maps to the prescribed simple root in `K`.
Source: Stacks Project, Algebra, Tags 04GN and 04GP.
Proof: Filteredness descends the coefficients and simple-root data to one pointed
etale residue triple.
Adjoin a universal root using the standard etale algebra for a monic polynomial and its
invertible derivative, then use the root in K to define a residue embedding. The induced
triple morphism supplies the stage element, whose polynomial equation and image in K
follow by functoriality.
(blueprint: lem-weil-pbc-etale-triples-colimit-simple-roots-construction) -/
theorem etaleResidueTriples_simple_root_stage
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
      ∃ t : EtaleResidueTriples R p K
          (CommRingCat.ofHom (algebraMap ((Spec R).residueField p) K)),
        ∃ x : t.B, f.IsRoot (c.ι.app t x) ∧ ψ (c.ι.app t x) = a₀ := by
  sorry

end AlgebraicGeometry.Scheme
