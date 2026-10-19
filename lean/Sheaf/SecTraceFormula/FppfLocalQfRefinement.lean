/-
Copyright (c) 2026 The SHEAF contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import WeilConjectures.AlgebraicGeometry.QuasiFiniteMorphism
import Sheaf.TraceFormula.FppfLocalQfNeighbourhood

/-!
# Locally quasi-finite refinements of fppf coverings

Source: Stacks Project, More on Morphisms, Tag 0572, lemma-qf-fp-flat-dominates-fppf
(blueprint: lem-trf-fppf-local-qf-refinement).

## Main statements

* `exists_fppf_localQf_refinement` states that every small fppf covering admits a
  jointly surjective refinement by flat, locally finitely presented, locally
  quasi-finite morphisms.
-/

universe u

@[expose] public section

open CategoryTheory
open AlgebraicGeometry

namespace AlgebraicGeometry

/-- An fppf covering admits a small jointly-surjective refinement by flat, locally finitely
presented, locally quasi-finite morphisms, with each refinement member factoring through a member
of the original covering. Source: Stacks Project, More on Morphisms, Tag 0572
(blueprint: lem-trf-fppf-local-qf-refinement). -/
theorem exists_fppf_localQf_refinement
    (S : Scheme.{u}) (I : Type u) (Sᵢ : I → Scheme.{u})
    (f : ∀ i : I, Sᵢ i ⟶ S)
    (hf : ∀ i : I, Flat (f i))
    (hfp : ∀ i : I, LocallyOfFinitePresentation (f i))
    (hcover : ∀ s : S, ∃ i : I, ∃ x : Sᵢ i, f i x = s) :
    ∃ (J : Type u) (T : J → Scheme.{u}) (g : ∀ j : J, T j ⟶ S)
      (hflat : ∀ j : J, Flat (g j))
      (hfp' : ∀ j : J, LocallyOfFinitePresentation (g j))
      (hqf : ∀ j : J, Scheme.Hom.IsLocallyQuasiFinite (g j))
      (ι : J → I) (h : ∀ j : J, T j ⟶ Sᵢ (ι j)),
      (∀ j : J, h j ≫ f (ι j) = g j) ∧
      (∀ s : S, ∃ j : J, ∃ x : T j, g j x = s) := by
  sorry

end AlgebraicGeometry

end
