/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.Replete
public import Mathlib.CategoryTheory.Sites.EpiMono

/-!
# Lifting sections along epimorphisms of sheaves on the affine pro-étale site

Let `g : G ⟶ H` be an epimorphism of abelian sheaves on the affine pro-étale site `S.AffineProEt`
and `s` a section of `H` over `V`. Then `s` lifts to `G` after pulling back along a single
surjection `W ⟶ V`: the image sieve of `s` contains a finite jointly surjective family, which
factors through its disjoint union `W`, and the local lifts glue over the pairwise disjoint
pieces of `W`.

## Main statements

* `AlgebraicGeometry.Scheme.AffineProEt.exists_surjective_factorization_disjoint`: a finite
  jointly surjective family factors through a single surjection, with pairwise disjoint pieces.
* `AlgebraicGeometry.Scheme.AffineProEt.exists_surjective_lift_of_epi`: sections of an
  epimorphism of abelian sheaves lift after pullback along a single surjection.
* `AlgebraicGeometry.Scheme.AffineProEt.ofArrows_mem_topology_of_surjective`: a single surjection
  generates a covering sieve.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.Scheme.AffineProEt

variable {S : Scheme.{u}}

/-- Distinct components of the disjoint union `Spec (∏ᵢ Γ(V i))` have disjoint images. -/
lemma disjoint_range_sigmaCoverι {X : S.AffineProEt} {ι : Type u} [Finite ι]
    (V : ι → S.AffineProEt) (f : ∀ i, V i ⟶ X) {i k : ι} (hik : i ≠ k) :
    Disjoint (Set.range (sigmaCoverι V f i).left.base)
      (Set.range (sigmaCoverι V f k).left.base) := by
  rw [Set.disjoint_left]
  rintro _ ⟨a, rfl⟩ ⟨b, hb⟩
  obtain ⟨p, -, -⟩ := exists_left_base_preimage
    (IsPullback.of_hasPullback (sigmaCoverι V f i) (sigmaCoverι V f k)) a b hb.symm
  exact (isEmpty_of_sigmaCoverι_eq V f hik _ _ pullback.condition).elim p

/-- Given a finite jointly surjective family `f i : V i ⟶ X` in the affine pro-étale site, the
family factors through a single surjection `q : W ⟶ X` such that the pieces `j i : V i ⟶ W` form
a Zariski cover of `W` by pairwise disjoint open subschemes. -/
lemma exists_surjective_factorization_disjoint {X : S.AffineProEt} {ι : Type u} [Finite ι]
    (V : ι → S.AffineProEt) (f : ∀ i, V i ⟶ X)
    (hsurj : ∀ x : X.left, ∃ i, x ∈ Set.range ((f i).left.base)) :
    ∃ (W : S.AffineProEt) (q : W ⟶ X) (j : ∀ i, V i ⟶ W),
      Surjective q.left ∧ (∀ i, j i ≫ q = f i) ∧ (∀ i, IsOpenImmersion (j i).left) ∧
      (∀ w : W.left, ∃ i, w ∈ Set.range ((j i).left.base)) ∧
      ∀ i k, i ≠ k → Disjoint (Set.range (j i).left.base) (Set.range (j k).left.base) :=
  ⟨sigmaCover V f, sigmaCoverπ V f, sigmaCoverι V f, surjective_sigmaCoverπ V f hsurj,
    sigmaCoverι_π V f, isOpenImmersion_sigmaCoverι V f, exists_mem_range_sigmaCoverι V f,
    fun _ _ ↦ disjoint_range_sigmaCoverι V f⟩


end AlgebraicGeometry.Scheme.AffineProEt
