/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FiniteEtale

/-!
# Sections over disjoint unions on the small étale site

The sections of an étale sheaf over an étale `X`-scheme `P` that is the disjoint union of open
subschemes `Uₛ` are the product of the sections over the `Uₛ`
(`AlgebraicGeometry.Scheme.Etale.existsUnique_of_pairwise_disjoint`). This generalises the
two-piece splitting `AlgebraicGeometry.Scheme.Etale.existsUnique_of_isCompl`. It is the first
step towards computing the pushforward along a trivial finite étale cover `∐ₛ U ⟶ U`, an
input to the constructibility of extensions by zero along étale maps [Stacks 03SA].
-/

@[expose] public section

universe u' u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.Scheme

variable {A : Type u'} [Category.{u + 1} A] {X : Scheme.{u}}
  (G : Sheaf X.smallEtaleTopology A) {P : X.Etale} {ι : Type u} (U : ι → X.Etale)
  (i : ∀ s, U s ⟶ P) [∀ s, IsOpenImmersion (i s).left]

/-- **Sections over a disjoint union.** The sections of a sheaf on the small étale site over `P`
are determined by their restrictions to a family of open subschemes of `P` with pairwise disjoint
images covering `P`, and any family of sections over them glues. -/
lemma Etale.existsUnique_of_pairwise_disjoint
    (hdisj : Pairwise fun s t ↦ Disjoint (Set.range (i s).left.base) (Set.range (i t).left.base))
    (hcov : ⋃ s, Set.range (i s).left.base = Set.univ) {a : A}
    (x : ∀ s, a ⟶ G.obj.obj (op (U s))) :
    ∃! σ : a ⟶ G.obj.obj (op P), ∀ s, σ ≫ G.obj.map (i s).op = x s := by
  have hcov' : Sieve.ofArrows U i ∈ X.smallEtaleTopology P := by
    rw [ofArrows_mem_smallEtaleTopology_iff]
    exact hcov
  have hsh := (G.property a).isSheafFor (Presieve.ofArrows U i) hcov'
  rw [Presieve.isSheafFor_arrows_iff] at hsh
  have hmono (s : ι) : Mono (i s) := ⟨fun g₁ g₂ hg ↦ MorphismProperty.Over.Hom.ext
    ((cancel_mono (i s).left).1 (congrArg (fun g ↦ g.left) hg :))⟩
  have hempty {T : X.Etale} {s t : ι} (hst : s ≠ t) (g₁ : T ⟶ U s) (g₂ : T ⟶ U t)
      (hg : g₁ ≫ i s = g₂ ≫ i t) : IsEmpty T.left := by
    refine ⟨fun z ↦ ?_⟩
    have h₁ : (i s).left (g₁.left z) = (i t).left (g₂.left z) := by
      rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply]
      exact congrArg (fun g ↦ g.left z) hg
    have h₂ : (i s).left (g₁.left z) ∈ Set.range (i t).left.base := ⟨_, h₁.symm⟩
    exact Set.disjoint_iff.1 (hdisj hst) ⟨⟨_, rfl⟩, h₂⟩
  obtain ⟨σ, hσ, hσu⟩ := hsh (fun s ↦ x s) (by
    intro s t T g₁ g₂ hg
    by_cases hst : s = t
    · subst hst
      obtain rfl : g₁ = g₂ := (cancel_mono (i s)).1 hg
      rfl
    · have := hempty hst g₁ g₂ hg
      exact (Etale.isTerminalSectionsOfIsEmpty G T).hom_ext _ _)
  exact ⟨σ, hσ, fun σ' hσ' ↦ hσu σ' hσ'⟩

end AlgebraicGeometry.Scheme
