/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.WeaklyContractible
public import WeilConjectures.CategoryTheory.Sites.FiniteDisjointCover

/-!
# Finite disjoint refinements over w-contractible affine schemes

Let `W` be an object of the small pro-étale site of a scheme whose underlying scheme is the
spectrum of a w-contractible ring. Every covering sieve of `W` contains the members of a finite
cover of `W` by pairwise disjoint open immersions
(`AlgebraicGeometry.Scheme.ProEt.hasFiniteDisjointRefinements_of_iso`); this is the finite form
of `AlgebraicGeometry.Scheme.ProEt.isWeaklyContractible_of_iso`. Moreover every scheme admits a
pro-étale cover by spectra of w-contractible rings
(`AlgebraicGeometry.Scheme.exists_isWContractibleRing_cover`).
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry

namespace Scheme.ProEt

variable {T : Scheme.{u}}

/-- Let `W` be an object of the small pro-étale site whose underlying scheme admits a section
`s` of a morphism `∐ V j ⟶ W.left`. The preimages under `s` of the components `V j` form a
disjoint cover of `W`, indexed by the same type, by members of every sieve `S` containing the
morphisms to `W` factoring through some `V j`. -/
lemma isDisjointCover_of_comp_sigmaDesc_eq_id {W : T.ProEt} {κ : Type u}
    {V : κ → Scheme.{u}} (v : ∀ j, V j ⟶ W.left) (s : W.left ⟶ ∐ V)
    (hs : s ≫ Sigma.desc v = 𝟙 _) (S : Sieve W)
    (hS : ∀ j {Y : T.ProEt} (a : Y ⟶ W) (b : Y.left ⟶ V j), b ≫ v j = a.left → S a) :
    ∃ (Y : κ → T.ProEt) (f : ∀ i, Y i ⟶ W),
      (topology T).IsDisjointCover f ∧ ∀ i, S (f i) := by
  let O (j : κ) : W.left.Opens := s ⁻¹ᵁ (Sigma.ι V j).opensRange
  have hO (j : κ) : Set.range ((O j).ι ≫ s).base ⊆ Set.range (Sigma.ι V j).base := by
    rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, Opens.range_ι]
    rintro _ ⟨x, hx, rfl⟩
    exact hx
  refine ⟨fun j ↦ ofOpenImmersion W (O j).ι, fun j ↦ ofOpenImmersionHom W (O j).ι,
    ⟨?_, fun j ↦ ?_, ?_⟩, fun j ↦ hS j _ (IsOpenImmersion.lift (Sigma.ι V j) ((O j).ι ≫ s)
      (hO j)) ?_⟩
  · refine mem_topology_of_openImmersion _ (fun j ↦ (O j).ι) (fun x ↦ ?_)
      (fun j ↦ Sieve.ofArrows_mk _ _ j)
    obtain ⟨j, y, hy⟩ := (sigmaOpenCover V).exists_eq (s x)
    refine ⟨j, ?_⟩
    rw [Opens.range_ι]
    exact ⟨y, hy⟩
  · refine (ProEt.forget T ⋙ CategoryTheory.Over.forget T).mono_of_mono_map ?_
    exact inferInstanceAs (Mono (O j).ι)
  · intro i j hij Z a b hab
    have : IsEmpty Z.left := by
      refine ⟨fun z ↦ ?_⟩
      have hab' : a.left ≫ (O i).ι = b.left ≫ (O j).ι := congrArg (fun g ↦ g.left) hab
      have hi : (a.left ≫ (O i).ι).base z ∈ O i := by
        exact (Opens.range_ι (O i)).subset ⟨a.left z, rfl⟩
      have hj : (a.left ≫ (O i).ι).base z ∈ O j := by
        rw [hab']
        exact (Opens.range_ι (O j)).subset ⟨b.left z, rfl⟩
      exact (disjoint_opensRange_sigmaι V i j hij).le_bot ⟨hi, hj⟩
    exact bot_mem_topology Z
  · rw [← Sigma.ι_desc v j, ← Category.assoc, IsOpenImmersion.lift_fac, Category.assoc, hs,
      Category.comp_id]
    rfl

end Scheme.ProEt

end AlgebraicGeometry
