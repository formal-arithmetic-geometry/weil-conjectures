/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Adic.LisseCover.RegularLattice

/-!
# Lattices of lisse sheaves on connected normal schemes

Let `T` be a connected Noetherian scheme whose local rings are integrally closed domains (a
connected normal Noetherian scheme), `f : V ⟶ T` a single-morphism pro-étale cover and
`γ : V ×_T V → GL_n(E)` a cocycle acting on the lattices of `Eⁿ` by a descent cocycle. Then `γ`
has a twisted section with values in the lattices
(`AlgebraicGeometry.exists_isTwistedSection_compactOpenLattice_of_isIntegrallyClosed_stalk`,
blueprint `lemma-global-lattice-normal-scheme`). The proof is that of the regular case
`AlgebraicGeometry.exists_isTwistedSection_compactOpenLattice_of_connectedSpace`, which only uses
the finiteness of the orbits of locally constant sheaves of sets on geometrically unibranch
schemes (`AlgebraicGeometry.exists_finite_invariant_subset_of_isIntegrallyClosed_stalk`).
-/

@[expose] public section

universe u

open CategoryTheory Limits PadicAlgCl

namespace AlgebraicGeometry

variable {l : ℕ} [Fact l.Prime] {E : IntermediateField ℚ_[l] (PadicAlgCl l)}
  [FiniteDimensional ℚ_[l] E] {n : ℕ} {T V : Scheme.{u}}

/-- **Lattices on connected normal schemes** (blueprint `lemma-global-lattice-normal-scheme`).
Let `T` be a connected Noetherian scheme whose local rings are integrally closed domains, and `γ`
a cocycle on a single-morphism pro-étale cover of `T` acting on the lattices of `Eⁿ` by a descent
cocycle. Then `γ` has a twisted section with values in the lattices: the orbit of the standard
lattice lies in a finite invariant set of lattices
(`AlgebraicGeometry.exists_finite_invariant_subset_of_isIntegrallyClosed_stalk`), whose sum is an
invariant lattice. -/
theorem exists_isTwistedSection_compactOpenLattice_of_isIntegrallyClosed_stalk
    [IsLocallyNoetherian T] [CompactSpace T] [ConnectedSpace T]
    (hT : ∀ y : T, IsDomain (T.presheaf.stalk y) ∧ IsIntegrallyClosed (T.presheaf.stalk y))
    (f : V ⟶ T) [WeaklyEtale f] [Surjective f] [QuasiCompact f]
    (γ : ↥(pullback f f) → GL (Fin n) E)
    (hc : IsDescentCocycle f (fun z (L : CompactOpenLattice E n) ↦ γ z • L)) :
    ∃ σ, IsTwistedSection f (fun z (L : CompactOpenLattice E n) ↦ γ z • L) (𝟙 T) σ := by
  classical
  obtain ⟨t₀⟩ := (inferInstance : Nonempty T)
  obtain ⟨v₀, -⟩ := f.surjective t₀
  obtain ⟨A, hAfin, hAlc, hAinv, hs⟩ :=
    exists_finite_invariant_subset_of_isIntegrallyClosed_stalk hT f hc v₀
      (CompactOpenLattice.standard E n)
  set p₁ := (pullback.fst f f).base
  set p₂ := (pullback.snd f f).base
  set q := (pullback.fst f (𝟙 T)).base
  have hq : Function.Surjective q := (pullback.fst f (𝟙 T)).surjective
  -- `A` is nonempty everywhere
  have hne (w : V) : (A w).Nonempty := by
    have key := IsTwistedSection.apply_eq_of_preconnectedSpace (f := f) (𝟙 T)
      (fun x ↦ (A (q x)).Nonempty)
      ((hAlc.comp _).comp_continuous (pullback.fst f (𝟙 T)).base.hom.continuous)
      (fun w ↦ by
        have h := hAinv ((twistedPairMap f (𝟙 T)).base w)
        simp only [p₁, p₂, ← Scheme.Hom.comp_apply, pullback.lift_fst, pullback.lift_snd] at h
        simp only [q, Scheme.Hom.comp_apply] at h ⊢
        rw [h, Set.image_nonempty])
    obtain ⟨x, hx⟩ := hq w
    obtain ⟨x₀, hx₀⟩ := hq v₀
    have := key x x₀
    simp only [hx, hx₀, eq_iff_iff] at this
    exact this.2 ⟨_, hs⟩
  -- the sum of the lattices of `A`
  let sumL (B : Set (CompactOpenLattice E n)) : CompactOpenLattice E n :=
    if h : B.Finite ∧ B.Nonempty then
      CompactOpenLattice.sum h.1.toFinset (h.1.toFinset_nonempty.2 h.2)
    else CompactOpenLattice.standard E n
  have hsumL (w : V) : sumL (A w) = CompactOpenLattice.sum (hAfin w).toFinset
      ((hAfin w).toFinset_nonempty.2 (hne w)) := by
    simp only [sumL, dite_eq_left (And.intro (hAfin w) (hne w))]
  refine ⟨fun x ↦ sumL (A (q x)), ?_, fun w ↦ ?_⟩
  · exact (hAlc.comp sumL).comp_continuous (pullback.fst f (𝟙 T)).base.hom.continuous
  · set z := (twistedPairMap f (𝟙 T)).base w
    have h := hAinv z
    have e₁ : p₁ z = q ((pullback.fst (pullback.snd f (𝟙 T)) (pullback.snd f (𝟙 T))).base w) := by
      simp only [z, p₁, q, ← Scheme.Hom.comp_apply, pullback.lift_fst]
    have e₂ : p₂ z = q ((pullback.snd (pullback.snd f (𝟙 T)) (pullback.snd f (𝟙 T))).base w) := by
      simp only [z, p₂, q, ← Scheme.Hom.comp_apply, pullback.lift_snd]
    rw [e₁, e₂] at h
    change sumL (A _) = γ z • sumL (A _)
    rw [hsumL, hsumL, CompactOpenLattice.smul_sum]
    congr 1
    ext L
    simp only [Set.Finite.mem_toFinset, Finset.mem_image, h, Set.mem_image]

end AlgebraicGeometry
