/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.DeligneLaumon.Reduction.Weights

/-!
# Local Frobenius eigenvalues of mixed Weil sheaves

A Weil sheaf which is `ι`-mixed of weights at most `w` has weights at most `w` at every closed
point: every eigenvalue `α` of its local Frobenius at a closed point `x` satisfies
`|ι α| ≤ q_x ^ (w / 2)`. The stalk functors are exact, so the stalk of the middle term of a short
exact sequence is an extension of Frobenius modules, and every eigenvalue of the middle term of
such an extension is an eigenvalue of the sub or of the quotient; induction along the filtration
gives the bound.

## Main statements

- `FrobeniusModule.hasEigenvalue_or_hasEigenvalue_of_exact`: eigenvalues in an exact sequence.
- `AlgebraicGeometry.WeilSheaf.exists_stalkAtMap_eq_of_stalkAtMap_cokernel_π_eq_zero`: exactness
  of the stalks of `0 → F → G → coker → 0`.
- `AlgebraicGeometry.WeilSheaf.IsMixedOfWeightsAtMost.hasWeightsAtMost`: a sheaf mixed of weights
  at most `w` has weights at most `w`.
-/

@[expose] public section

universe u v w

open CategoryTheory Limits

namespace FrobeniusModule

variable {K : Type w} [Field K] {A B C : FrobeniusModule.{v, w} K}

/-- In a sequence `A ⟶ B ⟶ C` of Frobenius modules, with `A ⟶ B` injective and exact at `B`,
every eigenvalue of the Frobenius of `B` is an eigenvalue of the Frobenius of `A` or of `C`. -/
theorem hasEigenvalue_or_hasEigenvalue_of_exact (f : A.carrier →ₗ[K] B.carrier)
    (hf : ∀ x, f (A.frobenius x) = B.frobenius (f x)) (g : B.carrier →ₗ[K] C.carrier)
    (hg : ∀ x, g (B.frobenius x) = C.frobenius (g x)) (hinj : Function.Injective f)
    (hex : ∀ y, g y = 0 → ∃ x, f x = y) {α : K} (hα : B.frobeniusEnd.HasEigenvalue α) :
    A.frobeniusEnd.HasEigenvalue α ∨ C.frobeniusEnd.HasEigenvalue α := by
  obtain ⟨y, hy⟩ := hα.exists_hasEigenvector
  rw [Module.End.hasEigenvector_iff, Module.End.mem_eigenspace_iff] at hy
  by_cases hgy : g y = 0
  · obtain ⟨x, rfl⟩ := hex y hgy
    left
    refine Module.End.hasEigenvalue_of_hasEigenvector (x := x) ?_
    rw [Module.End.hasEigenvector_iff, Module.End.mem_eigenspace_iff]
    refine ⟨hinj ?_, fun h ↦ hy.2 (by rw [h, map_zero])⟩
    change f (A.frobenius x) = f (α • x)
    rw [hf, map_smul]
    exact hy.1
  · right
    refine Module.End.hasEigenvalue_of_hasEigenvector (x := g y) ?_
    rw [Module.End.hasEigenvector_iff, Module.End.mem_eigenspace_iff]
    refine ⟨?_, hgy⟩
    change C.frobenius (g y) = α • g y
    rw [← hg, ← map_smul]
    exact congrArg g hy.1

/-- The middle term of an exact sequence `A ↪ B ⟶ C` of Frobenius modules whose outer terms have
weights at most `w` has weights at most `w`. -/
theorem HasWeightsAtMost.of_exact {ι : K →+* ℂ} {q : ℕ} {w : ℝ} (f : A.carrier →ₗ[K] B.carrier)
    (hf : ∀ x, f (A.frobenius x) = B.frobenius (f x)) (g : B.carrier →ₗ[K] C.carrier)
    (hg : ∀ x, g (B.frobenius x) = C.frobenius (g x)) (hinj : Function.Injective f)
    (hex : ∀ y, g y = 0 → ∃ x, f x = y) (hA : A.HasWeightsAtMost ι q w)
    (hC : C.HasWeightsAtMost ι q w) : B.HasWeightsAtMost ι q w :=
  fun α hα ↦ by
    rcases hasEigenvalue_or_hasEigenvalue_of_exact f hf g hg hinj hex hα with h | h
    exacts [hA α h, hC α h]

/-- A Frobenius-stable subspace of a Frobenius module with weights at most `w` has weights at
most `w`. -/
theorem HasWeightsAtMost.of_injective {ι : K →+* ℂ} {q : ℕ} {w : ℝ}
    (f : A.carrier →ₗ[K] B.carrier) (hf : ∀ x, f (A.frobenius x) = B.frobenius (f x))
    (hinj : Function.Injective f) (hB : B.HasWeightsAtMost ι q w) : A.HasWeightsAtMost ι q w :=
  fun α hα ↦ hB α (hasEigenvalue_of_injective f hf hinj hα)

end FrobeniusModule

namespace AlgebraicGeometry.WeilSheaf

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
  {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]

/-- The stalk functor at a geometric point preserves finite limits: it is the composite of the
forgetful functors, the pullback and the global sections, which all do. -/
instance preservesFiniteLimits_stalkFunctor
    (s : Spec (.of (AlgebraicClosure k₀)) ⟶ (X ↘ Spec (CommRingCat.of k₀)).geometricFiber) :
    PreservesFiniteLimits (stalkFunctor k₀ l s) := by
  have : PreservesLimits (Sheaf.Γ (Scheme.ProEt.topology (Spec (.of (AlgebraicClosure k₀))))
      (WeilCoefficients.{u} l)) :=
    (constantSheafΓAdj _ _).rightAdjoint_preservesLimits
  have : Functor.PreservesZeroMorphisms (C := WeilSheaf k₀ l X)
      (WeilSheaf.objectProperty k₀ l X).ι := ⟨fun _ _ ↦ rfl⟩
  have : PreservesFiniteLimits (C := WeilSheaf k₀ l X) (WeilSheaf.objectProperty k₀ l X).ι :=
    have := (WeilSheaf.objectProperty k₀ l X).preservesKernels_ι
    Functor.preservesFiniteLimits_of_preservesKernels _
  have : PreservesLimits (ProEtale.AdicSheaf.forget (l := l)
      (X ↘ Spec (CommRingCat.of k₀)).geometricFiber) := ⟨inferInstance⟩
  unfold stalkFunctor
  infer_instance

/-- The stalk functor at a geometric point is exact: it preserves finite limits and
epimorphisms. -/
instance preservesHomology_stalkFunctor
    (s : Spec (.of (AlgebraicClosure k₀)) ⟶ (X ↘ Spec (CommRingCat.of k₀)).geometricFiber) :
    (stalkFunctor k₀ l s).PreservesHomology :=
  Functor.preservesHomology_of_preservesEpis_and_kernels _

/-- Exactness of the stalks of `F ↪ G ↠ coker φ` in the middle: an element of the stalk of `G`
killed by the stalk of the cokernel projection comes from the stalk of `F`. -/
theorem exists_stalkAtMap_eq_of_stalkAtMap_cokernel_π_eq_zero {F G : WeilSheaf k₀ l X}
    (φ : F ⟶ G)
    (s : Spec (.of (AlgebraicClosure k₀)) ⟶ (X ↘ Spec (CommRingCat.of k₀)).geometricFiber)
    (m : ℕ) (hs : s ≫ ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ m).hom =
      (specGeometricFrobenius k₀ ^ m).hom ≫ s)
    (y : (G.stalkAt s m hs).carrier) (hy : stalkAtMap s m hs (cokernel.π φ) y = 0) :
    ∃ x, stalkAtMap s m hs φ x = y :=
  (ShortComplex.moduleCat_exact_iff _).1
    ((ShortComplex.exact_cokernel φ).map (stalkFunctor k₀ l s)) y hy

/-- Along a finite filtration `0 = G 0 ↪ G 1 ↪ ⋯ ↪ G n` whose successive quotients have stalks
at `s` of weights at most `w`, every `G i` has stalk at `s` of weights at most `w`. -/
theorem stalkAt_hasWeightsAtMost_of_filtration {ι : PadicAlgCl l →+* ℂ} {q : ℕ} {w : ℝ}
    (s : Spec (.of (AlgebraicClosure k₀)) ⟶ (X ↘ Spec (CommRingCat.of k₀)).geometricFiber)
    (m : ℕ) (hs : s ≫ ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ m).hom =
      (specGeometricFrobenius k₀ ^ m).hom ≫ s)
    {n : ℕ} (G : Fin (n + 1) → WeilSheaf k₀ l X) (φ : ∀ i : Fin n, G i.castSucc ⟶ G i.succ)
    (h0 : IsZero (G 0)) (hmono : ∀ i, Mono (φ i))
    (h : ∀ i : Fin n, ((cokernel (φ i)).stalkAt s m hs).HasWeightsAtMost ι q w) :
    ∀ (i : ℕ) (hi : i < n + 1), ((G ⟨i, hi⟩).stalkAt s m hs).HasWeightsAtMost ι q w := by
  intro i
  induction i with
  | zero =>
    intro hi α hα
    exfalso
    obtain ⟨v, hv⟩ := hα.exists_hasEigenvector
    have : Subsingleton ((G ⟨0, hi⟩).stalkAt s m hs).carrier :=
      ModuleCat.subsingleton_of_isZero ((WeilCoefficients.toModuleCat l).map_isZero
        ((stalkFunctor k₀ l s).map_isZero (X := G ⟨0, hi⟩) h0))
    exact hv.2 (Subsingleton.elim _ _)
  | succ i ih =>
    intro hi
    let j : Fin n := ⟨i, by omega⟩
    have := hmono j
    exact FrobeniusModule.HasWeightsAtMost.of_exact (stalkAtMap s m hs (φ j))
      (stalkAtMap_frobenius s m hs _) (stalkAtMap s m hs (cokernel.π (φ j)))
      (stalkAtMap_frobenius s m hs _) (injective_stalkAtMap s m hs _)
      (exists_stalkAtMap_eq_of_stalkAtMap_cokernel_π_eq_zero _ s m hs) (ih j.castSucc.2) (h j)

/-- A Weil sheaf which is `ι`-mixed of weights at most `w` has weights at most `w`: at every
closed point `x`, every eigenvalue `α` of the local Frobenius satisfies `|ι α| ≤ q_x ^ (w / 2)`.
The stalk functors being exact, this follows by induction along the filtration from the bounds
for its punctually pure quotients (blueprint: `sk-d-dl-general-weights`). -/
theorem IsMixedOfWeightsAtMost.hasWeightsAtMost {ι : PadicAlgCl l →+* ℂ} {F : WeilSheaf k₀ l X}
    {w : ℝ} (h : F.IsMixedOfWeightsAtMost ι w) : F.HasWeightsAtMost ι w := by
  intro x
  obtain ⟨n, G, φ, h0, ⟨e⟩, hmono, hpure⟩ := h
  have hs := Scheme.Hom.geometricFiberPointOfFinitePoint_comp_geometricGaloisFrobenius_pow
    (X ↘ Spec (CommRingCat.of k₀)) x
  have hq : 1 ≤ (X ↘ Spec (CommRingCat.of k₀)).residueCard x.1 :=
    Nat.one_le_pow _ _ Nat.card_pos
  have hquot (i : Fin n) : ((cokernel (φ i)).stalkAt _ _ hs).HasWeightsAtMost ι
      ((X ↘ Spec (CommRingCat.of k₀)).residueCard x.1) w := by
    obtain ⟨v, hv, hpv⟩ := hpure i
    exact (hpv x).hasWeightsAtMost.mono hq hv
  have hlast : ((G (Fin.last n)).stalkAt _ _ hs).HasWeightsAtMost ι
      ((X ↘ Spec (CommRingCat.of k₀)).residueCard x.1) w :=
    stalkAt_hasWeightsAtMost_of_filtration _ _ hs G φ h0 hmono hquot n n.lt_succ_self
  have hF : (F.stalkAt _ _ hs).HasWeightsAtMost ι
      ((X ↘ Spec (CommRingCat.of k₀)).residueCard x.1) w :=
    FrobeniusModule.HasWeightsAtMost.of_injective (stalkAtMap _ _ hs e.inv)
      (stalkAtMap_frobenius _ _ hs _) (injective_stalkAtMap _ _ hs _) hlast
  exact hF

end AlgebraicGeometry.WeilSheaf
