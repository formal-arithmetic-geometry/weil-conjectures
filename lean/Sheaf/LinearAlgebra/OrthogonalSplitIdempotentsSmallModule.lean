module

public import Mathlib.Algebra.Algebra.Tower
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Data.Countable.Defs
public import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.Algebra.Module.ULift

/-! # Split idempotents orthogonal on a module

Source: the Weil conjectures blueprint, sec-six-functors-basics,
sk-thm-sf-ctf-stability-direct-images.proof.md, paragraph (3), agent coefficient auxiliary,
returned reconstruction proof steps 8–9
(blueprint: lem-sfb-orthogonal-split-idempotents-small-module).

The auxiliary is agent-formulated: the blueprint paragraph motivates the reconstruction
argument but does not itself state this algebraic lemma or supply an external reference.
-/

@[expose] public section

set_option autoImplicit false

universe u v w t

namespace Module

/-- Split operators with projections orthogonal on a module give independent translates,
an injection into every spanning set of a nonzero module, and the countability obstruction.

Source: the Weil conjectures blueprint, sec-six-functors-basics,
sk-thm-sf-ctf-stability-direct-images.proof.md, paragraph (3), agent coefficient auxiliary,
returned reconstruction proof steps 8–9
(blueprint: lem-sfb-orthogonal-split-idempotents-small-module).

Proof (agent-formulated extraction, as in the DAG):
1. Fix q ≠ 0 and put x_i = u_i • q and p_i = u_i * r_i. Then r_i • x_i = q,
   so x_i ≠ 0, and p_i • x_i = x_i. For i ≠ j, the annihilation hypothesis gives
   p_i • x_j = p_i • (p_j • x_j) = (p_i * p_j) • x_j = 0.
2. Apply p_k to a finite K-linear relation among the x_i. Scalar restriction along
   the central algebra map makes this action K-linear, so only t_k • x_k remains.
   Apply r_k to get t_k • q = 0. The field inverse of a nonzero t_k would give q = 0;
   hence each coefficient is zero. This is precisely LinearIndependent K (u · • q).
3. If Q is nonzero, choose such a q. Apply lem-sfb-independent-family-spanning-cardinality,
   represented by Mathlib's linearIndependent_le_span'', to any spanning set W.
   Enlarge universes when applying that cardinal inequality; cardinal comparison
   is existence of an injection I → W, including when I and Q have different universes.
4. If I is uncountable and W is a countable spanning set, a nonzero Q would give an
   injection I → W. Compose with the injection W → ℕ furnished by def-sfb-countable-set.
   This contradicts ¬ Countable I, so every element of Q is zero.

IsScalarTower expresses that the K-vector-space structure is induced by the unital
D-action. Products of distinct projections need only annihilate Q. -/
theorem orthogonal_split_idempotents_small_module
    (K : Type u) [Field K] (D : Type v) [Ring D] [Algebra K D]
    (Q : Type w) [AddCommGroup Q] [Module D Q] [Module K Q] [IsScalarTower K D Q]
    (I : Type t) (u r : I → D)
    (_hsplit : ∀ i : I, r i * u i = 1)
    (_horthogonal : ∀ (i j : I), i ≠ j → ∀ x : Q, ((u i * r i) * (u j * r j)) • x = 0) :
    (∀ q : Q, q ≠ 0 → LinearIndependent K (fun i : I ↦ u i • q)) ∧
      (∀ W : Set Q, Submodule.span K W = ⊤ → Nontrivial Q →
        ∃ f : I → W, Function.Injective f) ∧
      (¬ Countable I → (∃ W : Set Q, Countable W ∧ Submodule.span K W = ⊤) →
        Subsingleton Q) := by
  classical
  have hleft (i : I) (q : Q) : r i • (u i • q) = q := by
    rw [← mul_smul, _hsplit, one_smul]
  have hfixed (i : I) (q : Q) : (u i * r i) • (u i • q) = u i • q := by
    rw [mul_smul, hleft]
  have hzero (i j : I) (hij : i ≠ j) (q : Q) :
      (u i * r i) • (u j • q) = 0 := by
    calc
      (u i * r i) • (u j • q) =
          ((u i * r i) * (u j * r j)) • (u j • q) := by
        rw [mul_smul (u i * r i) (u j * r j), hfixed]
      _ = 0 := _horthogonal i j hij _
  have hind : ∀ q : Q, q ≠ 0 → LinearIndependent K (fun i : I ↦ u i • q) := by
    intro q hq
    rw [linearIndependent_iff']
    intro s a ha k hk
    have hsum := congrArg (fun x : Q ↦ (u k * r k) • x) ha
    have hisolate : (u k * r k) • (∑ i ∈ s, a i • (u i • q)) =
        a k • (u k • q) := by
      rw [Finset.smul_sum]
      simp_rw [smul_comm (u k * r k)]
      rw [Finset.sum_eq_single k]
      · rw [hfixed]
      · intro j _ hj
        rw [hzero k j (Ne.symm hj), smul_zero]
      · exact fun h ↦ (h hk).elim
    rw [hisolate, smul_zero] at hsum
    have hscalar := congrArg (fun x : Q ↦ r k • x) hsum
    rw [smul_comm, hleft, smul_zero] at hscalar
    by_contra ha0
    apply hq
    calc
      q = (a k)⁻¹ • (a k • q) := by
        rw [← mul_smul, inv_mul_cancel₀ ha0, one_smul]
      _ = 0 := by rw [hscalar, smul_zero]
  have hinj : ∀ W : Set Q, Submodule.span K W = ⊤ → Nontrivial Q →
      ∃ f : I → W, Function.Injective f := by
    intro W hW hQ
    let := hQ
    obtain ⟨q, hq⟩ := exists_ne (0 : Q)
    let e : Q ≃ₗ[K] ULift.{t} Q := ULift.moduleEquiv.symm
    let W' : Set (ULift.{t} Q) := e '' W
    have hW' : Submodule.span K W' = ⊤ := by
      rw [show W' = e '' W from rfl, Submodule.span_image_linearEquiv, hW]
      rw [Submodule.map_top, LinearMap.range_eq_top.mpr e.surjective]
    have hind' : LinearIndependent K
        (fun i : ULift.{w} I ↦ e (u i.down • q)) :=
      ((hind q hq).comp ULift.down ULift.down_injective).map'
        e.toLinearMap (LinearMap.ker_eq_bot.mpr e.injective)
    have hcard := linearIndependent_le_span'' hind' W' hW'
    obtain ⟨f⟩ := hcard
    let g : W' → W := fun x ↦ ⟨e.symm x, by
      obtain ⟨y, hy, he⟩ := x.property
      simpa [← he] using hy⟩
    have hg : Function.Injective g := by
      intro x y h
      apply Subtype.ext
      apply e.symm.injective
      exact congrArg Subtype.val h
    exact ⟨fun i ↦ g (f (ULift.up i)), hg.comp (f.injective.comp ULift.up_injective)⟩
  refine ⟨hind, hinj, ?_⟩
  rintro hI ⟨W, hcount, hW⟩
  let := hcount
  by_contra hQ
  have : Nontrivial Q := not_subsingleton_iff_nontrivial.mp hQ
  obtain ⟨f, hf⟩ := hinj W hW inferInstance
  exact hI hf.countable

end Module
