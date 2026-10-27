module

public import Mathlib.Topology.ContinuousMap.Algebra
public import Mathlib.Topology.Algebra.Field
public import Mathlib.Algebra.BigOperators.Fin

/-!
# The graded jointly continuous homogeneous coordinate equivalence

Source: Stacks Project, Tag 0DVG, continuous group cohomology, and the agent-written
homogeneous coordinate calculation extracted from that complex
(blueprint: lem-sfb-joint-continuous-coordinate-equivalence).

The homogeneous submodule is specified by its exact carrier. The inhomogeneous
submodule is Mathlib's `continuousSubmodule`, with the product topology on finite powers.
Both have the pointwise operations inherited from all functions. No topology on a
cochain space, differential, or complex is asserted here. In degree zero, evaluation
on the unique empty tuple identifies the inhomogeneous space with the coefficient space.
-/

@[expose] public section

set_option autoImplicit false

universe u v w

namespace ContinuousCohomology

/-- Jointly continuous equivariant homogeneous functions form a vector subspace, and
cumulative-product evaluation gives a linear equivalence with continuous functions
on one fewer group variables. Its inverse acts by the first coordinate after taking
successive ratios. The `LinearEquiv` includes both inverse identities. The formulas
include degree zero: the forward map evaluates at the identity, and the inverse sends
`v` to `fun x ↦ ρ x v`, after identifying functions on the empty tuple with `V`.

Source: Stacks Project, Tag 0DVG, etale-cohomology.tex, lines 9007--9040, for the
continuous inhomogeneous terms; the graded homogeneous conversion is agent-written.
(blueprint: lem-sfb-joint-continuous-coordinate-equivalence).

Proof:
1. By lem-weil-pbc-initial-topology-continuity (Mathlib `continuous_iInf_rng` and
   `continuous_induced_rng`), continuity into a finite product is coordinatewise,
   including the empty product. Constants, pairing and composition preserve continuity.
2. Continuous functions are closed under zero, addition and scalar multiplication.
   These operations preserve equivariance because every ρ a is linear over the field
   def-weil-field. Thus the exact homogeneous carrier is a submodule B. Mathlib's
   continuousSubmodule gives the inhomogeneous submodule with pointwise operations.
3. The coordinates p₀ = 1 and pᵢ₊₁ = pᵢ gᵢ are continuous by induction using continuous
   multiplication and projections. Hence Fin.partialProd is continuous, and evaluating
   a continuous homogeneous function on it defines the forward map.
4. Each successive ratio xᵢ⁻¹ xᵢ₊₁ is continuous by inversion and multiplication.
   Compose a continuous inhomogeneous function with these ratios, pair with x₀, and
   use joint continuity of the action to obtain the continuous inverse formula.
5. The ratios of a*x equal the ratios of x. The action law then proves equivariance
   of the inverse formula. Evaluation and linearity of ρ prove linearity of both maps.
6. Successive ratios of cumulative products recover g, whose initial product is 1.
   Thus the forward map after the inverse is the identity, including the empty tuple.
7. Cumulative products of the ratios of x telescope to x₀⁻¹*xᵢ, in that order.
   Equivariance and the action law give the other inverse identity. No commutativity
   of J is used.
8. At n = 0, the cumulative-product tuple is (1), the ratio tuple is empty, and
   equivariance gives F(x) = ρ x (F(1)). Thus the formulas are exactly the stated
   degree-zero evaluation and orbit maps. No separation, compactness or discreteness
   assumption occurred in any step. -/
theorem exists_jointContinuousCoordinateEquivalence
    (E : Type u) [Field E] [TopologicalSpace E] [IsTopologicalDivisionRing E]
    (J : Type v) [Group J] [TopologicalSpace J] [IsTopologicalGroup J]
    (V : Type w) [AddCommGroup V] [Module E V] [TopologicalSpace V]
    [IsTopologicalAddGroup V] [ContinuousSMul E V]
    (ρ : J →* V ≃ₗ[E] V) (hρ : Continuous (fun p : J × V ↦ ρ p.1 p.2))
    (n : ℕ) :
    ∃ B : Submodule E ((Fin (n + 1) → J) → V),
      (∀ F : (Fin (n + 1) → J) → V,
        F ∈ B ↔ Continuous F ∧
          ∀ (a : J) (x : Fin (n + 1) → J), F (fun i ↦ a * x i) = ρ a (F x)) ∧
      ∃ e : B ≃ₗ[E] continuousSubmodule (Fin n → J) E V,
        (∀ (F : B) (g : Fin n → J), (e F).val g = F.val (Fin.partialProd g)) ∧
        (∀ (f : continuousSubmodule (Fin n → J) E V) (x : Fin (n + 1) → J),
          (e.symm f).val x = ρ (x 0) (f.val (fun i ↦ (x i.castSucc)⁻¹ * x i.succ))) := by
  let B : Submodule E ((Fin (n + 1) → J) → V) :=
    { carrier := {F | Continuous F ∧
        ∀ (a : J) (x : Fin (n + 1) → J), F (fun i ↦ a * x i) = ρ a (F x)}
      zero_mem' := ⟨continuous_const, by simp⟩
      add_mem' := by
        intro F H hF hH
        refine ⟨hF.1.add hH.1, ?_⟩
        intro a x
        change F (fun i ↦ a * x i) + H (fun i ↦ a * x i) = ρ a (F x + H x)
        rw [hF.2, hH.2, map_add]
      smul_mem' := by
        intro c F hF
        refine ⟨hF.1.const_smul c, ?_⟩
        intro a x
        change c • F (fun i ↦ a * x i) = ρ a (c • F x)
        rw [hF.2, map_smul] }
  have hP : Continuous (Fin.partialProd : (Fin n → J) → (Fin (n + 1) → J)) := by
    apply continuous_pi
    intro i
    induction i using Fin.inductionOn with
    | zero => simpa using (continuous_const : Continuous (fun _ : Fin n → J ↦ (1 : J)))
    | succ i hi =>
      convert hi.mul (continuous_apply i) using 1
      funext g
      exact Fin.partialProd_succ g i
  let ratios : (Fin (n + 1) → J) → (Fin n → J) :=
    fun x i ↦ (x i.castSucc)⁻¹ * x i.succ
  have hr : Continuous ratios :=
    continuous_pi fun i ↦ (continuous_apply i.castSucc).inv.mul (continuous_apply i.succ)
  let Φ : B →ₗ[E] continuousSubmodule (Fin n → J) E V :=
    { toFun := fun F ↦ ⟨fun g ↦ F.val (Fin.partialProd g), F.property.1.comp hP⟩
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  let Ψ : continuousSubmodule (Fin n → J) E V →ₗ[E] B :=
    { toFun := fun f ↦ ⟨fun x ↦ ρ (x 0) (f.val (ratios x)), by
        refine ⟨hρ.comp ((continuous_apply 0).prodMk (f.property.comp hr)), ?_⟩
        intro a x
        have heq : ratios (fun i ↦ a * x i) = ratios x := by
          funext i
          dsimp [ratios]
          simp only [mul_inv_rev, mul_assoc, inv_mul_cancel_left]
        dsimp only
        rw [heq, map_mul]
        rfl⟩
      map_add' := by
        intro f g
        apply Subtype.ext
        funext x
        exact (ρ (x 0)).map_add _ _
      map_smul' := by
        intro c f
        apply Subtype.ext
        funext x
        exact (ρ (x 0)).map_smul c _ }
  have hleft : Function.LeftInverse Ψ Φ := by
    intro F
    apply Subtype.ext
    funext x
    change ρ (x 0) (F.val (Fin.partialProd (ratios x))) = F.val x
    have hx : (fun i ↦ x 0 * Fin.partialProd (ratios x) i) = x :=
      Fin.partialProd_left_inv x
    rw [← F.property.2 (x 0) (Fin.partialProd (ratios x)), hx]
  have hright : Function.RightInverse Ψ Φ := by
    intro f
    apply Subtype.ext
    funext g
    change ρ (Fin.partialProd g 0) (f.val (ratios (Fin.partialProd g))) = f.val g
    have hg : ratios (Fin.partialProd g) = g :=
      funext (Fin.partialProd_right_inv g)
    rw [hg, Fin.partialProd_zero, map_one]
    rfl
  let e : B ≃ₗ[E] continuousSubmodule (Fin n → J) E V :=
    { Φ with
      invFun := Ψ
      left_inv := hleft
      right_inv := hright }
  exact ⟨B, fun _ ↦ Iff.rfl, e, fun _ _ ↦ rfl, fun _ _ ↦ rfl⟩

end ContinuousCohomology
