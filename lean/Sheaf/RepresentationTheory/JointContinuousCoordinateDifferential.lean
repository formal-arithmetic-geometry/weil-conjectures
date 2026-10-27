module

public import Mathlib.Topology.Algebra.Field
public import Mathlib.Topology.Algebra.Module.Basic
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Fin.Tuple.Basic

import Mathlib.Tactic.FunProp

/-!
# Alternating omission and the jointly continuous coordinate differential

Source: Stacks Project, Tag 0DVG, `etale-cohomology.tex`, continuous group cohomology,
and the agent-written homogeneous-coordinate verification in the DAG proof.
(blueprint: lem-sfb-joint-continuous-coordinate-differential).

The submodules are specified by their exact membership predicates inside the full
function spaces, so their operations are pointwise. All four linear maps are specified
at every argument by their formulas. In degree zero, functions on the unique empty tuple
are canonically identified with V by evaluation; no function-space topology is used.
-/

@[expose] public section

universe u v w

namespace ContinuousCohomology

private theorem continuous_partialProd
    {J : Type v} [Group J] [TopologicalSpace J] [IsTopologicalGroup J] (n : ℕ) :
    Continuous (Fin.partialProd : (Fin n → J) → (Fin (n + 1) → J)) := by
  apply continuous_pi
  intro i
  induction i using Fin.inductionOn with
  | zero => simpa using (continuous_const : Continuous (fun _ : Fin n → J ↦ (1 : J)))
  | succ i hi =>
    convert hi.mul (continuous_apply i) using 1
    funext g
    exact Fin.partialProd_succ g i

private theorem omission_square
    {E : Type u} [Field E] {J : Type v} {V : Type w}
    [AddCommGroup V] [Module E V] (n : ℕ) (F : (Fin (n + 1) → J) → V)
    (x : Fin (n + 3) → J) :
    (∑ i : Fin (n + 3), (-1 : E) ^ i.val •
      ∑ j : Fin (n + 2), (-1 : E) ^ j.val • F ((x ∘ i.succAbove) ∘ j.succAbove)) = 0 := by
  simp_rw [Finset.smul_sum]
  rw [Fin.sum_sum_eq_sum_triangle_add]
  apply Finset.sum_eq_zero
  intro i _
  apply Finset.sum_eq_zero
  intro j hj
  have hij : i ≤ j := Finset.mem_Ici.mp hj
  have h₁ : i.castSucc.succAbove j = j.succ :=
    Fin.succAbove_castSucc_of_le i j hij
  have h₂ : j.predAbove i.castSucc = i := by
    exact Fin.predAbove_castSucc_of_le j i hij
  have hx : (x ∘ i.castSucc.succAbove) ∘ j.succAbove =
      (x ∘ j.succ.succAbove) ∘ i.succAbove := by
    funext k
    exact congrArg x (by
      simpa only [h₁, h₂] using
        (Fin.succAbove_succAbove_succAbove_predAbove i.castSucc j k).symm)
  simp only [Fin.val_castSucc, Fin.val_succ, hx, smul_smul]
  simp [pow_succ, mul_comm]

/-- The alternating omission differential on jointly continuous equivariant functions is
linear, squares to zero, and in cumulative-product coordinates is the continuous
inhomogeneous differential, with its individual first, internal, and final faces.

Source: Stacks Project, Tag 0DVG, displayed differential, and the agent-formulated
homogeneous-coordinate verification, all eight proof steps of the DAG node.
(blueprint: lem-sfb-joint-continuous-coordinate-differential).

The existential submodules have exactly the prescribed elements, not arbitrary models.
Their subtype operations are the ambient pointwise operations. Likewise the four map
formulas determine their values uniquely. `Fin.partialProd` is P, and the tuple
`fun i ↦ (x i.castSucc)⁻¹ * x i.succ` is r. `Fin.contractNth i` merges the adjacent
arguments indexed by i and i+1, except at the last index, where it drops the last one.
Thus its sum includes the final term with sign (-1)^(n+1). The internal-face index
`i : Fin n` corresponds to the paper's index i+1, with sign (-1)^(i.val+1).
The degree-zero clause evaluates the constant cochain at the unique empty tuple.

Proof: (1) Continuity is preserved by pointwise sums and scalar multiples; the action
is linear, so equivariance is preserved too. These predicates therefore give submodules.
(2) Finite cumulative products and successive ratios are continuous. Composing with F
or with f and the jointly continuous action gives Phi and Psi. Ratios are unchanged by
simultaneous left translation, so Psi is equivariant. Pointwise linearity gives linear
maps. In degree zero these maps are evaluation at 1 and x0 acting on the coefficient.
(3) Each omission is continuous and commutes with left translation. Finite summation
therefore gives a continuous equivariant function, and distributing sums proves that
delta is linear. (4) Dropping an argument and multiplying adjacent arguments are
continuous. Joint continuity of the action handles the first term of d. Addition and
scalar multiplication handle the finite signed sum; linearity follows term by term.
For n=0 the formula is g acting on v minus v.
(5) Expand two successive omission sums. For each pair a<b of original coordinates,
the two orders of deletion have signs (-1)^(a+b-1) and (-1)^(a+b), and cancel. Every
term occurs in exactly one such pair, also in characteristic two. Thus delta squared
is zero. (6) The tuple omitting p0 is g1 times the cumulative products of the tail.
Equivariance gives the first-face formula with sign +1. (7) Omitting pi, 1≤i≤n,
merges gi and g(i+1), by associativity in their original order; the sign is (-1)^i.
(8) Omitting the last cumulative product leaves the prefix, with sign (-1)^(n+1).
Substitution of these three face identities in the omission sum proves Phi delta =
d Phi. For n=0 there are two faces and no internal faces, giving gF(1)-F(1). -/
theorem exists_jointContinuousCoordinateDifferential
    (E : Type u) [Field E] [TopologicalSpace E] [IsTopologicalDivisionRing E]
    (J : Type v) [Group J] [TopologicalSpace J] [IsTopologicalGroup J]
    (V : Type w) [AddCommGroup V] [Module E V] [TopologicalSpace V]
    [ContinuousAdd V] [ContinuousSMul E V]
    (ρ : J →* V ≃ₗ[E] V) (hρ : Continuous (fun p : J × V ↦ ρ p.1 p.2)) :
    ∃ (B : ∀ n : ℕ, Submodule E ((Fin (n + 1) → J) → V))
      (C : ∀ n : ℕ, Submodule E ((Fin n → J) → V))
      (δ : ∀ n : ℕ, B n →ₗ[E] B (n + 1))
      (d : ∀ n : ℕ, C n →ₗ[E] C (n + 1))
      (Φ : ∀ n : ℕ, B n →ₗ[E] C n)
      (Ψ : ∀ n : ℕ, C n →ₗ[E] B n),
      (∀ (n : ℕ) (F : (Fin (n + 1) → J) → V),
        F ∈ B n ↔ Continuous F ∧
          ∀ (a : J) (x : Fin (n + 1) → J), F (fun i ↦ a * x i) = ρ a (F x)) ∧
      (∀ (n : ℕ) (f : (Fin n → J) → V), f ∈ C n ↔ Continuous f) ∧
      (∀ (n : ℕ) (F : B n) (g : Fin n → J),
        (Φ n F).val g = F.val (Fin.partialProd g)) ∧
      (∀ (n : ℕ) (f : C n) (x : Fin (n + 1) → J),
        (Ψ n f).val x = ρ (x 0) (f.val (fun i ↦ (x i.castSucc)⁻¹ * x i.succ))) ∧
      (∀ (n : ℕ) (F : B n) (x : Fin (n + 2) → J),
        (δ n F).val x = ∑ i : Fin (n + 2), (-1 : E) ^ i.val • F.val (x ∘ i.succAbove)) ∧
      (∀ (n : ℕ) (f : C n) (g : Fin (n + 1) → J),
        (d n f).val g = ρ (g 0) (f.val (Fin.tail g)) +
          ∑ i : Fin (n + 1), (-1 : E) ^ (i.val + 1) •
            f.val (Fin.contractNth i (· * ·) g)) ∧
      (∀ (f : C 0) (g : J),
        (d 0 f).val (fun _ ↦ g) = ρ g (f.val Fin.elim0) - f.val Fin.elim0) ∧
      (∀ n : ℕ, (δ (n + 1)).comp (δ n) = 0) ∧
      (∀ n : ℕ, (Φ (n + 1)).comp (δ n) = (d n).comp (Φ n)) ∧
      (∀ (n : ℕ) (F : B n) (g : Fin (n + 1) → J),
        F.val (Fin.tail (Fin.partialProd g)) = ρ (g 0) ((Φ n F).val (Fin.tail g))) ∧
      (∀ (n : ℕ) (F : B n) (g : Fin (n + 1) → J) (i : Fin n),
        F.val (Fin.partialProd g ∘ i.succ.castSucc.succAbove) =
          (Φ n F).val (Fin.contractNth i.castSucc (· * ·) g)) ∧
      (∀ (n : ℕ) (F : B n) (g : Fin (n + 1) → J),
        F.val (Fin.init (Fin.partialProd g)) = (Φ n F).val (Fin.init g)) := by
  classical
  let B : ∀ n : ℕ, Submodule E ((Fin (n + 1) → J) → V) := fun n ↦
    { carrier := {F | Continuous F ∧
        ∀ (a : J) (x : Fin (n + 1) → J), F (fun i ↦ a * x i) = ρ a (F x)}
      zero_mem' := ⟨continuous_const, by simp⟩
      add_mem' := by
        rintro F G ⟨hF, eF⟩ ⟨hG, eG⟩
        exact ⟨hF.add hG, by intro a x; simp [eF, eG]⟩
      smul_mem' := by
        rintro c F ⟨hF, eF⟩
        exact ⟨hF.const_smul c, by intro a x; simp [eF]⟩ }
  let C : ∀ n : ℕ, Submodule E ((Fin n → J) → V) := fun n ↦
    { carrier := {f | Continuous f}
      zero_mem' := continuous_const
      add_mem' := fun hf hg ↦ hf.add hg
      smul_mem' := fun c _ hf ↦ hf.const_smul c }
  let Φ : ∀ n : ℕ, B n →ₗ[E] C n := fun n ↦
    { toFun := fun F ↦ ⟨F.val ∘ Fin.partialProd,
        F.property.1.comp (continuous_partialProd n)⟩
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  let Ψ : ∀ n : ℕ, C n →ₗ[E] B n := fun n ↦
    { toFun := fun f ↦ ⟨fun x ↦ ρ (x 0)
          (f.val (fun i ↦ (x i.castSucc)⁻¹ * x i.succ)), by
        constructor
        · have hr : Continuous (fun x : Fin (n + 1) → J ↦
              fun i : Fin n ↦ (x i.castSucc)⁻¹ * x i.succ) :=
            continuous_pi fun i ↦
              (continuous_apply i.castSucc).inv.mul (continuous_apply i.succ)
          exact hρ.comp ((continuous_apply 0).prodMk (f.property.comp hr))
        · intro a x
          simp only [mul_inv_rev, mul_assoc, inv_mul_cancel_left]
          rw [map_mul]
          rfl⟩
      map_add' := by intro f g; apply Subtype.ext; funext x; exact (ρ (x 0)).map_add _ _
      map_smul' := by intro c f; apply Subtype.ext; funext x; exact (ρ (x 0)).map_smul _ _ }
  let δ : ∀ n : ℕ, B n →ₗ[E] B (n + 1) := fun n ↦
    { toFun := fun F ↦ ⟨fun x ↦ ∑ i : Fin (n + 2),
          (-1 : E) ^ i.val • F.val (x ∘ i.succAbove), by
        constructor
        · apply continuous_finsetSum
          intro i _
          exact (F.property.1.comp
            (continuous_pi fun j ↦ continuous_apply (i.succAbove j))).const_smul _
        · intro a x
          simp only [Function.comp_def, F.property.2, map_sum, map_smul]⟩
      map_add' := by
        intro F G
        apply Subtype.ext
        funext x
        simp [smul_add, Finset.sum_add_distrib]
      map_smul' := by
        intro c F
        apply Subtype.ext
        funext x
        change (∑ i : Fin (n + 2), (-1 : E) ^ i.val •
            (c • F.val (x ∘ i.succAbove))) =
          c • ∑ i : Fin (n + 2), (-1 : E) ^ i.val • F.val (x ∘ i.succAbove)
        rw [Finset.smul_sum]
        apply Finset.sum_congr rfl
        intro i _
        exact smul_comm _ _ _ }
  let d : ∀ n : ℕ, C n →ₗ[E] C (n + 1) := fun n ↦
    { toFun := fun f ↦ ⟨fun g ↦ ρ (g 0) (f.val (Fin.tail g)) +
          ∑ i : Fin (n + 1), (-1 : E) ^ (i.val + 1) •
            f.val (Fin.contractNth i (· * ·) g), by
        apply Continuous.add
        · have ht : Continuous (Fin.tail : (Fin (n + 1) → J) → (Fin n → J)) :=
            continuous_pi fun i ↦ continuous_apply i.succ
          exact hρ.comp ((continuous_apply 0).prodMk (f.property.comp ht))
        · apply continuous_finsetSum
          intro i _
          apply Continuous.const_smul
          apply f.property.comp
          apply continuous_pi
          intro k
          unfold Fin.contractNth
          split_ifs <;> fun_prop⟩
      map_add' := by
        intro f g
        apply Subtype.ext
        funext x
        simp [smul_add, Finset.sum_add_distrib, add_add_add_comm]
      map_smul' := by
        intro c f
        apply Subtype.ext
        funext x
        change ρ (x 0) (c • f.val (Fin.tail x)) +
            (∑ i : Fin (n + 1), (-1 : E) ^ (i.val + 1) •
              (c • f.val (Fin.contractNth i (· * ·) x))) =
          c • (ρ (x 0) (f.val (Fin.tail x)) +
            ∑ i : Fin (n + 1), (-1 : E) ^ (i.val + 1) •
              f.val (Fin.contractNth i (· * ·) x))
        rw [map_smul, smul_add, Finset.smul_sum]
        congr 1
        apply Finset.sum_congr rfl
        intro i _
        exact smul_comm _ _ _ }
  have first (n : ℕ) (F : B n) (g : Fin (n + 1) → J) :
      F.val (Fin.tail (Fin.partialProd g)) = ρ (g 0) ((Φ n F).val (Fin.tail g)) := by
    change F.val (Fin.tail (Fin.partialProd g)) =
      ρ (g 0) (F.val (Fin.partialProd (Fin.tail g)))
    rw [← F.property.2]
    apply congrArg F.val
    funext i
    exact Fin.partialProd_succ' g i
  have face (n : ℕ) (F : B n) (g : Fin (n + 1) → J) (i : Fin (n + 1)) :
      F.val (Fin.partialProd g ∘ i.succ.succAbove) =
        (Φ n F).val (Fin.contractNth i (· * ·) g) := by
    change F.val _ = F.val _
    rw [Fin.partialProd_contractNth]
  refine ⟨B, C, δ, d, Φ, Ψ, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, first, ?_, ?_⟩
  · intro n F; rfl
  · intro n f; rfl
  · intro n F g; rfl
  · intro n f x; rfl
  · intro n F x; rfl
  · intro n f g; rfl
  · intro f g
    change ρ g (f.val (Fin.tail (fun _ ↦ g))) +
      ∑ i : Fin 1, (-1 : E) ^ (i.val + 1) •
        f.val (Fin.contractNth i (· * ·) (fun _ ↦ g)) = _
    have he (x : Fin 0 → J) : x = Fin.elim0 := Subsingleton.elim _ _
    simp [he, sub_eq_add_neg]
  · intro n
    apply LinearMap.ext
    intro F
    apply Subtype.ext
    funext x
    exact omission_square n F.val x
  · intro n
    apply LinearMap.ext
    intro F
    apply Subtype.ext
    funext g
    change (∑ i : Fin (n + 2), (-1 : E) ^ i.val •
      F.val (Fin.partialProd g ∘ i.succAbove)) =
      ρ (g 0) ((Φ n F).val (Fin.tail g)) +
        ∑ i : Fin (n + 1), (-1 : E) ^ (i.val + 1) •
          (Φ n F).val (Fin.contractNth i (· * ·) g)
    rw [Fin.sum_univ_succ]
    simp only [Fin.val_zero, pow_zero, one_smul, Fin.succAbove_zero,
      Fin.val_succ]
    rw [show Fin.partialProd g ∘ Fin.succ = Fin.tail (Fin.partialProd g) from rfl,
      first]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    rw [face]
  · intro n F g i
    simpa only [Fin.succ_castSucc] using face n F g i.castSucc
  · intro n F g
    change F.val (Fin.init (Fin.partialProd g)) = F.val (Fin.partialProd (Fin.init g))
    apply congrArg F.val
    funext i
    exact (Fin.partialProd_init i).symm

end ContinuousCohomology
