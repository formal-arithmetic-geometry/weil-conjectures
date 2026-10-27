module

public import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
public import Mathlib.LinearAlgebra.Reflection
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.Data.Rat.Defs
public import Mathlib.Algebra.Group.Submonoid.Basic

/-! # Simple chamber folding of an affine lowering edge

Source: Andersen, The strong linkage principle (1980), Definition 1 and Lemma 1,
printed pp.54–55; the agent-written local calculation in the DAG proof.
(blueprint: lem-sfb-simple-chamber-fold-affine-step)

The helpers use the unbundled lattice and coroot data of this node. In particular,
no perfect pairing, spanning condition on the roots, or semisimplicity is assumed.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

namespace AffineChamberFold

/-- Root dominance for a specified set of simple roots: the difference is a finite
nonnegative integral sum of simple roots. Source: Andersen (1980), Definition 1, p.54
(blueprint: lem-sfb-simple-chamber-fold-affine-step). -/
def Dominance {X : Type u} [AddCommGroup X] (Δ : Set X) (u v : X) : Prop :=
  v - u ∈ AddSubmonoid.closure Δ

/-- The rho-shifted root reflection. The linear reflection is Mathlib's
`Module.preReflection`. Source: Andersen (1980), Definition 1, p.54
(blueprint: lem-sfb-simple-chamber-fold-affine-step). -/
def reflectionDot {X : Type u} [AddCommGroup X]
    (c : X → X →ₗ[ℤ] ℤ) (ρ β v : X) : X :=
  Module.preReflection β (c β) (v + ρ) - ρ

/-- An affine lowering edge, with arguments in source-to-target order. Positivity
of the root and the lowering condition are both explicit. Source: Andersen (1980),
Definition 1, p.54 (blueprint: lem-sfb-simple-chamber-fold-affine-step). -/
def Edge {X : Type u} [AddCommGroup X] (Φ Δ : Set X)
    (c : X → X →ₗ[ℤ] ℤ) (ρ : X) (p : ℤ) (v u : X) : Prop :=
  ∃ β ∈ Φ, β ∈ AddSubmonoid.closure Δ ∧ ∃ n : ℤ, 0 ≤ n ∧
    u = reflectionDot c ρ β v + (n * p) • β ∧ Dominance Δ u v

/-- Fold toward the nonnegative shifted simple-coroot half-space, fixing the wall.
Source: Andersen (1980), Lemma 1, p.54, local chamber-reduction calculation
(blueprint: lem-sfb-simple-chamber-fold-affine-step). -/
def fold {X : Type u} [AddCommGroup X]
    (c : X → X →ₗ[ℤ] ℤ) (ρ α v : X) : X :=
  if 0 ≤ c α (v + ρ) then v else reflectionDot c ρ α v

/-- Simple chamber folding replaces any affine lowering edge by a path of length
at most two, including the empty path when the folded endpoints coincide.

Source: Andersen (1980), Definition 1 and Lemma 1, printed pp.54–55; explicit
agent-written local edge-rewriting proof in the DAG.
(blueprint: lem-sfb-simple-chamber-fold-affine-step)

Proof:
1. Translate to x=v+rho and y=u+rho. Write the edge as y=x-k beta, where
   k=c_beta(x)-np. Independence of the simple roots and positivity of beta imply
   k>=0. Freeness (def-weil-pbc-free-module) makes X inject into its rationalization.
2. The identity c_alpha(alpha)=2 gives s_alpha squared equal to the identity and
   c_alpha(s_alpha z)=-c_alpha(z). For beta different from alpha, reducedness gives
   a positive coefficient away from alpha; reflection leaves it unchanged. The
   sign condition on root coefficients therefore makes gamma=s_alpha beta positive.
3. Covariance gives c_gamma(s_alpha x)=c_beta(x), hence the conjugated edge
   s_alpha x -> s_alpha y has root gamma, the same level n, and coefficient k>=0.
4. Put a=c_alpha(x), b=c_alpha(y). For beta different from alpha, use the original
   edge if both are nonnegative and the conjugated edge if both are negative.
   If a<0<=b, use s_alpha x -> x -> y, with first edge of level zero.
5. If b<0<=a, use x -> s_alpha x -> s_alpha y. Its first edge has level zero,
   and the second is the conjugated edge of step 3. This includes a=0.
6. If beta=alpha, then a>=np>=0 and b=-a+2np. For b>=0 keep the original edge.
   For b<0 the folded target is x-np alpha. When n=0 take the empty path.
   Otherwise divide a=hp+r with 0<=r<p. From a>2np obtain h>=2n.
7. Set z=x-r alpha. Then z=R_(alpha,h)(x) and c_alpha(z)=hp-r.
   The second edge R_(alpha,h-n)(z)=x-np alpha has coefficient np-r>0.
   Both levels h and h-n are nonnegative, so these are two lowering edges.
8. Translate all vertices back by -rho and remove stationary edges if desired.
   Only p>0 is used. No irreducibility or primality is required. If the simple
   roots are empty there is no alpha, so the assertion is vacuous.
-/
theorem simple_chamber_fold_affine_step
    {X : Type u} [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X]
    (Φ : Set X) (hfinite : Φ.Finite) (hzero : (0 : X) ∉ Φ)
    (hreduced : ∀ β ∈ Φ,
      {γ ∈ Φ | ∃ q : ℚ,
        (1 : ℚ) ⊗ₜ[ℤ] γ = q • ((1 : ℚ) ⊗ₜ[ℤ] β)} = {β, -β})
    (c : X → X →ₗ[ℤ] ℤ)
    (hself : ∀ β ∈ Φ, c β β = 2)
    (hneg : ∀ β ∈ Φ, c (-β) = -c β)
    (hreflect : ∀ β ∈ Φ, (Module.preReflection β (c β)) '' Φ = Φ)
    (hcov : ∀ β ∈ Φ, ∀ γ ∈ Φ,
      c (Module.preReflection β (c β) γ) = (c γ).comp (Module.preReflection β (c β)))
    (Δ : Set X) (hsubset : Δ ⊆ Φ)
    (hindependent : LinearIndependent ℚ (fun δ : Δ ↦ (1 : ℚ) ⊗ₜ[ℤ] (δ : X)))
    (hbase : ∀ β ∈ Φ,
      β ∈ AddSubmonoid.closure Δ ∨ -β ∈ AddSubmonoid.closure Δ)
    (ρ : X) (p : ℤ) (hp : 1 ≤ p) (α : X) (hα : α ∈ Δ)
    (v u : X) (hedge : Edge Φ Δ c ρ p v u) :
    ∃ (m : ℕ) (t : Fin (m + 1) → X), m ≤ 2 ∧
      t 0 = fold c ρ α v ∧ t (Fin.last m) = fold c ρ α u ∧
      ∀ j : Fin m, Edge Φ Δ c ρ p (t j.castSucc) (t j.succ) := by
  sorry

end AffineChamberFold
