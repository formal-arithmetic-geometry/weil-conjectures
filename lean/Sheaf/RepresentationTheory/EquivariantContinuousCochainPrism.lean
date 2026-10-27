module

public import Mathlib.RepresentationTheory.Continuous.TopRep
public import Mathlib.Topology.Algebra.Field
public import Mathlib.Algebra.Homology.Homotopy
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.LinearAlgebra.FreeModule.Basic

/-!
# Equivariant finite-family prism on jointly continuous cochains

Source: Stacks Project, Tag 019S, equation-homotopy-to-homotopy and its calculation,
simplicial.tex, lines 4739–4846; agent adaptation to permuted finite families.
(blueprint: lem-sfb-equivariant-continuous-cochain-prism).

Evaluation characterizes the actual jointly continuous homogeneous cochains and all
operators uniquely up to evaluation-preserving isomorphism. We use abstract vector spaces,
not an iterated continuous-map model, and extend the complex by zero in negative degrees.
-/

@[expose] public section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits

universe u v w z

namespace ContinuousCohomology

variable (E : Type u) [Field E] [TopologicalSpace E] [IsTopologicalDivisionRing E]
variable (G : Type v) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable (S : Type z) [Fintype S] (a : S → C(G, G))

/-- A precise specification of the homogeneous complex and the prescribed finite-family
operators. The injective evaluation maps have exactly the continuous equivariant functions
as image. The homotopy has the signed insertion formula, with its bottom component zero.

Source: Stacks Project, Tag 019S, equation-homotopy-to-homotopy, with the finite-family
cochain adaptation in steps 1–5 of the node proof.
(blueprint: lem-sfb-equivariant-continuous-cochain-prism). -/
structure EquivariantContinuousPrism (A : TopRep.{w} E G) where
  /-- The abstract homogeneous cochain complex. -/
  B : CochainComplex (ModuleCat.{max v w} E) ℤ
  /-- Evaluation on homogeneous tuples, respecting pointwise vector-space operations. -/
  eval : ∀ n : ℕ, B.X (n : ℤ) →ₗ[E] ((Fin (n + 1) → G) → A)
  /-- Evaluation is faithful. -/
  injective : ∀ n : ℕ, Function.Injective (eval n)
  /-- Every jointly continuous equivariant function, and only such a function, occurs. -/
  range : ∀ (n : ℕ) (F : (Fin (n + 1) → G) → A),
    (∃ f, eval n f = F) ↔ Continuous F ∧
      ∀ (g : G) (x : Fin (n + 1) → G), F (fun i ↦ g * x i) = A.ρ g (F x)
  /-- The complex is extended by zero in negative degrees. -/
  negative : ∀ j : ℤ, j < 0 → IsZero (B.X j)
  /-- Alternating deletion, including all faces. -/
  delta : ∀ (n : ℕ) (f : B.X (n : ℤ)) (x : Fin (n + 2) → G),
    eval (n + 1) ((B.d (n : ℤ) ((n + 1 : ℕ) : ℤ)).hom f) x =
      ∑ j : Fin (n + 2), (-1 : E) ^ j.val • eval n f (x ∘ j.succAbove)
  /-- The finite-family sum is a linear endomorphism of complexes. -/
  L : B ⟶ B
  /-- Its actual value is the specified finite sum of pullbacks. -/
  L_formula : ∀ (n : ℕ) (f : B.X (n : ℤ)) (x : Fin (n + 1) → G),
    eval n ((L.f (n : ℤ)).hom f) x = ∑ s : S, eval n f (fun i ↦ a s (x i))
  /-- The equation delta K + K delta = L - card(S) id in all integer degrees. -/
  prism : Homotopy L (Fintype.card S • 𝟙 B)
  /-- K in degree zero and all negative degrees is zero. -/
  bottom : ∀ j : ℤ, j ≤ 0 → prism.hom j (j - 1) = 0
  /-- K in degree n+1 inserts a_s(x_i) after x_i and transforms all following vertices. -/
  K_formula : ∀ (n : ℕ) (f : B.X ((n + 1 : ℕ) : ℤ)) (x : Fin (n + 1) → G),
    eval n ((prism.hom ((n + 1 : ℕ) : ℤ) (n : ℤ)).hom f) x =
      ∑ s : S, ∑ i : Fin (n + 1), (-1 : E) ^ i.val •
        eval (n + 1) f
          (Fin.insertNth i.succ (a s (x i)) (fun j ↦ if j ≤ i then x j else a s (x j)))
  /-- The degree-zero identity explicitly has the stated sign and endpoints. -/
  degree_zero : ∀ (f : B.X 0) (x : Fin 1 → G),
    eval 0 ((prism.hom 1 0).hom ((B.d 0 1).hom f)) x =
      ∑ s : S, (eval 0 f (fun i ↦ a s (x i)) - eval 0 f x)

/-- The finite-family prism exists simultaneously naturally in every jointly continuous
coefficient representation. The coefficient cochain map is uniquely specified by
postcomposition, and commutes with L and every K, including the zero bottom component.

Source: Stacks Project, Tag 019S, equation-homotopy-to-homotopy and its calculation,
simplicial.tex, lines 4739–4846; agent finite-family cochain adaptation.
(blueprint: lem-sfb-equivariant-continuous-cochain-prism).

Proof: (1) Take the vector subspaces of functions consisting of jointly continuous
homogeneous equivariant maps, with pointwise operations. Alternating deletion preserves
them. Two successive deletions occur in opposite orders with opposite signs, so delta
squares to zero; extend by zero below degree zero. Deletion commutes with applying a_s
to every coordinate, so their finite sum L is a cochain map.
(2) Each tuple substitution in L and K is continuous, and finite signed sums are
continuous and linear. For a fixed g, use the single permutation supplied by the
hypothesis in every coordinate. Equivariance of f followed by reindexing the finite sum
proves equivariance of L and K. No continuity of the chosen permutation is needed.
(3) Specialize lem-trf-coefficient-bar-prism-homotopy to the category with object set G
and one arrow between each pair, constant coefficients E, identity coefficient map,
and object maps id and a_s. Its free-module basis is the tuple basis of
 def-weil-pbc-free-module. The prism sends a tuple to the signed sum obtained by inserting
both x_i and a_s(x_i). Its boundary identity is a_s minus id, including degree zero.
(4) Extend evaluation of f linearly to that tuple free module and evaluate the chain
identity. This gives delta K_s + K_s delta = a_s pullback minus id. Sum over s; the
operators for single s need not preserve equivariance, but their sums do by (2).
For degree zero this gives the displayed sum of f(a_s x) minus f(x). For empty S all
operators and both sides of the equation vanish.
(5) A continuous equivariant linear coefficient map preserves the cochain spaces and
commutes with deletion. Moving it through both finite sums gives naturality of L and K
with the same family a, including K_0 = 0. Only continuity, finite products, finite
sums and linearity were used; no compactness or separation assumption is needed. -/
theorem exists_equivariantContinuousPrism
    (hperm : ∀ g : G, ∃ π : Equiv.Perm S,
      ∀ (s : S) (x : G), a s (g * x) = g * a (π s) x) :
    ∃ D : ∀ (A : TopRep.{w} E G)
        (_hA : Continuous (fun p : G × A ↦ A.ρ p.1 p.2)),
        EquivariantContinuousPrism E G S a A,
      ∀ (A W : TopRep.{w} E G)
        (hA : Continuous (fun p : G × A ↦ A.ρ p.1 p.2))
        (hW : Continuous (fun p : G × W ↦ W.ρ p.1 p.2)) (b : A ⟶ W),
        ∃ bStar : (D A hA).B ⟶ (D W hW).B,
          (∀ (n : ℕ) (f : (D A hA).B.X (n : ℤ)) (x : Fin (n + 1) → G),
            (D W hW).eval n ((bStar.f (n : ℤ)).hom f) x = b ((D A hA).eval n f x)) ∧
          (D A hA).L ≫ bStar = bStar ≫ (D W hW).L ∧
          (∀ i j : ℤ, (D A hA).prism.hom i j ≫ bStar.f j =
            bStar.f i ≫ (D W hW).prism.hom i j) := by
  sorry

end ContinuousCohomology
