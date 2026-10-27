/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicTopology.SimplicialObject.Basic
public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.Algebra.MvPolynomial.Basic

/-!
# Split polynomial boundary attachment

Source: Stacks Project, Cotangent Complex, Tag 08PX (`proposition-polynomial`),
inductive step, with compatible split variables as in Simplicial, Tag 017P
(`definition-split`) (blueprint: lem-sfb-split-polynomial-boundary-attachment).

The auxiliary definitions only spell out the ordinal labels and boundary equations
in the statement. Polynomial algebras and truncated simplicial objects are Mathlib's.
-/

@[expose] public section

set_option autoImplicit false

universe u v w z

open CategoryTheory Opposite Simplicial

namespace Algebra.SplitPolynomialAttachment

/-- The degree `k` object of the truncated simplex category.
Source: Stacks, Tag 0180 (blueprint: lem-sfb-split-polynomial-boundary-attachment). -/
def degree (n k : ℕ) (h : k ≤ n) : SimplexCategory.Truncated n :=
  ⟨SimplexCategory.mk k, h⟩

/-- Labels `(j,e,σ)` of the split polynomial variables in degree `k`.
Surjectivity forces `j ≤ k`, so no variables in higher nondegenerate degrees occur.
Source: Stacks, Tags 08PX and 017P
(blueprint: lem-sfb-split-polynomial-boundary-attachment). -/
def Variable {n : ℕ} (E : Fin (n + 1) → Type w) (k : ℕ) : Type w :=
  Σ j : Fin (n + 1), E j ×
    {σ : SimplexCategory.mk k ⟶ SimplexCategory.mk j.val //
      Function.Surjective σ.toOrderHom}

/-- Substitution of a surjection in a split variable label, leaving its generator fixed.
Source: Stacks, Tags 08PX and 017P
(blueprint: lem-sfb-split-polynomial-boundary-attachment). -/
def precompose {n k l : ℕ} {E : Fin (n + 1) → Type w}
    (τ : SimplexCategory.mk l ⟶ SimplexCategory.mk k)
    (hτ : Function.Surjective τ.toOrderHom) (x : Variable E k) : Variable E l :=
  ⟨x.1, x.2.1, τ ≫ x.2.2.1, x.2.2.2.comp hτ⟩

/-- The usual boundary equations, with no face--face condition in degree zero.
For degree `r+1`, indices `i ≤ j` encode the original pair `i < j+1`:
`d_i a_{j+1} = d_j a_i`.
Source: Stacks, Tag 08PX, compatible-boundary repair using Tag 017P
(blueprint: lem-sfb-split-polynomial-boundary-attachment). -/
def CompatibleFaces {A : Type u} [CommRing A] :
    (n : ℕ) → (P : SimplicialObject.Truncated (CommAlgCat.{v} A) n) →
      (Fin (n + 2) → P.obj (op (degree n n le_rfl))) → Prop
  | 0, _, _ => True
  | r + 1, P, a => ∀ (i j : Fin (r + 2)), i ≤ j →
      P.map (SimplexCategory.Truncated.Hom.tr (SimplexCategory.δ i)
        (Nat.le_succ r) le_rfl).op (a j.succ) =
      P.map (SimplexCategory.Truncated.Hom.tr (SimplexCategory.δ j)
        (Nat.le_succ r) le_rfl).op (a i.castSucc)

/-- Attach finitely many polynomial generators with prescribed compatible faces, retaining
all old degrees literally and every split degeneracy by composition of surjections.
The `Sum` of variable types presents the displayed iterated polynomial algebra over `A`.
The equality `hP` is literal equality of the restricted functor with `P`; `eqToHom hP`
only transports expressions across this equality. Naturality of the augmentations and
functoriality of `P'` include all augmentation and simplicial identities.

Source: Stacks Project, Cotangent Complex, Tag 08PX (`proposition-polynomial`),
inductive step, repaired by the split indexing of Simplicial, Tag 017P
(`definition-split`) (blueprint: lem-sfb-split-polynomial-boundary-attachment).

Proof:
1. Form `Q = A[x_(e,σ), y_t]`. For a new face `D_i`, send an old variable to
   `P(σ δ_i)(x_(e,id))`, and send `y_t` to `a t i`. Define each new degeneracy
   by composing the surjection label. Polynomial evaluation and uniqueness
   (`def-weil-pbc-mv-polynomial-ring`) give these algebra maps.
2. Check face--face identities on variables. On `y_t` they are `hfaces`;
   on old variables they follow from old functoriality and the coface identity.
   No such check is required for `n = 0`.
3. Check mixed face--degeneracy identities on old variables using the ordinal
   identities for omitting and repeating vertices. The two middle cases are
   identities, and all other cases use maps wholly in the old truncation.
4. Check degeneracy--degeneracy identities by equality of composite surjection
   labels, including the case of collapsing three consecutive vertices.
5. Apply `lem-sfb-truncated-simplex-presentation` to these objects and maps.
   Keep the old objects and operators literally, obtaining `hP`. Every
   surjection is a composite of codegeneracies, giving the last displayed clause.
6. Augment each old variable by the augmentation of its nondegenerate source
   generator and `y_t` by `b t`. The equations `haug` and old augmentation
   naturality give every new augmentation identity by polynomial uniqueness.
   The natural-transformation clause of recognition gives `ε'`.
   This works with empty variable sets, empty `T`, and the zero ring. -/
theorem exists_boundary_attachment
    {A : Type u} [CommRing A] {B : Type v} [CommRing B] [Algebra A B]
    (n : ℕ) (P : SimplicialObject.Truncated (CommAlgCat.{v} A) n)
    (ε : P ⟶ (Functor.const (SimplexCategory.Truncated n)ᵒᵖ).obj (CommAlgCat.of A B))
    (E : Fin (n + 1) → Type w) [∀ j : Fin (n + 1), Finite (E j)]
    (p : ∀ k : Fin (n + 1), MvPolynomial (Variable E k.val) A ≃ₐ[A]
      P.obj (op (degree n k.val (Nat.le_of_lt_succ k.isLt))))
    (hdeg : ∀ (k l : Fin (n + 1))
      (τ : SimplexCategory.mk l.val ⟶ SimplexCategory.mk k.val)
      (hτ : Function.Surjective τ.toOrderHom) (x : Variable E k.val),
      P.map (SimplexCategory.Truncated.Hom.tr τ
        (Nat.le_of_lt_succ l.isLt) (Nat.le_of_lt_succ k.isLt)).op
          (p k (MvPolynomial.X x)) = p l (MvPolynomial.X (precompose τ hτ x)))
    (T : Type z) [Finite T] (b : T → B)
    (a : T → Fin (n + 2) → P.obj (op (degree n n le_rfl)))
    (haug : ∀ (t : T) (i : Fin (n + 2)), ε.app (op (degree n n le_rfl)) (a t i) = b t)
    (hfaces : ∀ t : T, CompatibleFaces n P (a t)) :
    ∃ (P' : SimplicialObject.Truncated (CommAlgCat.{v} A) (n + 1))
      (ε' : P' ⟶ (Functor.const (SimplexCategory.Truncated (n + 1))ᵒᵖ).obj
        (CommAlgCat.of A B))
      (hP : (SimplicialObject.Truncated.trunc (CommAlgCat.{v} A) (n + 1) n
        (Nat.le_succ n)).obj P' = P)
      (q : MvPolynomial (Variable E (n + 1) ⊕ T) A ≃ₐ[A]
        P'.obj (op (degree (n + 1) (n + 1) le_rfl))),
      Functor.whiskerLeft (SimplexCategory.Truncated.incl n (n + 1) (Nat.le_succ n)).op ε' =
        eqToHom hP ≫ ε ∧
      (∀ (t : T) (i : Fin (n + 2)),
        (eqToHom hP).app (op (degree n n le_rfl))
          (P'.map (SimplexCategory.Truncated.Hom.tr (SimplexCategory.δ i)
            (Nat.le_succ n) le_rfl).op (q (MvPolynomial.X (Sum.inr t)))) = a t i) ∧
      (∀ t : T, ε'.app (op (degree (n + 1) (n + 1) le_rfl))
        (q (MvPolynomial.X (Sum.inr t))) = b t) ∧
      (∀ (k : Fin (n + 1))
        (τ : SimplexCategory.mk (n + 1) ⟶ SimplexCategory.mk k.val)
        (hτ : Function.Surjective τ.toOrderHom) (x : Variable E k.val),
        P'.map (SimplexCategory.Truncated.Hom.tr τ le_rfl
          (Nat.le_trans (Nat.le_of_lt_succ k.isLt) (Nat.le_succ n))).op
            ((eqToHom hP.symm).app (op (degree n k.val (Nat.le_of_lt_succ k.isLt)))
              (p k (MvPolynomial.X x))) =
          q (MvPolynomial.X (Sum.inl (precompose τ hτ x)))) := by
  sorry

end Algebra.SplitPolynomialAttachment
