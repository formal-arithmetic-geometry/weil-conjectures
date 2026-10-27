/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q17
-/
module

public import Mathlib.AlgebraicTopology.SimplicialObject.Op
public import Mathlib.AlgebraicTopology.ExtraDegeneracy

/-!
# Ordinal reversal, extra degeneracies, and simplicial homotopies

Source: Stacks Project, Tag 08ND, `lemma-standard-simplicial-homotopy`, in Situation
08N9, with the explicit ordinal and prism-index calculations in the DAG
(blueprint: lem-trf-simplicial-reversal-extra-degeneracies-homotopy).

The reversal functor, its formula, involution, and face and degeneracy identities
are Mathlib's `SimplexCategory.rev`, `rev_map_apply`, `rev_map_rev_map`,
`SimplicialObject.opFunctor`, `opFunctor_obj_δ`, and `opFunctor_obj_σ`.
The statements below supply the remaining transport and compatibility clauses.
-/

@[expose] public section

universe u v u' v'

set_option autoImplicit false

open CategoryTheory Opposite Simplicial
open _root_.SimplicialObject

namespace CategoryTheory.SimplicialObject

variable {C : Type u} [Category.{v} C]

/-- Reverse an augmentation by precomposition, keeping its point and degree components.
Source: Stacks Project, Tag 08ND, auxiliary reversal calculation, DAG steps 1--2
(blueprint: lem-trf-simplicial-reversal-extra-degeneracies-homotopy). -/
def Augmented.ordinalReverse (X : Augmented C) : Augmented C where
  left := opFunctor.obj X.left
  right := X.right
  hom := Functor.whiskerLeft SimplexCategory.rev.op X.hom

/-- Reversal fixes the unique map to degree zero, and hence the explicit section formula.
Source: Stacks Project, Tag 08ND, auxiliary reversal calculation
(blueprint: lem-trf-simplicial-reversal-extra-degeneracies-homotopy).

Proof (DAG steps 2 and 5): the value of the reversed map to [0] is always zero,
so it is the same unique map. Precomposition by reversal therefore gives the same
operator on W. Composing this equality with t in degree zero gives the last equality. -/
theorem ordinalReverse_terminal (W : SimplicialObject C) (Y : C) (t : Y ⟶ W _⦋0⦌)
    (n : ℕ) :
    SimplexCategory.rev.map (SimplexCategory.isTerminalZero.from ⦋n⦌) =
      SimplexCategory.isTerminalZero.from ⦋n⦌ ∧
    (opFunctor.obj W).map (SimplexCategory.isTerminalZero.from ⦋n⦌).op =
      W.map (SimplexCategory.isTerminalZero.from ⦋n⦌).op ∧
    t ≫ (opFunctor.obj W).map (SimplexCategory.isTerminalZero.from ⦋n⦌).op =
      t ≫ W.map (SimplexCategory.isTerminalZero.from ⦋n⦌).op := by
  sorry

/-- The supplied right extra-degeneracy maps become exactly Mathlib's left data.
The section has the unchanged explicit components, also after applying any functor.
Source: Stacks Project, Tag 08ND, auxiliary reversal calculation
(blueprint: lem-trf-simplicial-reversal-extra-degeneracies-homotopy).

Proof (DAG steps 1--5 and 9): use Mathlib's reversal of faces and degeneracies.
On degree n+1 the zeroth reversed face is d_(n+1), and on degree one the first
reversed face is d_0. In the remaining face equations substitute k = n+1-i;
in the degeneracy equations substitute k = n-i. These are bijections of precisely
the supplied index ranges. The augmentation is unchanged. Thus the same t and t'
fill ExtraDegeneracy, without any extra relation. Its section is t' followed by
the unique operator to [0], which reversal fixes by ordinalReverse_terminal.
Functoriality follows because a functor maps compositions and identities to those
of the images; in particular it maps these very same components, not chosen replacements. -/
theorem exists_extraDegeneracy_ordinalReverse (X : Augmented C)
    (t' : X.right ⟶ X.left _⦋0⦌)
    (t : ∀ n : ℕ, X.left _⦋n⦌ ⟶ X.left _⦋n + 1⦌)
    (hε : t' ≫ X.hom.app (op ⦋0⦌) = 𝟙 X.right)
    (hlast : ∀ n : ℕ, t n ≫ X.left.δ (Fin.last (n + 1)) = 𝟙 (X.left _⦋n⦌))
    (hfirst : t 0 ≫ X.left.δ 0 = X.hom.app (op ⦋0⦌) ≫ t')
    (hδ : ∀ (n : ℕ) (i : Fin (n + 2)),
      t (n + 1) ≫ X.left.δ i.castSucc = X.left.δ i ≫ t n)
    (hσ : ∀ (n : ℕ) (i : Fin (n + 1)),
      t n ≫ X.left.σ i.castSucc = X.left.σ i ≫ t (n + 1)) :
    ∃ ed : Augmented.ExtraDegeneracy X.ordinalReverse,
      ed.s' = t' ∧ (∀ n : ℕ, ed.s n = t n) ∧
      (∀ n : ℕ, ed.section_.app (op ⦋n⦌) =
        t' ≫ X.left.map (SimplexCategory.isTerminalZero.from ⦋n⦌).op) ∧
      (∀ (D : Type u') [Category.{v'} D] (F : C ⥤ D),
        (ed.map F).s' = F.map t' ∧
        (∀ n : ℕ, (ed.map F).s n = F.map (t n)) ∧
        (∀ n : ℕ, (ed.map F).section_.app (op ⦋n⦌) =
          F.map (t' ≫ X.left.map (SimplexCategory.isTerminalZero.from ⦋n⦌).op))) := by
  sorry

/-- Every section of the reversed augmentation gives a section with identical components.
The component characterization also specifies its compatibility with every functor.
Source: Stacks Project, Tag 08ND, auxiliary reversal calculation
(blueprint: lem-trf-simplicial-reversal-extra-degeneracies-homotopy).

Proof (DAG steps 1, 2, 5, 9): use the same components for a. Naturality of b at
r(alpha), together with r(r(alpha)) = alpha, proves naturality of a at alpha.
The section equality is unchanged in each degree. Applying any functor to the
component equalities gives the last assertion, including evaluation functors. -/
theorem exists_section_of_ordinalReverse (X : Augmented C)
    (b : (const C).obj X.right ⟶ X.ordinalReverse.left)
    (hb : b ≫ X.ordinalReverse.hom = 𝟙 _) :
    ∃ a : (const C).obj X.right ⟶ X.left,
      a ≫ X.hom = 𝟙 _ ∧
      (∀ n : ℕ, a.app (op ⦋n⦌) = b.app (op ⦋n⦌)) ∧
      (∀ (D : Type u') [Category.{v'} D] (F : C ⥤ D) (n : ℕ),
        F.map (a.app (op ⦋n⦌)) = F.map (b.app (op ⦋n⦌))) := by
  sorry

/-- A reversed homotopy transports with the prescribed reversed indices and endpoints.
The component formula is retained under every functor, including parameter evaluation.
Source: Stacks Project, Tag 08ND, auxiliary reversal calculation
(blueprint: lem-trf-simplicial-reversal-extra-degeneracies-homotopy).

Proof (DAG steps 6--9): put K_j^n = H_(n-j)^n. Reversal of the two endpoint
faces gives d_0 K_0 = f and d_(n+1) K_n = g, the endpoints of Homotopy g f.
If i<j, the reversed face index n+1-i is greater than n-j+1, so the original
upper face identity gives the lower identity for K. If i>j+1, it is less than
n-j, so the original lower identity gives the upper one. The middle identity
at j follows from that at n-j-1, with the two sides exchanged. For degeneracies,
i≤j becomes n+1-i>n-j and uses the upper original identity; i>j becomes
n+1-i≤n-j and uses the lower original identity. All indices stay in range,
including degree zero. Finally whiskerRight applies F to each component,
so its components are exactly F.map (H.h i.rev). -/
theorem exists_homotopy_of_ordinalReverse {A B : SimplicialObject C} (f g : A ⟶ B)
    (H : Homotopy (opFunctor.map f) (opFunctor.map g)) :
    ∃ K : Homotopy g f,
      (∀ (n : ℕ) (i : Fin (n + 1)), K.h i = H.h i.rev) ∧
      (∀ (D : Type u') [Category.{v'} D] (F : C ⥤ D) (n : ℕ) (i : Fin (n + 1)),
        (K.whiskerRight F).h i = F.map (H.h i.rev)) := by
  sorry

/-- Compatible maps of extra-degeneracy diagrams stay compatible after reversal;
their explicit sections commute as well. No extra-degeneracy laws are needed for
this compatibility itself. Source: Stacks Project, Tag 08ND, DAG step 9
(blueprint: lem-trf-simplicial-reversal-extra-degeneracies-homotopy).

Proof: reversal keeps the components of u, v, t, and t' unchanged, giving the
first two equations. For the last, naturality of u at q_n moves it past W(q_n),
and the given degree-zero compatibility then moves it past t'. -/
theorem ordinalReverse_extraDegeneracy_naturality {X X' : Augmented C}
    (u : X ⟶ X') (t' : X.right ⟶ X.left _⦋0⦌)
    (t : ∀ n : ℕ, X.left _⦋n⦌ ⟶ X.left _⦋n + 1⦌)
    (t'' : X'.right ⟶ X'.left _⦋0⦌)
    (t₂ : ∀ n : ℕ, X'.left _⦋n⦌ ⟶ X'.left _⦋n + 1⦌)
    (hzero : t' ≫ u.left.app (op ⦋0⦌) = u.right ≫ t'')
    (hdeg : ∀ n : ℕ, t n ≫ u.left.app (op ⦋n + 1⦌) =
      u.left.app (op ⦋n⦌) ≫ t₂ n) :
    t' ≫ (opFunctor.map u.left).app (op ⦋0⦌) = u.right ≫ t'' ∧
    (∀ n : ℕ, t n ≫ (opFunctor.map u.left).app (op ⦋n + 1⦌) =
      (opFunctor.map u.left).app (op ⦋n⦌) ≫ t₂ n) ∧
    (∀ n : ℕ,
      (t' ≫ X.left.map (SimplexCategory.isTerminalZero.from ⦋n⦌).op) ≫
          u.left.app (op ⦋n⦌) =
        u.right ≫ (t'' ≫ X'.left.map (SimplexCategory.isTerminalZero.from ⦋n⦌).op)) := by
  sorry

/-- Compatible homotopy diagrams remain compatible when the prism indices are reversed.
This covers any outputs with the prescribed components, rather than a pointwise choice.
Source: Stacks Project, Tag 08ND, DAG step 9
(blueprint: lem-trf-simplicial-reversal-extra-degeneracies-homotopy).

Proof: substitute n-j for j in hH. Replace the resulting components by those
of K and K' using hK and hK'. The maps u and v have the same components under
opFunctor, so this is exactly naturality of the transported homotopies. -/
theorem ordinalReverse_homotopy_naturality
    {A B A' B' : SimplicialObject C} {f g : A ⟶ B} {f' g' : A' ⟶ B'}
    (H : Homotopy (opFunctor.map f) (opFunctor.map g))
    (H' : Homotopy (opFunctor.map f') (opFunctor.map g'))
    (K : Homotopy g f) (K' : Homotopy g' f')
    (hK : ∀ (n : ℕ) (i : Fin (n + 1)), K.h i = H.h i.rev)
    (hK' : ∀ (n : ℕ) (i : Fin (n + 1)), K'.h i = H'.h i.rev)
    (u : A ⟶ A') (v : B ⟶ B')
    (hH : ∀ (n : ℕ) (i : Fin (n + 1)),
      H.h i ≫ (opFunctor.map v).app (op ⦋n + 1⦌) =
        (opFunctor.map u).app (op ⦋n⦌) ≫ H'.h i) :
    ∀ (n : ℕ) (i : Fin (n + 1)),
      K.h i ≫ v.app (op ⦋n + 1⦌) = u.app (op ⦋n⦌) ≫ K'.h i := by
  sorry

/-- The transfer of arbitrary sections commutes with maps of augmented diagrams.
Source: Stacks Project, Tag 08ND, DAG steps 5 and 9
(blueprint: lem-trf-simplicial-reversal-extra-degeneracies-homotopy).

Proof: in each degree replace a and a' by b and b', respectively. The assumed
square for b and b' then gives the desired square, since reversal leaves the
components of u unchanged. Extensionality of natural transformations finishes. -/
theorem ordinalReverse_section_naturality {X X' : Augmented C} (u : X ⟶ X')
    (b : (const C).obj X.right ⟶ X.ordinalReverse.left)
    (b' : (const C).obj X'.right ⟶ X'.ordinalReverse.left)
    (a : (const C).obj X.right ⟶ X.left)
    (a' : (const C).obj X'.right ⟶ X'.left)
    (ha : ∀ n : ℕ, a.app (op ⦋n⦌) = b.app (op ⦋n⦌))
    (ha' : ∀ n : ℕ, a'.app (op ⦋n⦌) = b'.app (op ⦋n⦌))
    (hb : b ≫ opFunctor.map u.left = (const C).map u.right ≫ b') :
    a ≫ u.left = (const C).map u.right ≫ a' := by
  sorry

/-- Reversal commutes with postcomposition on objects, arrows, and augmentations.
In particular, take F to be evaluation at any object of a parameter category.
Source: Stacks Project, Tag 08ND, DAG steps 1 and 9
(blueprint: lem-trf-simplicial-reversal-extra-degeneracies-homotopy).

Proof: both sides on an object n are F(W_n); both sides on an operator alpha
are F(W(r(alpha))). Both arrow components are F(f_n), and both augmentations
have point F(Y) and components F(p_n). Functor and natural-transformation
extensionality give the three equalities. Together with the component formulas
for the transported data, sections, and homotopies this gives evaluation
compatibility in a parameter functor category, without a choice of pointwise data. -/
theorem ordinalReverse_whiskering {D : Type u'} [Category.{v'} D] (F : C ⥤ D)
    {A B : SimplicialObject C} (f : A ⟶ B) (X : Augmented C) :
    ((whiskering C D).obj F).obj (opFunctor.obj A) =
      opFunctor.obj (((whiskering C D).obj F).obj A) ∧
    Functor.whiskerRight (opFunctor.map f) F =
      opFunctor.map (Functor.whiskerRight f F) ∧
    ((Augmented.whiskering C D).obj F).obj X.ordinalReverse =
      (((Augmented.whiskering C D).obj F).obj X).ordinalReverse := by
  sorry

end CategoryTheory.SimplicialObject
