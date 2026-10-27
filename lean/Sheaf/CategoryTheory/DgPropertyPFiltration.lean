module

public import Sheaf.CategoryTheory.DgAlgebraDerivedCategory
public import Mathlib.Algebra.DirectSum.Basic
public import Mathlib.Algebra.Exact.Basic

/-!
# Property-(P) filtrations of right DG modules

Source: Stacks Project, dga.tex, Tag 09KK, section-P-resolutions
(blueprint: def-sfb-dg-property-p-filtration).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace CategoryTheory.DgAlgebra

/-- An exhaustive increasing filtration starting at zero, with graded right-linear
retractions and DG quotients that are small direct sums of shifts of the regular module.
The injective maps `embedding` realize the stages as actual DG submodules of `P`.
Exactness and surjectivity identify `layer p` with `F (p+1) / F p`. The additive
coordinates and their differential/action equations identify that quotient with
`⨁ j, A[shift p j]`, including its differential sign and unchanged right action.
`HEq` in the action equation is only the canonical reassociation of integer degrees.
Source: Stacks Project, dga.tex, Tag 09KK, section-P-resolutions, with the filtration
reindexed to start at F₀ = 0 (blueprint: def-sfb-dg-property-p-filtration). -/
structure PropertyPFiltration (A : Algebra.{u}) (P : RightModule A) where
  F : ℕ → RightModule A
  embedding (p : ℕ) : F p ⟶ P
  embedding_injective (p : ℕ) (n : ℤ) :
    Function.Injective (((underlying A).map (embedding p)).f n)
  initial (n : ℤ) : Subsingleton (((underlying A).obj (F 0)).X n)
  inclusion (p : ℕ) : F p ⟶ F (p + 1)
  compatibility (p : ℕ) : inclusion p ≫ embedding (p + 1) = embedding p
  exhaustive (n : ℤ) (x : ((underlying A).obj P).X n) :
    ∃ (p : ℕ) (y : ((underlying A).obj (F p)).X n),
      (((underlying A).map (embedding p)).f n) y = x
  retraction (p : ℕ) (n : ℤ) :
    ((underlying A).obj (F (p + 1))).X n →+ ((underlying A).obj (F p)).X n
  retraction_left_inverse (p : ℕ) (n : ℤ) (x : ((underlying A).obj (F p)).X n) :
    retraction p n ((((underlying A).map (inclusion p)).f n) x) = x
  retraction_action (p : ℕ) (n m : ℤ) (x : ((underlying A).obj (F (p + 1))).X n)
      (a : A.X.X m) :
    retraction p (n + m) (act A (F (p + 1)) n m x a) =
      act A (F p) n m (retraction p n x) a
  layer : ℕ → RightModule A
  projection (p : ℕ) : F (p + 1) ⟶ layer p
  projection_surjective (p : ℕ) (n : ℤ) :
    Function.Surjective (((underlying A).map (projection p)).f n)
  layer_exact (p : ℕ) (n : ℤ) :
    Function.Exact (((underlying A).map (inclusion p)).f n)
      (((underlying A).map (projection p)).f n)
  index : ℕ → Type u
  shift (p : ℕ) : index p → ℤ
  coordinate (p : ℕ) (n : ℤ) :
    ((underlying A).obj (layer p)).X n ≃+
      DirectSum (index p) (fun j : index p ↦ A.X.X (n + shift p j))
  coordinate_differential (p : ℕ) (n : ℤ) (x : ((underlying A).obj (layer p)).X n)
      (j : index p) :
    coordinate p (n + 1) ((((underlying A).obj (layer p)).d n (n + 1)) x) j =
      (shift p j).negOnePow •
        A.X.d (n + shift p j) (n + 1 + shift p j) (coordinate p n x j)
  coordinate_action (p : ℕ) (n m : ℤ) (x : ((underlying A).obj (layer p)).X n)
      (a : A.X.X m) (j : index p) :
    HEq (coordinate p (n + m) (act A (layer p) n m x a) j)
      (act A (regular A) (n + shift p j) m (coordinate p n x j) a)

/-- A right DG module has property (P) when it admits the specified filtration.
Source: Stacks Project, dga.tex, Tag 09KK, section-P-resolutions
(blueprint: def-sfb-dg-property-p-filtration). -/
def HasPropertyP (A : Algebra.{u}) (P : RightModule A) : Prop :=
  Nonempty (PropertyPFiltration A P)

end CategoryTheory.DgAlgebra
