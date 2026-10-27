module

public import Sheaf.CategoryTheory.DgAlgebraDerivedCategory
public import Mathlib.Algebra.Module.CharacterModule

/-!
# Complete dual-free filtrations of right DG modules

Source: Stacks Project, dga.tex, property (I) immediately before Tag 09KR,
and the character-dual convention preceding Tag 09K4
(blueprint: def-sfb-dg-complete-dual-free-filtration).

The quotients and layers are specified by surjections and exact inclusions.
Thus the filtration is the kernels of the quotient projections. Completeness
is unique lifting of every compatible tuple, rather than a choice of a limit.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace CategoryTheory.DgAlgebra

/-- A complete decreasing filtration with graded-split quotient transitions and
products of shifted character-dual layers. `Q p` represents I/F_p, with F_p the
kernel of `projection p`. `layer p` represents F_p/F_(p+1), by `layer_exact`.
`coordinate` identifies every homogeneous layer with the full product of
Hom_Z(A^(-(n+k)), Q/Z). The two coordinate equations pin its DG differential
and right action. The shifted dual differential has sign (-1)^(n+1), since
(-1)^k (-1)^(n+k+1) = (-1)^(n+1). Sections need not commute with differentials.
Source: Stacks Project, dga.tex, property (I) before Tag 09KR and the
character-dual conventions before Tag 09K4
(blueprint: def-sfb-dg-complete-dual-free-filtration). -/
structure CompleteDualFreeFiltration (A : Algebra.{u}) (I : RightModule A) where
  Q : ℕ → RightModule A
  projection (p : ℕ) : I ⟶ Q p
  projection_surjective (p : ℕ) (n : ℤ) :
    Function.Surjective (((underlying A).map (projection p)).f n)
  initial (n : ℤ) : Subsingleton (((underlying A).obj (Q 0)).X n)
  transition (p : ℕ) : Q (p + 1) ⟶ Q p
  compatibility (p : ℕ) : projection (p + 1) ≫ transition p = projection p
  complete (n : ℤ) (x : ∀ p : ℕ, ((underlying A).obj (Q p)).X n)
      (hx : ∀ p : ℕ, (((underlying A).map (transition p)).f n) (x (p + 1)) = x p) :
    ∃! y : ((underlying A).obj I).X n,
      ∀ p : ℕ, (((underlying A).map (projection p)).f n) y = x p
  sectionMap (p : ℕ) (n : ℤ) :
    ((underlying A).obj (Q p)).X n →+ ((underlying A).obj (Q (p + 1))).X n
  section_right_inverse (p : ℕ) (n : ℤ) (x : ((underlying A).obj (Q p)).X n) :
    (((underlying A).map (transition p)).f n) (sectionMap p n x) = x
  section_action (p : ℕ) (n m : ℤ) (x : ((underlying A).obj (Q p)).X n)
      (a : A.X.X m) :
    sectionMap p (n + m) (act A (Q p) n m x a) =
      act A (Q (p + 1)) n m (sectionMap p n x) a
  layer : ℕ → RightModule A
  inclusion (p : ℕ) : layer p ⟶ Q (p + 1)
  layer_injective (p : ℕ) (n : ℤ) :
    Function.Injective (((underlying A).map (inclusion p)).f n)
  layer_exact (p : ℕ) (n : ℤ) :
    Function.Exact (((underlying A).map (inclusion p)).f n)
      (((underlying A).map (transition p)).f n)
  index : ℕ → Type u
  shift (p : ℕ) : index p → ℤ
  coordinate (p : ℕ) (n : ℤ) :
    ((underlying A).obj (layer p)).X n ≃+
      (∀ t : index p, CharacterModule (A.X.X (-(n + shift p t))))
  coordinate_differential (p : ℕ) (n : ℤ) (x : ((underlying A).obj (layer p)).X n)
      (t : index p) (b : A.X.X (-(n + 1 + shift p t))) :
    coordinate p (n + 1) ((((underlying A).obj (layer p)).d n (n + 1)) x) t b =
      (n + 1).negOnePow • coordinate p n x t
        (cast (congrArg (fun r : ℤ ↦ (A.X.X r : Type u)) (by omega))
          ((A.X.d (-(n + 1 + shift p t)) (-(n + 1 + shift p t) + 1)) b))
  coordinate_action (p : ℕ) (n m : ℤ) (x : ((underlying A).obj (layer p)).X n)
      (a : A.X.X m) (t : index p) (b : A.X.X (-(n + m + shift p t))) :
    coordinate p (n + m) (act A (layer p) n m x a) t b =
      coordinate p n x t
        (cast (congrArg (fun r : ℤ ↦ (A.X.X r : Type u)) (by omega))
          (act A (regular A) m (-(n + m + shift p t)) a b))

end CategoryTheory.DgAlgebra
