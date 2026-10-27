module

public import Sheaf.CategoryTheory.DgAlgebraDerivedCategory

/-!
# Specified finite semi-free filtrations of right dg modules

Source: Stacks Project, dga.tex, Tag 09R2, lemma-factor-through-nicer
(blueprint: def-sfb-dg-finite-semi-free-filtration).

Submodules are represented by degreewise injective dg maps into the given module.
The zero initial term is numbered 0, so layer i is the quotient F(i+1)/F(i).
The specified coproduct cocone records the coordinates, not only an abstract
isomorphism type of the layer. Its summands have the actual signed shift differential
and unchanged right action, as recorded by ShiftComparison.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.DgAlgebra

/-- A filtration with n+1 free layers, including the bottom layer. Exactness and
surjectivity present the actual layer quotients. The initial term is zero and the
last inclusion identifies the last term with T. Each cocone specifies the dg
isomorphism from the sum of the indicated shifts to its layer; no generators or
splittings of the filtration itself are chosen.
Source: Stacks, dga.tex, Tag 09R2, lemma-factor-through-nicer, its given filtration
(blueprint: def-sfb-dg-finite-semi-free-filtration). -/
structure FiniteSemiFreeFiltration (A : Algebra.{u}) (T : RightModule A) (n : ℕ) where
  term : Fin (n + 2) → RightModule A
  inclusion (i : Fin (n + 2)) : term i ⟶ T
  injective (i : Fin (n + 2)) (p : ℤ) :
    Function.Injective (((underlying A).map (inclusion i)).f p)
  initial (p : ℤ) : Subsingleton (((underlying A).obj (term 0)).X p)
  final (p : ℤ) :
    Function.Surjective (((underlying A).map (inclusion (Fin.last (n + 1)))).f p)
  step (i : Fin (n + 1)) : term i.castSucc ⟶ term i.succ
  compatibility (i : Fin (n + 1)) : step i ≫ inclusion i.succ = inclusion i.castSucc
  layer : Fin (n + 1) → RightModule A
  projection (i : Fin (n + 1)) : term i.succ ⟶ layer i
  surjective (i : Fin (n + 1)) (p : ℤ) :
    Function.Surjective (((underlying A).map (projection i)).f p)
  exact (i : Fin (n + 1)) (p : ℤ) :
    Function.Exact (((underlying A).map (step i)).f p)
      (((underlying A).map (projection i)).f p)
  index : Fin (n + 1) → Type u
  degree (i : Fin (n + 1)) : index i → ℤ
  summand (i : Fin (n + 1)) : index i → RightModule A
  shift (i : Fin (n + 1)) (j : index i) :
    ShiftComparison A (degree i j) (regular A) (summand i j)
  coprojection (i : Fin (n + 1)) (j : index i) : summand i j ⟶ layer i
  isColimit (i : Fin (n + 1)) : IsColimit (Cofan.mk (layer i) (coprojection i))

end CategoryTheory.DgAlgebra
