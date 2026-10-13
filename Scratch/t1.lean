module
public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.RingTheory.Polynomial.ScaleRoots
public import WeilConjectures.Mathlib.Algebra.Category.Ring.FinitePresentation
@[expose] public section
open CategoryTheory Limits Polynomial
universe u
namespace CommRingCat
variable {J : Type u} [SmallCategory J] {F : J ⥤ CommRingCat.{u}}
example (c : Cocone F) {i j : J} (f : i ⟶ j) (x : F.obj i) :
    c.ι.app j (F.map f x) = c.ι.app i x := by
  rw [← CommRingCat.comp_apply, c.w f]
end CommRingCat
