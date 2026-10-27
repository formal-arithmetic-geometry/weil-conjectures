module

public import Sheaf.CategoryTheory.DgAlgebraHomotopyStructure

/-!
# DG module cone coordinates

Source: Stacks Project, dga.tex, definition-shift, definition-cone, definition-homotopy
(blueprint: def-sfb-dg-module-cone-calculus).

Actions are data on the specified underlying complexes. No action or module is chosen
from an existence theorem. The DG homotopy quotient is imported from
`DgAlgebraHomotopyStructure`.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.MonoidalOpposite CochainComplex.HomComplex

namespace CategoryTheory.DgAlgebra

/-- An action on a specified complex, including its unit and associativity laws.
Source: Stacks, definition-dgm (blueprint: def-sfb-dg-module-cone-calculus). -/
abbrev ActionOn (A : Algebra.{u}) (C : Complex.{u}) := ModObj (mop A.X) (mop C)

/-- The module with the supplied underlying complex and actual action.
Source: Stacks, definition-dgm (blueprint: def-sfb-dg-module-cone-calculus). -/
def moduleOn (A : Algebra.{u}) (C : Complex.{u}) (a : ActionOn A C) : RightModule A :=
  @Mod.mk _ _ _ _ _ _ _ _ (mop C) a

/-- Evaluate an action on homogeneous elements.
Source: Stacks, definition-dgm (blueprint: def-sfb-dg-module-cone-calculus). -/
def actOn (A : Algebra.{u}) (C : Complex.{u}) (a : ActionOn A C) (p q : ℤ)
    (m : C.X p) (x : A.X.X q) : C.X (p + q) :=
  act A (moduleOn A C a) p q m x

/-- The unchanged right action on the actual shifted complex.
Source: Stacks, definition-shift (blueprint: def-sfb-dg-module-cone-calculus). -/
structure ShiftAction (A : Algebra.{u}) (M : RightModule A) (n : ℤ) where
  action : ActionOn A (((underlying A).obj M)⟦n⟧)
  unchanged (p q : ℤ) (m : (((underlying A).obj M)⟦n⟧).X p) (a : A.X.X q) :
    HEq
      ((((underlying A).obj M).shiftFunctorObjXIso n (p + q) (p + q + n) rfl).hom
        (actOn A _ action p q m a))
      (act A M (p + n) q
        ((((underlying A).obj M).shiftFunctorObjXIso n p (p + n) rfl).hom m) a)

/-- Componentwise action on the actual cone complex, in Mathlib's order (x,y).
Source: Stacks, definition-cone (blueprint: def-sfb-dg-module-cone-calculus). -/
structure ConeAction (A : Algebra.{u}) (M N : RightModule A)
    (f : (underlying A).obj M ⟶ (underlying A).obj N) where
  action : ActionOn A (CochainComplex.mappingCone f)
  target_action (p q : ℤ) (m : (CochainComplex.mappingCone f).X p) (a : A.X.X q) :
    HEq
      ((CochainComplex.mappingCone.snd f).v (p + q) (p + q) (add_zero _)
        (actOn A _ action p q m a))
      (act A N p q ((CochainComplex.mappingCone.snd f).v p p (add_zero _) m) a)
  source_action (p q : ℤ) (m : (CochainComplex.mappingCone f).X p) (a : A.X.X q) :
    HEq
      ((CochainComplex.mappingCone.fst f).val.v (p + q) (p + q + 1) rfl
        (actOn A _ action p q m a))
      (act A M (p + 1) q ((CochainComplex.mappingCone.fst f).val.v p (p + 1) rfl m) a)

/-- The cone module from its explicit action data.
Source: Stacks, definition-cone (blueprint: def-sfb-dg-module-cone-calculus). -/
def ConeAction.module {A : Algebra.{u}} {M N : RightModule A}
    {f : (underlying A).obj M ⟶ (underlying A).obj N} (a : ConeAction A M N f) :
    RightModule A := moduleOn A _ a.action

/-- The shifted module from its explicit action data.
Source: Stacks, definition-shift (blueprint: def-sfb-dg-module-cone-calculus). -/
def ShiftAction.module {A : Algebra.{u}} {M : RightModule A} {n : ℤ}
    (a : ShiftAction A M n) : RightModule A := moduleOn A _ a.action

/-- A lift of a fixed chain map to module maps. This records action preservation only;
no underlying map is chosen.
Source: Stacks, definition-dgm (blueprint: def-sfb-dg-module-cone-calculus). -/
abbrev LinearLift (A : Algebra.{u}) (M N : RightModule A)
    (f : (underlying A).obj M ⟶ (underlying A).obj N) :=
  IsModHom (mop A.X) (@id (M.X ⟶ N.X) f.mop)

/-- The action-preserving chain map with the specified underlying chain map.
Source: Stacks, definition-dgm (blueprint: def-sfb-dg-module-cone-calculus). -/
def linearLiftMap {A : Algebra.{u}} {M N : RightModule A}
    {f : (underlying A).obj M ⟶ (underlying A).obj N} (h : LinearLift A M N f) : M ⟶ N :=
  { hom := @id (M.X ⟶ N.X) f.mop, isModHom := h }

end CategoryTheory.DgAlgebra
