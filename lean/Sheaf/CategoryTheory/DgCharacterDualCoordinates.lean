module

public import Sheaf.CategoryTheory.DgAlgebraDerivedCategory
public import Mathlib.Algebra.Module.CharacterModule
public import Mathlib.Algebra.Group.Subgroup.Ker
public import Mathlib.GroupTheory.QuotientGroup.Defs

/-!
# Coordinate groups for DG character duals

Source: literature/stacks-project/dga.tex, character-dual conventions preceding
Tag 09K4, lemma-hom-into-shift-dual-free
(blueprint: def-sfb-dg-character-dual-coordinates).

These are concrete presentations of maps to the specified shifted character dual,
not maps to an unspecified DG module. Equalizer subgroups impose exactly right
linearity and the chain equation. The null-homotopic maps form a subgroup already;
its subgroup closure gives that subgroup without choosing homotopies.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

namespace CategoryTheory.DgAlgebra

/-- The algebra unit in degree zero. Source: Stacks, definition-dga
(blueprint: def-sfb-dg-character-dual-coordinates). -/
def characterDualUnit (A : Algebra.{u}) : A.X.X 0 :=
  (MonObj.one (X := A.X)).f 0
    ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
      (ModuleCat.of (ULift.{u} ℤ) (ULift.{u} ℤ))).inv (ULift.up 1))

/-- The signed differential on the underlying character dual, from r to s=r+1.
Its two-index form avoids transporting the source of the incoming differential.
Source: Stacks, conventions before 09K4
(blueprint: def-sfb-dg-character-dual-coordinates). -/
def characterDualDifferential (C : Complex.{u}) (r s : ℤ) :
    CharacterModule (C.X (-r)) →+ CharacterModule (C.X (-s)) :=
  (r + 1).negOnePow • (CharacterModule.dual (C.d (-s) (-r)).hom).toAddMonoidHom

/-- Cycles in degree k of the character dual. Source: Stacks, Tag 09K4
(blueprint: def-sfb-dg-character-dual-coordinates). -/
def characterDualCycles (C : Complex.{u}) (k : ℤ) :
    AddSubgroup (CharacterModule (C.X (-k))) :=
  (characterDualDifferential C k (k + 1)).ker

/-- Boundaries viewed inside the cycle group. The square-zero identity ensures
that the incoming image lies in the cycles. Source: Stacks, Tag 09K4
(blueprint: def-sfb-dg-character-dual-coordinates). -/
def characterDualBoundaries (C : Complex.{u}) (k : ℤ) :
    AddSubgroup (characterDualCycles C k) :=
  (AddMonoidHom.range (characterDualDifferential C (k - 1) k)).comap
    (characterDualCycles C k).subtype

/-- The actual kernel/image quotient H^k(M-dual). Source: Stacks, Tag 09K4
(blueprint: def-sfb-dg-character-dual-coordinates). -/
abbrev CharacterDualCohomology (C : Complex.{u}) (k : ℤ) :=
  characterDualCycles C k ⧸ characterDualBoundaries C k

/-- Degree-t additive maps to A-dual[k], before imposing right linearity.
Source: Stacks, conventions before 09K4
(blueprint: def-sfb-dg-character-dual-coordinates). -/
abbrev CharacterDualCochain (A : Algebra.{u}) (M : RightModule A) (k t : ℤ) :=
  ∀ p : ℤ, ((underlying A).obj M).X p →+ CharacterModule (A.X.X (-(p + k + t)))

/-- A coordinate evaluation, as an additive homomorphism of cochains.
Source: Stacks, Tag 09K4 (blueprint: def-sfb-dg-character-dual-coordinates). -/
def characterDualCoordinate (A : Algebra.{u}) (M : RightModule A) (k t p : ℤ)
    (m : ((underlying A).obj M).X p) (b : A.X.X (-(p + k + t))) :
    CharacterDualCochain A M k t →+ AddCircle (1 : ℚ) :=
  (AddMonoidHom.eval b).comp
    ((AddMonoidHom.eval m).comp (Pi.evalAddMonoidHom _ p))

/-- The exact right-linearity equations, with the unchanged shifted action.
Source: Stacks, character-dual action preceding 09K4
(blueprint: def-sfb-dg-character-dual-coordinates). -/
def characterDualLinear (A : Algebra.{u}) (M : RightModule A) (k t : ℤ) :
    AddSubgroup (CharacterDualCochain A M k t) :=
  ⨅ (p : ℤ), ⨅ (q : ℤ), ⨅ (m : ((underlying A).obj M).X p),
    ⨅ (a : A.X.X q), ⨅ (b : A.X.X (-(p + q + k + t))),
    AddMonoidHom.eqLocus
      (characterDualCoordinate A M k t (p + q) (act A M p q m a) b)
      (characterDualCoordinate A M k t p m
        ((A.X.XIsoOfEq (show q + -(p + q + k + t) = -(p + k + t) by omega)).hom
          (act A (regular A) q (-(p + q + k + t)) a b)))

/-- Degree-zero right-linear chain maps to A-dual[k]. The shifted target's
 differential has sign (-1)^(p+1). Source: Stacks, Tag 09K4
(blueprint: def-sfb-dg-character-dual-coordinates). -/
def characterDualMaps (A : Algebra.{u}) (M : RightModule A) (k : ℤ) :
    AddSubgroup (CharacterDualCochain A M k 0) :=
  characterDualLinear A M k 0 ⊓
    ⨅ (p : ℤ), ⨅ (m : ((underlying A).obj M).X p),
      ⨅ (b : A.X.X (-(p + 1 + k + 0))),
      AddMonoidHom.eqLocus
        (characterDualCoordinate A M k 0 (p + 1)
          (((underlying A).obj M).d p (p + 1) m) b)
        ((p + 1).negOnePow • characterDualCoordinate A M k 0 p m
          (A.X.d (-(p + 1 + k + 0)) (-(p + k + 0)) b))

/-- Null-homotopic chain maps, using degree-minus-one right-linear additive h
and exactly f=d h+h d. This set is already closed under addition and negation,
so taking its subgroup closure changes no elements. Source: Stacks, Tag 09K4
and definition-homotopy (blueprint: def-sfb-dg-character-dual-coordinates). -/
def characterDualNullMaps (A : Algebra.{u}) (M : RightModule A) (k : ℤ) :
    AddSubgroup (characterDualMaps A M k) :=
  AddSubgroup.closure {f | ∃ h : characterDualLinear A M k (-1),
    ∀ (p : ℤ) (m : ((underlying A).obj M).X p) (b : A.X.X (-(p + k + 0))),
      f.val p m b =
        p.negOnePow • h.val p m (A.X.d (-(p + k + 0)) (-(p + k + -1)) b) +
          h.val (p + 1) (((underlying A).obj M).d p (p + 1) m)
            ((A.X.XIsoOfEq (show -(p + k + 0) = -(p + 1 + k + -1) by omega)).hom b)}

/-- Hom_K(M,A-dual[k]), as the additive quotient by right-linear homotopies.
Source: Stacks, Tag 09K4 (blueprint: def-sfb-dg-character-dual-coordinates). -/
abbrev CharacterDualHomotopyMaps (A : Algebra.{u}) (M : RightModule A) (k : ℤ) :=
  characterDualMaps A M k ⧸ characterDualNullMaps A M k

end CategoryTheory.DgAlgebra
