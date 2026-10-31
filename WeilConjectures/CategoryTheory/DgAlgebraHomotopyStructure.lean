/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.DgAlgebraDerivedCategory
public import Mathlib.CategoryTheory.Quotient
public import Mathlib.CategoryTheory.Triangulated.Subcategory

/-!
# The homotopy quotient of right dg modules

Source: Stacks Project, dga.tex, definitions of homotopy, translation, cone and
 distinguished triangles, and Tags 09KH, 09KJ, 09KW
(blueprint: def-sfb-dg-homotopy-structure).

The quotient is constructed from action-preserving homotopies. `HomotopyStructure`
specifies the standard additive shift and cone triangulation on that fixed quotient.
Its existence, the octahedral axiom and the acyclic cone criterion are assertions,
not assumptions on the dg algebra.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace CategoryTheory.DgAlgebra

/-- An ordinary chain homotopy whose degree-minus-one maps preserve the right action.
The equation in `Homotopy` says precisely f-g=dh+hd; no sign is inserted into
right A-linearity. Source: Stacks, dga.tex, definition-homotopy
(blueprint: def-sfb-dg-homotopy-structure). -/
def homotopyRel (A : Algebra.{u}) : HomRel (RightModule A) :=
  fun M N f g ↦ ∃ h : Homotopy ((underlying A).map f) ((underlying A).map g),
    ∀ (p q : ℤ) (m : ((underlying A).obj M).X p) (a : A.X.X q),
      HEq (h.hom (p + q) (p + q - 1) (act A M p q m a))
        (act A N (p - 1) q (h.hom p (p - 1) m) a)

/-- The category of right dg modules modulo A-linear chain homotopy. The general
quotient construction takes the compositional equivalence closure, which here is
already the homotopy congruence. Source: Stacks, dga.tex, section-homotopy
(blueprint: def-sfb-dg-homotopy-structure). -/
abbrev HomotopyCategory (A : Algebra.{u}) := CategoryTheory.Quotient (homotopyRel A)

/-- The canonical quotient functor to K(A,d).
Source: Stacks, dga.tex, section-homotopy
(blueprint: def-sfb-dg-homotopy-structure). -/
abbrev homotopyQuotient (A : Algebra.{u}) : RightModule A ⥤ HomotopyCategory A :=
  CategoryTheory.Quotient.functor (homotopyRel A)

/-- Acyclicity means vanishing in every degree of the actual underlying complex.
Source: Stacks, dga.tex, lemma-acyclic, Tag 09KW
(blueprint: def-sfb-dg-homotopy-structure). -/
def homotopyAcyclic (A : Algebra.{u}) : ObjectProperty (HomotopyCategory A) :=
  fun M ↦ ((underlying A).obj M.as).Acyclic

/-- Standard pretriangulation data on the actual dg homotopy quotient. Additions
are the underlying additions, shifts retain the unchanged right action, and the
cone comparison fixes the inclusion and negative projection. The cohomology
functors factor the underlying cohomology functors exactly. Distinguished triangles
are precisely the isomorphic copies of these specified cone triangles.
Source: Stacks, dga.tex, definition-shift, definition-cone,
section-distinguished and Tag 09KH (blueprint: def-sfb-dg-homotopy-structure). -/
class HomotopyStructure (A : Algebra.{u}) where
  [modulePreadditive : Preadditive (RightModule A)]
  [underlyingAdditive : (underlying A).Additive]
  [preadditive : Preadditive (HomotopyCategory A)]
  [quotientAdditive : (homotopyQuotient A).Additive]
  [zero : HasZeroObject (HomotopyCategory A)]
  [shift : HasShift (HomotopyCategory A) ℤ]
  [shiftAdditive : ∀ n : ℤ, (shiftFunctor (HomotopyCategory A) n).Additive]
  [pretriangulated : Pretriangulated (HomotopyCategory A)]
  cohomology (n : ℤ) : HomotopyCategory A ⥤ ModuleCat.{u} (ULift.{u} ℤ)
  cohomology_factors (n : ℤ) : homotopyQuotient A ⋙ cohomology n =
    underlying A ⋙ HomologicalComplex.homologyFunctor _ (ComplexShape.up ℤ) n
  shifts_exist (n : ℤ) (M : RightModule A) :
    ∃ S : RightModule A, Nonempty (ShiftComparison A n M S)
  cones_exist {M N : RightModule A} (f : M ⟶ N) :
    ∃ (K S : RightModule A) (s : ShiftComparison A 1 M S) (g : N ⟶ K) (h : K ⟶ S),
      Nonempty (ConeComparison A f K S s g h)
  shiftIso (n : ℤ) (M S : RightModule A) (e : ShiftComparison A n M S) :
    (homotopyQuotient A).obj S ≅ ((homotopyQuotient A).obj M)⟦n⟧
  shift_natural (n : ℤ) (M N S V : RightModule A)
      (eM : ShiftComparison A n M S) (eN : ShiftComparison A n N V)
      (f : M ⟶ N) (g : S ⟶ V)
      (comm : (underlying A).map g ≫ eN.iso.hom =
        eM.iso.hom ≫ ((underlying A).map f)⟦n⟧') :
    (homotopyQuotient A).map g ≫ (shiftIso n N V eN).hom =
      (shiftIso n M S eM).hom ≫ ((homotopyQuotient A).map f)⟦n⟧'
  distinguished_iff (t : Triangle (HomotopyCategory A)) :
    t ∈ distTriang (HomotopyCategory A) ↔
      ∃ (M N K S : RightModule A) (f : M ⟶ N) (s : ShiftComparison A 1 M S)
        (g : N ⟶ K) (h : K ⟶ S),
        Nonempty (ConeComparison A f K S s g h) ∧
        Nonempty (t ≅ Triangle.mk ((homotopyQuotient A).map f)
          ((homotopyQuotient A).map g)
          ((homotopyQuotient A).map h ≫ (shiftIso 1 M S s).hom))

attribute [instance_reducible] HomotopyStructure.modulePreadditive
  HomotopyStructure.preadditive HomotopyStructure.shift HomotopyStructure.pretriangulated

attribute [instance] HomotopyStructure.modulePreadditive HomotopyStructure.underlyingAdditive
  HomotopyStructure.preadditive HomotopyStructure.quotientAdditive HomotopyStructure.zero
  HomotopyStructure.shift HomotopyStructure.shiftAdditive HomotopyStructure.pretriangulated

end CategoryTheory.DgAlgebra
