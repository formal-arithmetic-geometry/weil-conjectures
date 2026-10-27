module

public import Sheaf.CategoryTheory.DgAlgebraDerivedCategory

/-!
# Derived morphisms from the shifted regular DG module

Source: Stacks Project, dga.tex, Tags 09K1 and 09KY(1)
(blueprint: lem-sfb-dg-free-shift-derived-hom).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.MonoidalCategory

namespace CategoryTheory.DgAlgebra

/-- The unit in degree `-k` of a shifted regular module, using the specified comparison.
Source: Stacks, dga.tex, definition-shift and Tag 09K1
(blueprint: lem-sfb-dg-free-shift-derived-hom). -/
def shiftedRegularUnit (A : Algebra.{u}) (k : ℤ) (S : RightModule A)
    (s : ShiftComparison A k (regular A) S) : ((underlying A).obj S).X (-k) :=
  (s.iso.inv.f (-k))
    ((((underlying A).obj (regular A)).shiftFunctorObjXIso k (-k) 0
      (neg_add_cancel k).symm).inv
      ((MonObj.one (X := A.X)).f 0
        ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
          (ModuleCat.of (ULift.{u} ℤ) (ULift.{u} ℤ))).inv (1 : ULift.{u} ℤ))))

/-- Evaluation of a DG map on the shifted unit, as an element of the actual module.
Source: Stacks, dga.tex, Tag 09K1
(blueprint: lem-sfb-dg-free-shift-derived-hom). -/
def shiftedRegularEvaluation (A : Algebra.{u}) (k : ℤ) (S : RightModule A)
    (s : ShiftComparison A k (regular A) S) (M : RightModule A) (f : S ⟶ M) :
    ((underlying A).obj M).X (-k) :=
  (((underlying A).map f).f (-k)) (shiftedRegularUnit A k S s)

/-- Evaluation at the unit computes derived Hom from `A[k]`, with representatives,
its boundary criterion, and naturality on DG module maps.
Source: Stacks Project, dga.tex, Tag 09K1 and Tag 09KY(1)
(blueprint: lem-sfb-dg-free-shift-derived-hom).

Proof:
1. Evaluate homogeneous right-linear maps from A[k] at 1. The inverse sends x to
   a mapping to xa. Since d(1)=0, the mapping-complex differential evaluates to d(x);
   the two terms containing d(a) cancel with signs (-1)^(r-k)=(-1)^(r+k).
2. Closed degree-zero maps are DG maps and correspond to cycles in M^(-k).
   A degree-minus-one homotopy evaluates to y with f(1)-g(1)=d(y), and conversely
   a mapping to ya gives that homotopy. Thus Hom in the homotopy category is H^(-k).
3. For acyclic N the same mapping complex is acyclic in every degree. Hence A[k]
   is homotopically projective; lem-sfb-dg-homotopically-projective-hom-derived
   makes its homotopy-to-derived Hom map bijective. This proves existence of DG
   representatives and exactly the boundary criterion. Sums of representatives
   evaluate to sums, giving the additive equivalence normalized below through
   the canonical inclusion of cohomology into the quotient by boundaries.
4. For h:M to N, (h f)(1)=h(f(1)); passing to cohomology proves naturality.
   These arguments include arbitrary integers and unbounded noncommutative algebras,
   with no flatness or countability restriction. -/
theorem free_shift_derived_hom (A : Algebra.{u}) [DerivedStructure A]
    (k : ℤ) (S : RightModule A) (s : ShiftComparison A k (regular A) S) :
    (∀ (M : RightModule A) (φ : (Q A).obj S ⟶ (Q A).obj M),
      ∃ f : S ⟶ M, (Q A).map f = φ) ∧
    (∀ (M : RightModule A) (f g : S ⟶ M),
      (Q A).map f = (Q A).map g ↔
        ∃ y : ((underlying A).obj M).X (-k - 1),
          (((underlying A).obj M).d (-k - 1) (-k)) y =
            shiftedRegularEvaluation A k S s M f - shiftedRegularEvaluation A k S s M g) ∧
    ∃ e : ∀ M : RightModule A,
        ((Q A).obj S ⟶ (Q A).obj M) ≃+ ((underlying A).obj M).homology (-k),
      (∀ (M : RightModule A) (f : S ⟶ M),
        (((underlying A).obj M).homologyι (-k)) (e M ((Q A).map f)) =
          (((underlying A).obj M).pOpcycles (-k))
            (shiftedRegularEvaluation A k S s M f)) ∧
      (∀ (M N : RightModule A) (h : M ⟶ N)
          (φ : (Q A).obj S ⟶ (Q A).obj M),
        e N (φ ≫ (Q A).map h) =
          (HomologicalComplex.homologyMap ((underlying A).map h) (-k)) (e M φ)) := by
  sorry

end CategoryTheory.DgAlgebra
