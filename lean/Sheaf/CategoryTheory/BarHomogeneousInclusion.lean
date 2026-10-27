/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group T3
-/
module

public import Sheaf.CategoryTheory.InternalHomogeneousCochainCoordinateData

/-! # Homogeneous inclusion of the bar presentation

Source: the internal sheaf adaptation of the displayed bar differential of Stacks 0DVG.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace CategoryTheory.CondensedBar

/-- The successive-quotient inclusion presents the given bar complex as homogeneous
cochains. All maps are uniquely specified by their generalized evaluations.
Source: Stacks 0DVG, internal adaptation, coordinate construction and deletion calculation
(blueprint: lem-sfb-bar-homogeneous-inclusion). -/
structure BarHomogeneousInclusion {A : Ring.{u}} (F : InternalFunctions A)
    (J : ProfiniteGrp.{u}) (B : BarDiagram (G := J) F) where
  inclusion : ∀ (M : Equivariant A J) (n : ℕ),
    ((cochains B).obj M).X n ⟶ (F.functor (power J (n + 1))).obj M.module
  injective : ∀ (M : Equivariant A J) (n : ℕ) (S : Profinite.{u}),
    Function.Injective ((inclusion M n).hom.hom.app (op S))
  image : ∀ (M : Equivariant A J) (n : ℕ) (S : Profinite.{u})
    (x : sections A ((F.functor (power J (n + 1))).obj M.module) S),
    (∃ y : sections A (((cochains B).obj M).X n) S,
      (inclusion M n).hom.hom.app (op S) y = x) ↔ IsHomogeneousSection F J M n S x
  maps : ∀ {M N : Equivariant A J} (h : M ⟶ N) (n : ℕ),
    ((cochains B).map h).f n ≫ inclusion N n =
      inclusion M n ≫ (F.functor (power J (n + 1))).map h.val
  differential : ∀ (M : Equivariant A J) (n : ℕ) (S : Profinite.{u})
    (x : sections A (((cochains B).obj M).X n) S) (T : Profinite.{u}) (f : T ⟶ S)
    (g : Fin (n + 2) → C(T, J)),
    (F.evaluate (power J (n + 2)) S M.module
      ((((cochains B).obj M).d n (n + 1) ≫ inclusion M (n + 1)).hom.hom.app (op S) x)).val
        T f (tupleMap g) =
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val •
        (F.evaluate (power J (n + 1)) S M.module
          ((inclusion M n).hom.hom.app (op S) x)).val T f
            (tupleMap (fun j ↦ g (i.succAbove j)))

  evaluation : ∀ (M : Equivariant A J) (n : ℕ) (S : Profinite.{u})
    (c : sections A (((cochains B).obj M).X n) S)
    (T : Profinite.{u}) (f : T ⟶ S) (x : Fin (n + 1) → C(T, J)),
    (F.evaluate (power J (n + 1)) S M.module
      ((inclusion M n).hom.hom.app (op S) c)).val T f (tupleMap x) =
      M.act T (x 0)
        (inhomogeneousCoordinateValue B M n S c T f (coordinateQuotients x))

/-- The successive-quotient formula gives the homogeneous inclusion, with exactly its
specified image and alternating-deletion differential, on the given bar complex.
Source: Stacks 0DVG, internal adaptation, steps 1--4 of the coordinate calculation
(blueprint: lem-sfb-bar-homogeneous-inclusion).

Proof: on each profinite slice send c to the family x ↦ x₀ c(x₀⁻¹x₁,...,xₙ₋₁⁻¹xₙ).
The action and evaluation restriction laws make this a natural family. The evaluation
equivalence constructs the section. Additivity and scalar compatibility give linearity;
the section-module equivalence lifts the resulting natural linear maps to internal maps.
Coefficient naturality follows from equivariance and the bar-term naturality. Simultaneous
left multiplication cancels in the successive quotients and acts through x₀, proving
homogeneity. Evaluation on prefix products is a left inverse, proving injectivity. For a
homogeneous family, evaluate it on prefixes to obtain the inverse section; multiplying
back by x₀ recovers the original family, proving the image characterization. Finally
apply the bar face formulas: the initial face acts by x₀(x₀⁻¹x₁)=x₁, each interior face
multiplies adjacent quotients to xᵢ₋₁⁻¹xᵢ₊₁, and the last face drops the last quotient.
These are exactly deletion of the respective entries, with their original signs. Summing
the faces proves the displayed differential formula, also in degree zero and characteristic
two. This constructs every data field explicitly; no representative of a mere existence
statement is needed. -/
theorem exists_barHomogeneousInclusion {A : Ring.{u}} (F : InternalFunctions A)
    (J : ProfiniteGrp.{u}) (B : BarDiagram (G := J) F) :
    Nonempty (BarHomogeneousInclusion F J B) := by sorry

end CategoryTheory.CondensedBar
