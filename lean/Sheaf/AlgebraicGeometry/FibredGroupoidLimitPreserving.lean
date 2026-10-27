module

public import Sheaf.AlgebraicGeometry.StablePointedModuliGroupoids
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.CategoryTheory.Filtered.Basic

/-! # Limit preservation for a fibred groupoid over an arbitrary scheme

Source: Stacks Project, Artin's Axioms, Tag 07XL, definition-limit-preserving, used in Tag 07XX
(blueprint: def-sfb-fibred-groupoid-limit-preserving).

The three descent conditions express essential surjectivity, fullness and faithfulness
of the natural directed affine 2-colimit comparison. No descent for covers is imposed.
-/

@[expose] public section

set_option autoImplicit false

universe u v w

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

namespace CategoryTheory.FibredGroupoidLimit

/-- An object in a specified fibre, retaining its automorphisms.
Source: Stacks, Categories, fibred groupoids, Tag 003T
(blueprint: def-sfb-fibred-groupoid-limit-preserving). -/
abbrev Object {S : Scheme.{u}} (F : BasedCategory.{v, w} (Over S)) (T : Over S) :=
  Functor.Fiber F.p T

/-- An arrow in the total category over exactly the specified map of bases.
Source: Stacks, Categories, Tag 003T
(blueprint: def-sfb-fibred-groupoid-limit-preserving). -/
abbrev Lift {S : Scheme.{u}} {F : BasedCategory.{v, w} (Over S)} {T U : Over S}
    (a : T ⟶ U) (x : Object F T) (y : Object F U) :=
  {b : x.val ⟶ y.val // F.p.IsHomLift a b}

/-- Every object at the inverse limit descends to a stage.
Source: Stacks, Artin, limit preserving, axiom [1]
(blueprint: def-sfb-fibred-groupoid-limit-preserving). -/
def ObjectsDescend {S : Scheme.{u}} (F : BasedCategory.{v, w} (Over S)) : Prop :=
  ∀ (I : Type u) [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (D : Iᵒᵖ ⥤ Over S) (c : Cone D),
    (∀ i : I, IsAffine (D.obj (op i)).left) → IsAffine c.pt.left →
    Nonempty (IsLimit c) → ∀ x : Object F c.pt,
      ∃ (i : I) (xi : Object F (D.obj (op i))), Nonempty (Lift (c.π.app (op i)) x xi)

/-- Arrows between stage objects descend after passage to a common later stage.
The two factorizations retain the specified identifications at the limit.
Source: Stacks, Artin, axiom [1]
(blueprint: def-sfb-fibred-groupoid-limit-preserving). -/
def ArrowsDescend {S : Scheme.{u}} (F : BasedCategory.{v, w} (Over S)) : Prop :=
  ∀ (I : Type u) [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (D : Iᵒᵖ ⥤ Over S) (c : Cone D),
    (∀ i : I, IsAffine (D.obj (op i)).left) → IsAffine c.pt.left →
    Nonempty (IsLimit c) → ∀ (i : I) (xi yi : Object F (D.obj (op i)))
      (x y : Object F c.pt) (px : Lift (c.π.app (op i)) x xi)
      (py : Lift (c.π.app (op i)) y yi) (a : x ⟶ y),
      ∃ (j : I) (hij : i ≤ j) (xj yj : Object F (D.obj (op j)))
        (qx : Lift (D.map (homOfLE hij).op) xj xi)
        (qy : Lift (D.map (homOfLE hij).op) yj yi)
        (rx : Lift (c.π.app (op j)) x xj) (ry : Lift (c.π.app (op j)) y yj)
        (b : xj ⟶ yj),
        rx.val ≫ qx.val = px.val ∧ ry.val ≫ qy.val = py.val ∧
          a.val ≫ ry.val = rx.val ≫ b.val

/-- Equality of stage arrows detected at the limit holds at a later stage.
Source: Stacks, Artin, axiom [1]
(blueprint: def-sfb-fibred-groupoid-limit-preserving). -/
def ArrowEqualitiesDescend {S : Scheme.{u}} (F : BasedCategory.{v, w} (Over S)) : Prop :=
  ∀ (I : Type u) [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (D : Iᵒᵖ ⥤ Over S) (c : Cone D),
    (∀ i : I, IsAffine (D.obj (op i)).left) → IsAffine c.pt.left →
    Nonempty (IsLimit c) → ∀ (i : I) (xi yi : Object F (D.obj (op i)))
      (a b : xi ⟶ yi) (x : Object F c.pt) (px : Lift (c.π.app (op i)) x xi),
      px.val ≫ a.val = px.val ≫ b.val →
      ∃ (j : I) (hij : i ≤ j) (xj : Object F (D.obj (op j)))
        (qx : Lift (D.map (homOfLE hij).op) xj xi), qx.val ≫ a.val = qx.val ≫ b.val

/-- Equivalence on directed affine 2-colimits, including arrows and their equalities.
Source: Stacks, Artin, axiom [1], Tag 07XL
(blueprint: def-sfb-fibred-groupoid-limit-preserving). -/
def IsLimitPreserving {S : Scheme.{u}} (F : BasedCategory.{v, w} (Over S)) : Prop :=
  ObjectsDescend F ∧ ArrowsDescend F ∧ ArrowEqualitiesDescend F

end CategoryTheory.FibredGroupoidLimit
