module

public import Sheaf.CategoryTheory.GroupoidStackificationLocalDescription

/-! # The local stackification interface

Source: Stacks Project, Tags 02ZP and 0436
(blueprint: def-sfb-groupoid-stackification-map).
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe w

open CategoryTheory Opposite
open scoped Pseudofunctor.StrongTrans

namespace CategoryTheory.Pseudofunctor

/-- The local characterization of a stackification map, including extension into stacks.
This packages exactly the properties of `exists_groupoid_stackification_local_description`.
Source: Stacks Project, Tags 02ZP and 0436
(blueprint: def-sfb-groupoid-stackification-map). -/
def IsGroupoidStackification {C : Type w} [SmallCategory C] (J : GrothendieckTopology C)
    {P A : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{w, w}} (i : StrongTrans P A) : Prop :=
  (∀ T : C, IsGroupoid (P.obj (.mk (op T)))) ∧
  (∀ T : C, IsGroupoid (A.obj (.mk (op T)))) ∧ A.IsStack J ∧
  (∀ (T : C) (u v : P.obj (.mk (op T))),
    ∃ e : sheafify (J.over T) (P.presheafHom u v) ≅
        A.presheafHom ((i.app (.mk (op T))).toFunctor.obj u)
          ((i.app (.mk (op T))).toFunctor.obj v),
      ∀ (V : Over T) (φ : (P.presheafHom u v).obj (op V)),
        e.hom.app (op V) ((toSheafify (J.over T) (P.presheafHom u v)).app (op V) φ) =
          (i.naturality V.hom.op.toLoc).inv.toNatTrans.app u ≫
            (i.app (.mk (op V.left))).toFunctor.map φ ≫
              (i.naturality V.hom.op.toLoc).hom.toNatTrans.app v) ∧
  (∀ (T : C) (a : A.obj (.mk (op T))),
    ∃ R : Sieve T, R ∈ J T ∧
      ∀ (V : C) (f : V ⟶ T), R f →
        ∃ u : P.obj (.mk (op V)),
          Nonempty ((i.app (.mk (op V))).toFunctor.obj u ≅
            (A.map f.op.toLoc).toFunctor.obj a)) ∧
  (∀ (Y : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{w, w}),
    (∀ T : C, IsGroupoid (Y.obj (.mk (op T)))) → Y.IsStack J →
    ∀ F : StrongTrans P Y, ∃ H : StrongTrans A Y,
      Nonempty (@CategoryTheory.Iso (StrongTrans P Y)
        (StrongTrans.homCategory (F := P) (G := Y)) (StrongTrans.vcomp i H) F))

end CategoryTheory.Pseudofunctor
