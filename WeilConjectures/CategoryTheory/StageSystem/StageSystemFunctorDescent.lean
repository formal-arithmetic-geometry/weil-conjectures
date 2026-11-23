/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.NatIso
public import WeilConjectures.CategoryTheory.CommonStage.CoherentPairFunctorDescent
public import WeilConjectures.CategoryTheory.StageSystem.Basic
import WeilConjectures.CategoryTheory.StageSystem.Functor

/-! # Coherent functor descent on the existing StageSystem quotient

## Main definitions

* `StageSystem.pairFunctorCoherent`: the specified tower equation.
* `StageSystem.coefficientPairFunctor`: descent on the actual upstream quotient.

The imported original interface retains additive structures, compatible natural
transformations and outer Karoubi extension. This interface transports its functor
construction to the independently existing `StageSystem.PairCategory` carrier.
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe w u v u' v'

namespace CategoryTheory.StageSystem

variable {I : Type w} [Preorder I] [IsDirectedOrder I]
  {C : I → Type u} [∀ i, Category.{v} (C i)]
  {D : I → Type u'} [∀ i, Category.{v'} (D i)]
  (S : StageSystem C) (T : StageSystem D)
  (φ : ∀ i, C i ⥤ D i)
  (b : ∀ {i j} (h : i ≤ j), φ i ⋙ T.T h ≅ S.T h ⋙ φ j)

/-- The coherent tower equation, with the source and target associators retained. -/
def pairFunctorCoherent : Prop :=
  ∀ {i j k} (h : i ≤ j) (h' : j ≤ k) (X : C i),
    (T.T h').map ((b h).hom.app X) ≫ (b h').hom.app ((S.T h).obj X) ≫
        (φ k).map ((S.assoc h h').hom.app X) =
      (T.assoc h h').hom.app ((φ i).obj X) ≫ (b (h.trans h')).hom.app X

/-- The descended object keeps the coefficient stage. -/
def coefficientPairFunctorObject (P : S.PairCategory) : T.PairCategory :=
  match P with
  | ⟨i, X⟩ => ⟨i, (φ i).obj X⟩

omit [IsDirectedOrder I] in
/-- Matching the pair first preserves the original stagewise object formula. -/
theorem coefficientPairFunctorObject_eq (P : S.PairCategory) :
    coefficientPairFunctorObject S T φ P = ⟨P.stage, (φ P.stage).obj P.obj⟩ := by
  cases P
  rfl

/-- The functor on the upstream quotient is uniquely prescribed by all representatives. -/
theorem coefficientPairFunctor_exists (hb : pairFunctorCoherent S T φ b) :
    ∃! F : S.PairCategory ⥤ T.PairCategory,
      (∀ P, F.obj P = coefficientPairFunctorObject S T φ P) ∧
      (∀ {P Q : S.PairCategory} (M : I) (hP : P.stage ≤ M) (hQ : Q.stage ≤ M)
        (f : P.toStage hP ⟶ Q.toStage hQ),
        HEq (F.map (PairCategory.mkHom M hP hQ f))
          (PairCategory.mkHom
            (X := coefficientPairFunctorObject S T φ P)
            (Y := coefficientPairFunctorObject S T φ Q) M hP hQ
            ((b hP).hom.app P.obj ≫ (φ M).map f ≫ (b hQ).inv.app Q.obj))) := by
  let G : S.Morphism T := ⟨φ, b, hb⟩
  refine ⟨G.functor, ⟨fun P ↦ by cases P; rfl, fun _ _ _ _ ↦ HEq.rfl⟩, ?_⟩
  intro F hF
  apply Functor.hext hF.1
  intro P Q f
  induction f using PairCategory.hom_induction with
  | h M hP hQ f => exact hF.2 M hP hQ f

/-- Coherent-pair descent, with uniquely determined object and arrow formulas. -/
@[irreducible] def coefficientPairFunctor (hb : pairFunctorCoherent S T φ b) :=
  ((coefficientPairFunctor_exists S T φ b hb).exists.choose).copyObj
    (coefficientPairFunctorObject S T φ)
    (fun P ↦ eqToIso ((coefficientPairFunctor_exists S T φ b hb).exists.choose_spec.1 P))

end CategoryTheory.StageSystem
