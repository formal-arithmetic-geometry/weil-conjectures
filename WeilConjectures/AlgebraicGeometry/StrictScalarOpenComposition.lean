/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CompactSupportStrictScalarMate

import WeilConjectures.AlgebraicGeometry.StrictScalarOpenUnit
import WeilConjectures.AlgebraicGeometry.StrictScalarPullComposition
import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Mates

/-! # Scalar compatibility with the normalized strict open compositor

Source: Stacks Project, Tags 0E8I, 03DI, 0F7D; strict scalar refinement, Steps 3--6 and 9.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
attribute [local irreducible] CategoryTheory.Functor.mapDerivedCategory
  CategoryTheory.Functor.rightDerivedFunctor
universe u
open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.ProEtale.StrictTower
namespace WeilConjectures.PurStrictScalar
attribute [local irreducible] T U scalarAdj properRestriction openTensor strictScalarPull
  AlgebraicGeometry.ProEtale.StrictTower.G AlgebraicGeometry.ProEtale.StrictTower.J
  AlgebraicGeometry.ProEtale.StrictTower.R

variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (F : Type u) [Field F] [Algebra ℚ_[l] F] [FiniteDimensional ℚ_[l] F]
  (i : E →ₐ[ℚ_[l]] F)

private theorem openTensor_isIso {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsOpenImmersion f] : IsIso (openTensor l E F i f) := by
  rw [openTensor_ordinary l E F i f]
  unfold T J
  exact (Functor.mapDerivedCategorySquareIso
    (@asIso _ _ _ _ (ordinaryOpenTensor l E F i f)
      (ordinaryOpenTensor_isIso l E F i f))).isIso_hom

private def openIso {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] :
    J (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) f ⋙ T l E F i Y ≅
      T l E F i X ⋙ J (ULift.{u + 1} (Padic.coefficientExtensionIntegers l F)) f :=
  @asIso _ _ _ _ (openTensor l E F i f) (openTensor_isIso l E F i f)

private theorem openIso_inv_mate {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsOpenImmersion f] :
    mateEquiv
      (jAdj (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) f)
      (jAdj (ULift.{u + 1} (Padic.coefficientExtensionIntegers l F)) f)
      (TwoSquare.mk _ _ _ _ (openIso l E F i f).inv) =
        TwoSquare.mk _ _ _ _ (strictScalarPull l E F i f).hom := by
  apply mateEquiv_eq_of_unit
  intro M
  have hu : (T l E F i X).map ((jAdj _ f).unit.app M) ≫
      (strictScalarPull l E F i f).hom.app ((J _ f).obj M) ≫
      (G _ f).map ((openIso l E F i f).hom.app M) =
        (jAdj _ f).unit.app ((T l E F i X).obj M) := by
    simpa only [strictScalarPull, openIso, asIso_hom] using
      strictScalarOpenUnit l E F i f M
  change (T l E F i X).map ((jAdj _ f).unit.app M) ≫
    (strictScalarPull l E F i f).hom.app ((J _ f).obj M) = _
  rw [← hu]
  simp only [Category.assoc, ← Functor.map_comp, Iso.hom_inv_id_app]
  erw [(G (ULift.{u + 1} (Padic.coefficientExtensionIntegers l F)) f).map_id,
    Category.comp_id]

private theorem jComp_mate (A : Type (u + 1)) [CommRing A]
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsOpenImmersion f] [IsOpenImmersion g] :
    conjugateEquiv (jAdj A (f ≫ g)) ((jAdj A f).comp (jAdj A g))
      (jComp A f g).hom = (gComp A f g).hom := by
  change (conjugateIsoEquiv (jAdj A (f ≫ g)) ((jAdj A f).comp (jAdj A g))
    ((conjugateIsoEquiv (jAdj A (f ≫ g)) ((jAdj A f).comp (jAdj A g))).symm
      (gComp A f g))).hom = _
  exact congrArg Iso.hom
    ((conjugateIsoEquiv (jAdj A (f ≫ g)) ((jAdj A f).comp (jAdj A g))).apply_symm_apply
      (gComp A f g))

private theorem pull_hom_composition {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (N : Derived (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) Z) :
    (T l E F i X).map ((gComp _ f g).hom.app N) ≫
        (strictScalarPull l E F i f).hom.app ((G _ g).obj N) ≫
        (G (ULift.{u + 1} (Padic.coefficientExtensionIntegers l F)) f).map
          ((strictScalarPull l E F i g).hom.app N) =
      (strictScalarPull l E F i (f ≫ g)).hom.app N ≫
        (gComp _ f g).hom.app ((T l E F i Z).obj N) := by
  have h := strictScalarPullComposition l E F i f g N
  apply (cancel_epi ((strictScalarPull l E F i (f ≫ g)).inv.app N)).mp
  simp only [Iso.inv_hom_id_app_assoc]
  rw [← reassoc_of% h]
  simp only [Iso.inv_hom_id_app_assoc, ← Functor.map_comp, Iso.inv_hom_id_app]
  erw [(G (ULift.{u + 1} (Padic.coefficientExtensionIntegers l F)) f).map_id,
    Category.comp_id]

private theorem open_inverse_composition {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsOpenImmersion f] [IsOpenImmersion g] :
    TwoSquare.mk _ _ _ _ (openIso l E F i (f ≫ g)).inv =
      (((TwoSquare.mk _ _ _ _ (openIso l E F i f).inv).vComp
        (TwoSquare.mk _ _ _ _ (openIso l E F i g).inv)).whiskerLeft
          (jComp (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) f g).hom).whiskerRight
              (jComp (ULift.{u + 1} (Padic.coefficientExtensionIntegers l F)) f g).inv := by
  let A := ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)
  let B := ULift.{u + 1} (Padic.coefficientExtensionIntegers l F)
  apply (mateEquiv (jAdj A (f ≫ g)) (jAdj B (f ≫ g))).injective
  rw [openIso_inv_mate, mateEquiv_conjugateEquiv_vcomp _
    ((jAdj B f).comp (jAdj B g)),
    conjugateEquiv_mateEquiv_vcomp _ ((jAdj A f).comp (jAdj A g)),
    mateEquiv_hcomp, openIso_inv_mate, openIso_inv_mate, jComp_mate]
  rw [show conjugateEquiv ((jAdj B f).comp (jAdj B g)) (jAdj B (f ≫ g))
    (jComp B f g).inv = (gComp B f g).inv from
      Adjunction.conjugateEquiv_leftAdjointCompIso_inv _ _ _ _]
  ext N
  dsimp only [TwoSquare.whiskerBottom, TwoSquare.whiskerTop,
    TwoSquare.hComp, TwoSquare.mk, TwoSquare.natTrans]
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.associator_hom_app,
    Functor.associator_inv_app, Category.id_comp, Category.comp_id]
  change _ = ((T l E F i X).map ((gComp A f g).hom.app N) ≫
    ((strictScalarPull l E F i f).hom.app ((G A g).obj N) ≫
      (G B f).map ((strictScalarPull l E F i g).hom.app N))) ≫
        (gComp B f g).inv.app ((T l E F i Z).obj N)
  rw [pull_hom_composition]
  simp only [Category.assoc]
  erw [Iso.hom_inv_id_app, Category.comp_id]

private theorem forward_of_inverse
    {C : Type*} [Category C] {P Q R S V : C}
    (a : P ≅ Q) (b : Q ≅ V) (c : P ≅ R) (d : R ≅ S) (e : S ≅ V)
    (h : b.inv = e.inv ≫ d.inv ≫ c.inv ≫ a.hom) :
    a.hom ≫ b.hom = c.hom ≫ d.hom ≫ e.hom := by
  apply (cancel_mono b.inv).mp
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rw [h]
  simp only [Iso.hom_inv_id_assoc]

/-- Scalar balancing preserves the normalized compositor for two open extensions.
Source: Stacks Tags 0E8I, 03DI, 0F7D; strict scalar refinement, Steps 3--5 and 9.
(blueprint: lem-pur-strict-scalar-open-composition).
Proof: ordinary open balancing makes openTensor invertible. The strict open-unit
formula identifies its inverse as the mate of strictScalarPull.hom. Cancel inverses
in strictScalarPullComposition to obtain the corresponding hom pasting equation.
The specified jComp has conjugate gComp, by its composition-adjunction definition.
Horizontal mate pasting and compatibility with these conjugates therefore identify
the inverse composite open map with the pasted inverse open maps. Evaluating and
cancelling gives the displayed equation, entirely within strict derived categories. -/
theorem strictScalarOpenComposition {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsOpenImmersion f] [IsOpenImmersion g]
    (M : Derived (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) X) :
    (T l E F i Z).map
        ((jComp (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) f g).hom.app M) ≫
        (openTensor l E F i (f ≫ g)).app M =
      (openTensor l E F i g).app
          ((J (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) f).obj M) ≫
        (J (ULift.{u + 1} (Padic.coefficientExtensionIntegers l F)) g).map
          ((openTensor l E F i f).app M) ≫
        (jComp (ULift.{u + 1} (Padic.coefficientExtensionIntegers l F)) f g).hom.app
          ((T l E F i X).obj M) := by
  let A := ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)
  let B := ULift.{u + 1} (Padic.coefficientExtensionIntegers l F)
  have h := congrArg (fun q ↦ q.app M) (open_inverse_composition l E F i f g)
  simp only [TwoSquare.whiskerLeft, TwoSquare.whiskerRight, TwoSquare.vComp,
    TwoSquare.mk, TwoSquare.natTrans, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.associator_hom_app, Functor.associator_inv_app,
    Category.id_comp, Category.comp_id] at h
  exact forward_of_inverse
    ((T l E F i Z).mapIso ((jComp A f g).app M))
    ((openIso l E F i (f ≫ g)).app M)
    ((openIso l E F i g).app ((J A f).obj M))
    ((J B g).mapIso ((openIso l E F i f).app M))
    ((jComp B f g).app ((T l E F i X).obj M))
    (by simpa only [Functor.mapIso_hom, Functor.mapIso_inv, Iso.app_inv,
      Iso.app_hom, Category.assoc] using h)

end WeilConjectures.PurStrictScalar
