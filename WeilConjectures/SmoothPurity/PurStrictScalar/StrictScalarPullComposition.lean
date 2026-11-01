/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurStrictScalar.CompactSupportStrictScalarMate
public import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Mates
public import WeilConjectures.SmoothPurity.PurStrictScalar.StrictProperCompositionRestriction

/-! # Scalar compatibility with the normalized strict pullback compositor

Source: Stacks Project, Tags 07A6, 0B56, 0D6D; strict scalar refinement, Steps 3--6 and 9.
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

private theorem leftAdjointUniq_ofNatIsoRight_inv
    {A B : Type*} [Category A] [Category B]
    {L L' : A ⥤ B} {U U' : B ⥤ A}
    (a : L ⊣ U) (b : L' ⊣ U') (δ : U ≅ U') :
    (a.ofNatIsoRight δ |>.leftAdjointUniq b).inv =
      (conjugateEquiv a b).symm δ.hom := by
  ext N
  simp [Adjunction.leftAdjointUniq, conjugateEquiv_symm_apply_app,
    Adjunction.ofNatIsoRight_unit]

private theorem mateEquiv_whiskerTop
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {L : A ⥤ B} {R : B ⥤ A} {L' : C ⥤ D} {R' : D ⥤ C}
    (a : L ⊣ R) (b : L' ⊣ R') {G G' : A ⥤ C} {H : B ⥤ D}
    (α : TwoSquare G L L' H) (σ : G' ⟶ G) :
    mateEquiv a b (α.whiskerTop σ) = (mateEquiv a b α).whiskerRight σ := by
  simpa only [TwoSquare.whiskerBottom, TwoSquare.whiskerLeft,
    Functor.whiskerLeft_id', Functor.whiskerRight_id', Category.comp_id] using
    mateEquiv_whiskerTop_whiskerBottom a b α σ (𝟙 H)

private theorem strictScalarPull_double_mate {X Y : Scheme.{u}} (f : X ⟶ Y) :
    mateEquiv (scalarAdj l E F i X) (scalarAdj l E F i Y)
      (mateEquiv
        (adj (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) f)
        (adj (ULift.{u + 1} (Padic.coefficientExtensionIntegers l F)) f)
        (TwoSquare.mk _ _ _ _ (strictScalarPull l E F i f).inv)) =
      TwoSquare.mk _ _ _ _ (properRestriction l E F i f).inv := by
  change (mateEquiv (scalarAdj l E F i X) (scalarAdj l E F i Y)
    (mateEquiv (adj _ f) (adj _ f)
      (TwoSquare.mk _ _ _ _ (strictScalarPull l E F i f).inv))).natTrans = _
  rw [iterated_mateEquiv_conjugateEquiv, strictScalarPull,
    leftAdjointUniq_ofNatIsoRight_inv]
  exact (conjugateEquiv _ _).apply_symm_apply _

/-- The inverse scalar/pullback identifications respect the specified pullback compositor.
Source: Stacks Tags 07A6, 0B56, 0D6D; strict scalar refinement, Steps 3--4.
(blueprint: lem-pur-strict-scalar-pull-composition).
Proof: restriction of coefficients commutes with two successive ordinary direct images:
all three comparison maps act as the identity on the same sections over the iterated
base change. The module direct-image compositor identifies these sections with those
over the composite. Derive this square using the whole-complex resolution units that
uniquely specify properRestriction. Take its conjugate under the composite geometric
and scalar adjunctions. Conjugation preserves composition and the ordered units and
counits. The resulting left-adjoint comparisons are precisely strictScalarPull;
the geometric pullback compositor is gComp. This gives the displayed equation on
strict tower derived categories, including the prescribed transition maps. -/
theorem strictScalarPullComposition {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (M : Derived (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) Z) :
    (gComp (ULift.{u + 1} (Padic.coefficientExtensionIntegers l F)) f g).hom.app
        ((T l E F i Z).obj M) ≫
        (G (ULift.{u + 1} (Padic.coefficientExtensionIntegers l F)) f).map
          ((strictScalarPull l E F i g).inv.app M) ≫
        (strictScalarPull l E F i f).inv.app
          ((G (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) g).obj M) =
      (strictScalarPull l E F i (f ≫ g)).inv.app M ≫
        (T l E F i X).map
          ((gComp (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) f g).hom.app M)
    := by
  let A := ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)
  let B := ULift.{u + 1} (Padic.coefficientExtensionIntegers l F)
  let hf := TwoSquare.mk _ _ _ _ (strictScalarPull l E F i f).inv
  let hg := TwoSquare.mk _ _ _ _ (strictScalarPull l E F i g).inv
  let hfg := TwoSquare.mk _ _ _ _ (strictScalarPull l E F i (f ≫ g)).inv
  have h : hfg.whiskerLeft (gComp A f g).hom =
      (hg.vComp hf).whiskerRight (gComp B f g).hom := by
    apply (mateEquiv ((adj A g).comp (adj A f)) (adj B (f ≫ g))).injective
    rw [conjugateEquiv_mateEquiv_vcomp _ (adj A (f ≫ g)),
      mateEquiv_conjugateEquiv_vcomp _ ((adj B g).comp (adj B f)),
      mateEquiv_hcomp]
    change (mateEquiv (adj A (f ≫ g)) (adj B (f ≫ g)) hfg).whiskerTop
        (rComp A f g).hom =
      ((mateEquiv (adj A f) (adj B f) hf).hComp
        (mateEquiv (adj A g) (adj B g) hg)).whiskerBottom (rComp B f g).hom
    apply (mateEquiv (scalarAdj l E F i X) (scalarAdj l E F i Z)).injective
    rw [mateEquiv_whiskerTop, mateEquiv_whiskerBottom,
      mateEquiv_vcomp (scalarAdj l E F i X) (scalarAdj l E F i Y) (scalarAdj l E F i Z)]
    dsimp only [hf, hg, hfg]
    rw [strictScalarPull_double_mate, strictScalarPull_double_mate,
      strictScalarPull_double_mate]
    ext N
    have hr := (strictProperCompositionRestriction l E F i f g (f ≫ g) rfl).1 N
    simpa only [TwoSquare.whiskerLeft, TwoSquare.whiskerRight, TwoSquare.vComp,
      NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Functor.associator_hom_app, Functor.associator_inv_app, eqToIso_refl,
      Iso.refl_hom,
      NatTrans.id_app, Functor.map_id, Category.comp_id, Category.id_comp,
      Category.assoc] using hr.symm
  simpa only [hf, hg, hfg, TwoSquare.whiskerLeft, TwoSquare.whiskerRight,
    TwoSquare.vComp, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.associator_hom_app,
    Functor.associator_inv_app, Category.comp_id, Category.id_comp, Category.assoc] using
    (NatTrans.congr_app h M).symm

end WeilConjectures.PurStrictScalar
