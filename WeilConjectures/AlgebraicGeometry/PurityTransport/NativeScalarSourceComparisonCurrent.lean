/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.PurityTransport.TransportScalarLines
import WeilConjectures.CategoryTheory.DerivedFlatScalarSingle

/-! # The specified native Tate source comparison

Source: current blueprint sk-prop-sp-rational-adjunction, scalar extension across
pullback, Tate powers, and shift (blueprint: lem-sp-native-scalar-source-comparison-current).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.PurityTransport

set_option maxHeartbeats 1000000 in
-- Elaborate the native scalar adjunction and single comparisons together.
private theorem scalarLineZero_factor (ell : ℕ) [Fact ell.Prime]
    {c c' : Coefficient ell} (a : c.bundled.{u} ell ⟶ c'.bundled ell)
    (X : Scheme.{u}) (d : ℕ)
    (e : (Mod.extendScalars (coefficientMap (Λ := c.obj ell) (Λ' := c'.obj ell) a.hom.hom X)).obj
      (c.line ell X d) ≅ c'.line ell X d) :
    scalarLineZero ell a X d e =
      ((Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap (Λ := c.obj ell)
      (Λ' := c'.obj ell) a.hom.hom X)
        ).homEquiv _ _).symm
        ((DerivedCategory.singleFunctor _ 0).map
            ((Mod.extendRestrictAdjunction (coefficientMap (Λ := c.obj ell)
      (Λ' := c'.obj ell) a.hom.hom X)).unit.app
              (c.line ell X d)) ≫
          ((Mod.comap (coefficientMap (Λ := c.obj ell)
      (Λ' := c'.obj ell) a.hom.hom X)).mapDerivedCategorySingleFunctor 0
            ).inv.app ((Mod.extendScalars (coefficientMap (Λ := c.obj ell)
      (Λ' := c'.obj ell) a.hom.hom X)).obj
              (c.line ell X d))) ≫
        (DerivedCategory.singleFunctor _ 0).map e.hom := by
  rw [← Adjunction.homEquiv_naturality_right_symm]
  unfold scalarLineZero
  congr 1
  rw [Adjunction.homEquiv_unit, Functor.map_comp, Category.assoc]
  rw [Category.assoc]
  exact congrArg
    ((DerivedCategory.singleFunctor _ 0).map
      ((Mod.extendRestrictAdjunction (coefficientMap (Λ := c.obj ell)
        (Λ' := c'.obj ell) a.hom.hom X)).unit.app (c.line ell X d)) ≫ ·)
    (((Mod.comap (coefficientMap (Λ := c.obj ell)
      (Λ' := c'.obj ell) a.hom.hom X)).mapDerivedCategorySingleFunctor 0
        ).inv.naturality e.hom)


/-- The degree-zero scalar adjunct is invertible on a flat Tate power.
Source: Stacks 07A4 and the derived Tate-line step of sk-prop-sp-rational-adjunction.
Proof: factor the map through the canonical single-object adjunct, which is an
isomorphism because this Tate power is flat. Its remaining factor is the single
functor applied to the prescribed ordinary line isomorphism.
(blueprint: lem-sp-native-scalar-source-comparison-current). -/
private theorem scalarLineZero_isIso (ell : ℕ) [Fact ell.Prime]
    {c c' : Coefficient ell} (a : c.bundled.{u} ell ⟶ c'.bundled ell)
    (X : Scheme.{u}) [∀ x : X, Invertible (ell : X.residueField x)] (d : ℕ)
    (e : (Mod.extendScalars (coefficientMap (Λ := c.obj ell) (Λ' := c'.obj ell) a.hom.hom X)).obj
      (c.line ell X d) ≅ c'.line ell X d) : IsIso (scalarLineZero ell a X d e) := by
  rw [scalarLineZero_factor]
  have := isIso_flatSingle_adjunct
    (Mod.extendScalars (coefficientMap (Λ := c.obj ell) (Λ' := c'.obj ell) a.hom.hom X))
    (Mod.comap (coefficientMap (Λ := c.obj ell) (Λ' := c'.obj ell) a.hom.hom X))
    (Mod.extendRestrictAdjunction (coefficientMap (Λ := c.obj ell) (Λ' := c'.obj ell) a.hom.hom X))
    (Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap (Λ := c.obj ell)
      (Λ' := c'.obj ell) a.hom.hom X))
    (c.line ell X d) (line_flat ell c X d)
  infer_instance

/-- The normalized shifted line comparison remains invertible.
Source: the shift in the native Tate scalar comparison.
Proof: shifts preserve isomorphisms, and the canonical scalar/shift comparison
is already an isomorphism.
(blueprint: lem-sp-native-scalar-source-comparison-current). -/
private theorem scalarLineMap_isIso (ell : ℕ) [Fact ell.Prime]
    {c c' : Coefficient ell} (a : c.bundled.{u} ell ⟶ c'.bundled ell)
    (X : Scheme.{u}) [∀ x : X, Invertible (ell : X.residueField x)] (d : ℕ)
    (e : (Mod.extendScalars (coefficientMap (Λ := c.obj ell) (Λ' := c'.obj ell) a.hom.hom X)).obj
      (c.line ell X d) ≅ c'.line ell X d) : IsIso (scalarLineMap ell a X d e) := by
  have := scalarLineZero_isIso ell a X d e
  unfold scalarLineMap
  infer_instance

set_option maxHeartbeats 1000000 in
-- Derived monoidal comparison components unfold several native functors.
/-- The normalized source scalar components form a natural isomorphism.
Source: scalar/pullback and scalar/tensor comparisons in sk-prop-sp-rational-adjunction.
Proof: commute scalar extension with right tensoring using its normalized derived
monoidal tensorator. Insert the prescribed pullback scalar isomorphism, with
exact/left-derived comparisons on both sides. Finally tensor with the prescribed
shifted Tate-line isomorphism. Functor associators give the displayed endpoints.
The component formula is the definition of sourceScalar, using tensor interchange.
(blueprint: lem-sp-native-scalar-source-comparison-current). -/
theorem scalarSourceIso_nonempty (ell : ℕ) [Fact ell.Prime]
    {c c' : Coefficient ell} (a : c.bundled.{u} ell ⟶ c'.bundled ell)
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [∀ x : X, Invertible (ell : X.residueField x)] (d : ℕ)
    (ha : c.integralMap ell ≫ a.hom.hom = c'.integralMap ell)
    (p : ScalarLineCoordinates ell a ha X) :
    ∃ v : c.smoothSource ell f d ⋙ CondensedRing.scalarSixChange a X ≅
        CondensedRing.scalarSixChange a Y ⋙ c'.smoothSource ell f d,
      ∀ K, v.hom.app K = sourceScalar ell a f d ha p K := by
  let φ := coefficientMap (Λ := c.obj ell) (Λ' := c'.obj ell) a.hom.hom X
  let := (Mod.exists_extendScalarsMonoidal φ).choose
  let := Mod.extendScalars_preservesFlat φ
  let := (Mod.extendRestrictAdjunction φ).isLeftAdjoint
  let := (Mod.extendScalars φ).leftDerivedFunctorMonoidal
  let P₀ := (CondensedRing.upperStar (c.obj ell) f).leftDerivedFunctor
  let P₁ := (CondensedRing.upperStar (c'.obj ell) f).leftDerivedFunctor
  let QX := CondensedRing.scalarSixChange a X
  let QY := CondensedRing.scalarSixChange a Y
  let : QX.Monoidal := (Mod.extendScalars φ).leftDerivedFunctorMonoidal
  let L₀ := c.derivedLine ell X d
  let L₁ := c'.derivedLine ell X d
  have := scalarLineMap_isIso ell a X d (p.power d)
  let l : QX.obj L₀ ≅ L₁ := asIso (scalarLineMap ell a X d (p.power d))
  let pull : P₀ ⋙ QX ≅ QY ⋙ P₁ :=
    Functor.isoWhiskerRight
        (CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory (c.obj ell) f) QX ≪≫
      scalarPullbackIso a f ≪≫
      Functor.isoWhiskerLeft QY
        (CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory (c'.obj ell) f).symm
  let twist : tensorRight (QX.obj L₀) ≅ tensorRight L₁ :=
    NatIso.ofComponents (fun K ↦ tensorIso (Iso.refl K) l) (by
      intro K L g
      simp only [tensorIso_hom, Iso.refl_hom, id_tensorHom]
      exact (whisker_exchange g l.hom).symm)
  let v : c.smoothSource ell f d ⋙ QX ≅ QY ⋙ c'.smoothSource ell f d :=
    Functor.associator P₀ (tensorRight L₀) QX ≪≫
      Functor.isoWhiskerLeft P₀ (Functor.Monoidal.commTensorRight QX L₀).symm ≪≫
      (Functor.associator P₀ QX (tensorRight (QX.obj L₀))).symm ≪≫
      Functor.isoWhiskerRight pull (tensorRight (QX.obj L₀)) ≪≫
      Functor.associator QY P₁ (tensorRight (QX.obj L₀)) ≪≫
      Functor.isoWhiskerLeft QY (Functor.isoWhiskerLeft P₁ twist)
  refine ⟨v, ?_⟩
  intro K
  simp only [v, twist, pull, sourceScalar, scalarTensor, Iso.trans_hom,
    Iso.symm_hom, NatTrans.comp_app, Functor.associator_hom_app,
    Functor.associator_inv_app, Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.Monoidal.commTensorRight_inv_app,
    NatIso.ofComponents_hom_app, tensorIso_hom, Iso.refl_hom,
    tensorRight, curriedTensor, Functor.flip,
    Functor.mapIso_hom, Iso.app_hom, Iso.app_inv, asIso_hom,
    Category.id_comp, MonoidalCategory.tensorHom_def, id_whiskerRight,
    Functor.Monoidal.μIso_inv, l, L₀, L₁, QX, QY, P₀, P₁]
  erw [Category.id_comp]
  rfl

end AlgebraicGeometry.ProEtale.PurityTransport
