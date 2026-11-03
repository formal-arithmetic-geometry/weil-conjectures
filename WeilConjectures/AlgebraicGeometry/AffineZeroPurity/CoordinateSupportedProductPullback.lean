/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AffineZeroPurity.CoordinateZeroBaseChange
import WeilConjectures.AlgebraicGeometry.AffineZeroPurity.CoordinateProductPullbackData
import WeilConjectures.AlgebraicGeometry.AffineZeroPurity.CoordinateBoundaryPullback
import WeilConjectures.AlgebraicGeometry.AffineZeroPurity.CoordinateZeroBaseChange
import WeilConjectures.SmoothPurity.PurityFiniteSetting.PurityFrameClass
import Mathlib.RingTheory.LocalRing.Defs
import Mathlib.Logic.Relation
import Mathlib.LinearAlgebra.Span.Defs
import WeilConjectures.SmoothPurity.LocalGeneratingTuples
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.LinearAlgebra.Span.Basic
import WeilConjectures.CategoryTheory.Sites.SmoothPurity.SupportLongExact
import WeilConjectures.SmoothPurity.PurityFiniteSetting.Supported.SupportedCupFunctoriality
import WeilConjectures.AlgebraicGeometry.Pur.PurTwistSheafLocallyFree
import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicCoefficientTwistsUnrestricted
import Mathlib.AlgebraicGeometry.AffineSpace
import WeilConjectures.AlgebraicGeometry.Support.SupportCohomology
import WeilConjectures.AlgebraicGeometry.Supported.SupportedCup
import WeilConjectures.CategoryTheory.Monoidal.Conjugate
import WeilConjectures.SixFunctors.ProEtale.RingSheaf.UpperStarSquare
import WeilConjectures.AlgebraicGeometry.AffineZeroPurity.DerivedSingleTensorPullback
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.TensorSheaf
import WeilConjectures.AlgebraicGeometry.EtaleSingleTensoratorPullback
import Mathlib.Logic.Small.Defs
import Mathlib.CategoryTheory.Limits.HasLimits
import all WeilConjectures.AlgebraicGeometry.AffineSpacePurity.AffineSpacePurityComparison
import all WeilConjectures.AlgebraicGeometry.AffineZeroPurity.AffineSpaceCoordinateBoundaries
import all WeilConjectures.AlgebraicGeometry.AffineZeroPurity.AffineSpaceThomMap
import all WeilConjectures.AlgebraicGeometry.AffineZeroPurity.AffineSpaceZeroSectionConstructions
public import WeilConjectures.AlgebraicGeometry.CoordinateDivisorBaseChange

/-! # Pullback of the supported coordinate product -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048
universe u v w
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open AlgebraicGeometry WeilConjectures
namespace AlgebraicGeometry.ProEtale.AffineZeroPurity
open AffineSpacePurity

set_option allowUnsafeReducibility true in
attribute [local implicit_reducible] PurityFiniteSetting.Coefficient PurityFiniteSetting.Ring
  PurityFiniteSetting.coefficientCommRing PurityFiniteSetting.ringCommRing
  AffineLinePurity.Ring Scheme.finiteTateCoefficient setting

set_option allowUnsafeReducibility true in
attribute [local reducible] cupTensorObject
  classSource supportData cupSingle
  AffineSpacePurity.D
  PurityFiniteSetting.functorialCupSheaves PurityFiniteSetting.functorialCupTopology
  PurityFiniteSetting.functorialCupCategory PurityFiniteSetting.functorialCupAbelian
  PurityFiniteSetting.functorialCupHasDerived PurityFiniteSetting.functorialCupSource
  PurityFiniteSetting.functorialCupMonoidal
  PurityFiniteSetting.functorialCupInverseImage PurityFiniteSetting.functorialCupConstant

private theorem action_pullback_succ
    {C : Type v} {D : Type w} [Category C] [Category D]
    (T : C ⥤ C ⥤ C) (T' : D ⥤ D ⥤ D) (H : C ⥤ D)
    (N : C) (N' : D) (eN : H.obj N ≅ N')
    (δ : ∀ M, H.obj ((T.obj M).obj N) ≅ (T'.obj (H.obj M)).obj (H.obj N))
    (K : C) (K' : D) (u : H.obj K ≅ K') (d : ℕ) :
    let F := T.flip.obj N
    let G := T'.flip.obj N'
    let e := fun M ↦ δ M ≪≫ (T'.obj (H.obj M)).mapIso eN
    let b := fun j ↦ actionPullbackIso F G H e K j ≪≫ (action G j).mapIso u
    (b (d + 1)).hom =
      (δ ((action F d).obj K)).hom ≫
        (T'.mapIso (b d)).hom.app (H.obj N) ≫
        (T'.obj ((action G d).obj K')).map eN.hom := by
  dsimp only
  simp only [actionPullbackIso, action, Iso.trans_hom, Functor.mapIso_hom,
    Functor.comp_map, Functor.comp_obj, Functor.flip_obj_map,
    Functor.flip_obj_obj, Category.assoc]
  rw [← NatTrans.comp_app, ← T'.map_comp, NatTrans.naturality]

private theorem refl_component {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) (X : C) : (Iso.refl F).app X = Iso.refl (F.obj X) := rfl

set_option maxHeartbeats 2000000 in
-- Elaborate the recursive tensor comparison at its literal derived endpoints.
private theorem targetPullbackIso_succ (P : PurityFiniteSetting.{u}) (n : ℕ)
    {X' X : Scheme.{u}} (v : X' ⟶ X) (aX : X ⟶ Spec (.of P.field.k)) (d : ℕ) :
    (targetPullbackIso P n v aX (d + 1)).hom =
      (inverseImageTensorIso (setting P n).Coefficient v (target P n X d)
        (shiftedLine (setting P n) X)).hom ≫
        (AffineSpacePurity.tensorIso (setting P n).Coefficient X'
          (targetPullbackIso P n v aX d) (shiftedLinePullback (setting P n) v aX)).hom := by
  have h := action_pullback_succ
    (AffineSpacePurity.tensor (setting P n).Coefficient X)
    (AffineSpacePurity.tensor (setting P n).Coefficient X')
    (inverseImage (setting P n).Coefficient v)
    (shiftedLine (setting P n) X) (shiftedLine (setting P n) X')
    (shiftedLinePullback (setting P n) v aX)
    (fun M ↦ inverseImageTensorIso (setting P n).Coefficient v M
      (shiftedLine (setting P n) X)) (unit P n X) (unit P n X')
    (unitPullback P n v) d
  unfold targetPullbackIso AffineSpacePurity.tensorIso
  simp only [Functor.mapIso_refl, refl_component, Iso.refl_trans]
  with_unfolding_all exact h

private theorem targetPullbackIso_zero (P : PurityFiniteSetting.{u}) (n : ℕ)
    {X' X : Scheme.{u}} (v : X' ⟶ X) (aX : X ⟶ Spec (.of P.field.k)) :
    targetPullbackIso P n v aX 0 = unitPullback P n v := by
  apply Iso.ext
  exact Category.id_comp _

private theorem cupZero_base_irrel (Q : PurityFiniteSetting.{u})
    {Z W X : Scheme.{u}} (aX bX : X ⟶ Spec (.of Q.field.k))
    (i : Z ⟶ X) (j : W ⟶ X) [IsClosedImmersion i] [IsClosedImmersion j]
    (F G : CupPlus Q X)
    (α : (cupSingle Q X).obj ((lowerStar (ModuleCat.{u + 1} Q.Coefficient) i).obj
      (Q.constant Z)) ⟶ F.obj)
    (β : (cupSingle Q X).obj ((lowerStar (ModuleCat.{u + 1} Q.Coefficient) j).obj
      (Q.constant W)) ⟶ G.obj) :
    cupZero Q aX i j F G α β = cupZero Q bX i j F G α β := by
  rfl

private theorem targetPullbackIso_eqToHom (P : PurityFiniteSetting.{u}) (n : ℕ)
    {X' X : Scheme.{u}} (v : X' ⟶ X) (aX : X ⟶ Spec (.of P.field.k))
    {d e : ℕ} (h : d = e) :
    (inverseImage (setting P n).Coefficient v).map
        (eqToHom (congrArg (target P n X) h)) ≫
      (targetPullbackIso P n v aX e).hom =
    (targetPullbackIso P n v aX d).hom ≫
      eqToHom (congrArg (target P n X') h) := by
  subst e
  simp only [eqToHom_refl, CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]

private theorem target_successor_cast (P : PurityFiniteSetting.{u}) (n : ℕ)
    (X : Scheme.{u}) (d : ℕ) :
    eqToHom (target_succ P n X d) =
      𝟙 (cupTensorObject (setting P n) X (target P n X d)
        (shiftedLine (setting P n) X)) := by
  rfl

private theorem product_cons (P : PurityFiniteSetting.{u}) (n : ℕ)
    (B : Scheme.{u}) (aB : B ⟶ Spec (.of P.field.k)) (c : ℕ)
    (i : Fin c) (is : List (Fin c)) :
    product P n B aB c (i :: is) =
      cupZero (setting P n) (towerBase aB c) (supportMap B c is) (inclusion B c i)
        ⟨target P n (iteratedAffineLine B c) is.length,
          target_plus P n _ (towerBase aB c) is.length⟩
        ⟨shiftedLine (setting P n) (iteratedAffineLine B c), boundary_plus P n _⟩
        (product P n B aB c is) (boundary P n B aB c i) := by
  conv_lhs =>
    unfold product
    dsimp only [coordinateProductFold, coordinateProductTransport, coordinateProductStart]
  erw [eqToHom_refl, Category.id_comp, eqToHom_refl, Category.id_comp,
    target_successor_cast, Category.comp_id]
  with_unfolding_all rfl

private theorem coordinateProduct_pullback (P : PurityFiniteSetting.{u}) (n : ℕ)
    {B' B : Scheme.{u}} (g : B' ⟶ B) (aB : B ⟶ Spec (.of P.field.k))
    (c : ℕ) (is : List (Fin c)) :
    (coordinateListSourcePullback P n g c is).inv ≫
      (inverseImage (setting P n).Coefficient (spaceMap g c)).map
        (product P n B aB c is) ≫
      (targetPullbackIso P n (spaceMap g c) (towerBase aB c) is.length).hom =
    product P n B' (g ≫ aB) c is := by
  induction is with
  | nil =>
    have h := coordinateProduct_nil_pullback P n g aB c
    apply (cancel_epi (coordinateListSourcePullback P n g c []).hom).mp
    with_unfolding_all simpa only [Category.assoc, Iso.hom_inv_id_assoc, List.length_nil,
      targetPullbackIso_zero, target, action, Functor.id_obj] using h
  | cons i is ih =>
    let p := coordinateZeroLocusMap g c i
    have hp : IsPullback p (inclusion B' c i) (inclusion B c i) (spaceMap g c) := by
      simpa only [spaceMap] using coordinateZeroLocus_isPullback g c i
    let sq : ChosenCartesianSquare p (inclusion B' c i) (inclusion B c i)
        (spaceMap g c) :=
      ⟨hp.toCommSq, hp.isoPullback, hp.isoPullback_hom_fst, hp.isoPullback_hom_snd⟩
    have h := supportedCupZero_pullback (setting P n) (towerBase aB c)
      (supportMap B c is) (inclusion B c i)
      (supportMap B' c is) (inclusion B' c i) (spaceMap g c)
      (coordinateSupportMap g c is) p (coordinateSupportMap g c (i :: is))
      (coordinateSupportSquare g c is) sq (coordinateSupportSquare g c (i :: is))
      ⟨target P n (iteratedAffineLine B c) is.length,
        target_plus P n _ (towerBase aB c) is.length⟩
      ⟨shiftedLine (setting P n) (iteratedAffineLine B c), boundary_plus P n _⟩
      ⟨target P n (iteratedAffineLine B' c) is.length,
        target_plus P n _ (towerBase (g ≫ aB) c) is.length⟩
      ⟨shiftedLine (setting P n) (iteratedAffineLine B' c), boundary_plus P n _⟩
      (targetPullbackIso P n (spaceMap g c) (towerBase aB c) is.length)
      (shiftedLinePullback (setting P n) (spaceMap g c) (towerBase aB c))
      (eqToHom (classSource_eq P n B c is).symm ≫ product P n B aB c is)
      (boundary P n B aB c i)
    have hb := coordinateBoundary_pullback P n g aB c i p sq
    dsimp only [coordinateListSourcePullback] at ih
    simp only [Iso.trans_inv, Iso.symm_inv, Functor.mapIso_inv, classSource, cupSingle,
      eqToIso.hom, eqToIso.inv, eqToHom_refl, CategoryTheory.Functor.map_id,
      Category.id_comp, Category.comp_id] at ih
    simp only [eqToHom_refl, Category.id_comp] at h
    erw [ih, hb] at h
    rw [cupZero_base_irrel (setting P n) (spaceMap g c ≫ towerBase aB c)
      (towerBase (g ≫ aB) c)] at h
    rw [product_cons, product_cons]
    dsimp only [coordinateListSourcePullback]
    erw [Iso.trans_inv, Iso.trans_inv]
    simp only [Iso.symm_inv, Functor.mapIso_inv, eqToIso.hom, eqToIso.inv]
    erw [eqToHom_refl, eqToHom_refl, CategoryTheory.Functor.map_id,
      Category.id_comp, Category.comp_id]
    change _ ≫ _ ≫ (targetPullbackIso P n (spaceMap g c)
      (towerBase aB c) (is.length + 1)).hom = _
    erw [targetPullbackIso_succ]
    with_unfolding_all exact h

/-- Arbitrary pullback preserves the actual supported coordinate product.
Source: literature/blueprint/latest/blueprint/sec-smooth-purity/sk-prop-an/
cor-pur-affine-space-zero-section-purity.proof.md, final Cartier-map base-change
sentence; parent proof Step 3 (blueprint: lem-pur-coordinate-supported-product-pullback).

Proof: each coordinate divisor pulls back to its namesake, and multiplication
by the corresponding polynomial variable remains injective over an arbitrary
coefficient ring, including after killing other coordinates. Apply the geometric
Cartier naturality clause of cartier_kummer_map to each actual boundary, at the
chosen annihilating exponent. Induct over the coordinate list defining product.
The empty step is the normalized constant unit; the successor uses the supported
cup pullback equation, exact monoidal inverse image, and its single and shift
comparisons. This is the tensor product target, so retain its ordered tensor
pullback comparison rather than replacing it by an arbitrary Tate isomorphism.
For the full list, the comparison of the pulled-back total intersection with
the primed zero section is unique over the affine space. Restriction of the
constant unit normalizes its coefficient exchange. Thus it agrees with
coordinateSourcePullback, and the ordered tensor target comparison agrees with
targetPullbackIso. Transport the list induction by these identifications.
The argument includes the empty list, an empty base and zero coefficients. -/
theorem coordinate_supported_product_pullback (P : PurityFiniteSetting.{u}) (n : ℕ)
    {B' B : Scheme.{u}} (g : B' ⟶ B) (aB : B ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aB] [QuasiCompact aB] [IsSeparated aB]
    [LocallyOfFiniteType (g ≫ aB)] [QuasiCompact (g ≫ aB)] [IsSeparated (g ≫ aB)] (c : ℕ) :
    (coordinateSourcePullback P n g c).inv ≫
        (inverseImage (setting P n).Coefficient (spaceMap g c)).map
          (supportedClass P n B aB c) ≫
        (targetPullbackIso P n (spaceMap g c) (towerBase aB c) c).hom =
      supportedClass P n B' (g ≫ aB) c := by
  have h := coordinateProduct_pullback P n g aB c (List.finRange c)
  have hs := coordinateSupportTransport_pullback P n g c
  rw [supportedClass_transport, supportedClass_transport]
  simp only [Functor.map_comp, Category.assoc]
  rw [targetPullbackIso_eqToHom P n (spaceMap g c) (towerBase aB c)
    (@List.length_finRange c)]
  have hs' := congrArg (fun f ↦ (coordinateSourcePullback P n g c).inv ≫ f ≫
    (coordinateListSourcePullback P n g c (List.finRange c)).inv) hs
  simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.hom_inv_id,
    Category.comp_id] at hs'
  rw [reassoc_of% hs', reassoc_of% h]

end AlgebraicGeometry.ProEtale.AffineZeroPurity
