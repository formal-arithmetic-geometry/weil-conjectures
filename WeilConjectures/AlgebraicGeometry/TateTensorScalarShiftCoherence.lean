/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteSmoothPurity.FiniteSmoothCoefficientArrows
public import WeilConjectures.CategoryTheory.Exact.ExactDegreeZeroAdjoint
public import WeilConjectures.SixFunctors.Etale.Derived.Shift
import all WeilConjectures.SixFunctors.Etale.Derived.Shift
import all WeilConjectures.CategoryTheory.Right.RightExactTensorShiftCancellation
import all WeilConjectures.CategoryTheory.Derived.DerivedTensorRightExact
import all WeilConjectures.AlgebraicGeometry.Etale.Hom.EtaleHomComparisonModels
import all WeilConjectures.AlgebraicGeometry.ExceptionalCoefficients.ExceptionalCoefficientMaps
import WeilConjectures.CategoryTheory.Adjunction.Derived.DerivedAdjointCochainCounit

/-! # Normalized scalar tensor comparison and integer shifts

Source: `literature/blueprint/latest/blueprint/sec-smooth-purity/sk-thm-purity-transport/
 sk-thm-purity-transport.proof.md`, Step 1 (blueprint: lem-pur-tate-tensor-scalar-shift-coherence).
The statement records the normalized scalar tensor square and the shifted exact-single
adjunction transpose for all integer shifts, including negative shifts and without a
flatness hypothesis on the coefficient map.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
universe u v w
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry
open AlgebraicGeometry.Etale

namespace AlgebraicGeometry.Etale

set_option backward.defeqAttrib.useBackward true
set_option linter.style.haveILetI false
attribute [local irreducible] Functor.leftDerivedFunctor Functor.leftDerivedFunctorCounit
  _root_.DerivedCategory.monoidalClosed
  _root_.DerivedCategory.instMonoidalCategory_weilConjectures
  _root_.DerivedCategory.commShift₂CurriedTensor
attribute [local instance 2000] scalarSheafMonoidal
open CategoryTheory.Functor MonoidalCategory _root_.DerivedCategory
open scoped CategoryTheory.Functor
attribute [local instance] Functor.postcompose_left_commShift Functor.postcompose_right_commShift
  Functor.precompose_left_commShift Functor.precompose_right_commShift

set_option maxHeartbeats 2000000 in
-- Derived tensor conjugation elaborates large adjunction and localization comparisons.
private theorem normalized_tensor_shifts
    {C : Type v} [Category.{u + 1} C] [Abelian C]
  [IsGrothendieckAbelian.{u + 1} C]
  [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C]
  [Abelian.HasFunctorialFlatResolution C]
  {D : Type w} [Category.{u + 1} D] [Abelian D]
  [IsGrothendieckAbelian.{u + 1} D]
  [MonoidalCategory D] [MonoidalPreadditive D] [MonoidalClosed D] [BraidedCategory D]
  [Abelian.HasFunctorialFlatResolution D]
  (E : C ⥤ D) (U : D ⥤ C) [E.Additive] [U.Additive] [E.PreservesKFlatQuasiIso]
  [PreservesFiniteLimits U] [PreservesFiniteColimits U]
    (adj : E ⊣ U) [E.PreservesFlat] [E.IsLeftAdjoint] [E.Monoidal]
    (G : DerivedCategory C ⥤ DerivedCategory D) (ad : G ⊣ U.mapDerivedCategory)
    (r : ∀ P : CochainComplex C ℤ, G.obj (DerivedCategory.Q.obj P) ⟶
      DerivedCategory.Q.obj ((E.mapHomologicalComplex (.up ℤ)).obj P))
    (hr : ∀ P, r P = (ad.leftAdjointUniq
        (adj.derivedAdjunction.ofNatIsoRight U.rightDerivedFunctorIsoMapDerivedCategory)).hom.app
          (DerivedCategory.Q.obj P) ≫ E.rightExact_cochainCounit P)
    (μ : ∀ K L : DerivedCategory C, G.obj K ⊗ G.obj L ≅ G.obj (K ⊗ L))
    (hμ : (∀ {K K'} (f : K ⟶ K') L,
        (G.map f ▷ G.obj L) ≫ (μ K' L).hom = (μ K L).hom ≫ G.map (f ▷ L)) ∧
      (∀ K {L L'} (f : L ⟶ L'),
        (G.obj K ◁ G.map f) ≫ (μ K L').hom = (μ K L).hom ≫ G.map (K ◁ f)) ∧
      Functor.rightExactTensorModelNormalization E G r μ)
    (K L : DerivedCategory C) (a b : ℤ) :
    letI := ad.leftAdjointCommShift ℤ
    G.map (DerivedCategory.shiftTensorShiftIso _ K L a b).hom ≫
      (G.commShiftIso (a + b)).hom.app (K ⊗ L) ≫ (μ K L).inv⟦a + b⟧' =
    (μ (K⟦a⟧) (L⟦b⟧)).inv ≫
      ((G.commShiftIso a).hom.app K ⊗ₘ (G.commShiftIso b).hom.app L) ≫
      (DerivedCategory.shiftTensorShiftIso _ (G.obj K) (G.obj L) a b).hom := by
  let bd := adj.derivedAdjunction.ofNatIsoRight U.rightDerivedFunctorIsoMapDerivedCategory
  let e := ad.leftAdjointUniq bd
  letI := ad.leftAdjointCommShift ℤ
  letI := bd.leftAdjointCommShift ℤ
  have := ad.commShift_of_rightAdjoint ℤ
  have := bd.commShift_of_rightAdjoint ℤ
  have := derived_counit_commShift E U adj
  have := adjointUniq_commShift G E.leftDerivedFunctor ad bd
  have heq := normalized_iso_eq E G e r hr μ hμ
  let τ := tensorConjugate G E.leftDerivedFunctor e
    (asIso E.rightExact_leftDerivedTensorComparison)
  have hleft (V : DerivedCategory C) : NatTrans.CommShift (τ.hom.app V) ℤ := by
    have : NatTrans.CommShift
        ((asIso E.rightExact_leftDerivedTensorComparison).hom.app V) ℤ := by
      change NatTrans.CommShift (nativeLeft E V) ℤ
      exact nativeLeft_commShift E V
    exact conjugate_left_commShift G E.leftDerivedFunctor e
      (asIso E.rightExact_leftDerivedTensorComparison) V
  have hright (V : DerivedCategory C) : NatTrans.CommShift (τ.hom.flipApp V) ℤ := by
    have : NatTrans.CommShift
        ((asIso E.rightExact_leftDerivedTensorComparison).hom.flipApp V) ℤ := by
      change NatTrans.CommShift (nativeRight E V) ℤ
      exact nativeRight_commShift E V
    exact conjugate_right_commShift G E.leftDerivedFunctor e
      (asIso E.rightExact_leftDerivedTensorComparison) V
  have hcomp (V W : DerivedCategory C) : (μ V W).inv = (τ.hom.app V).app W := by
    rw [heq]
    rfl
  simp only [hcomp]
  let δ (V W : DerivedCategory C) := (τ.hom.app V).app W
  have hfirst (V W : DerivedCategory C) (n : ℤ) :
      G.map (((tensorRight W).commShiftIso n).hom.app V) ≫
        (G.commShiftIso n).hom.app (V ⊗ W) ≫ (δ V W)⟦n⟧' =
      δ (V⟦n⟧) W ≫ ((G.commShiftIso n).hom.app V ▷ G.obj W) ≫
        ((tensorRight (G.obj W)).commShiftIso n).hom.app (G.obj V) := by
    have := hright W
    have h := NatTrans.shift_app_comm (τ.hom.flipApp W) n V
    change ((tensorRight W ⋙ G).commShiftIso n).hom.app V ≫ (δ V W)⟦n⟧' =
      δ (V⟦n⟧) W ≫ ((G ⋙ tensorRight (G.obj W)).commShiftIso n).hom.app V at h
    simpa only [Functor.comp_obj, Functor.comp_map, Functor.commShiftIso_comp_hom_app,
      Functor.whiskerLeft_app, tensorLeft, tensorRight, curriedTensor_obj_obj,
      curriedTensor_obj_map, Functor.flip_obj_obj, Functor.flip_obj_map,
      curriedTensor_map_app, Category.assoc] using h
  have hsecond (V W : DerivedCategory C) (n : ℤ) :
      G.map (((tensorLeft V).commShiftIso n).hom.app W) ≫
        (G.commShiftIso n).hom.app (V ⊗ W) ≫ (δ V W)⟦n⟧' =
      δ V (W⟦n⟧) ≫ (G.obj V ◁ (G.commShiftIso n).hom.app W) ≫
        ((tensorLeft (G.obj V)).commShiftIso n).hom.app (G.obj W) := by
    have := hleft V
    have h := NatTrans.shift_app_comm (τ.hom.app V) n W
    change ((tensorLeft V ⋙ G).commShiftIso n).hom.app W ≫ (δ V W)⟦n⟧' =
      δ V (W⟦n⟧) ≫ ((G ⋙ tensorLeft (G.obj V)).commShiftIso n).hom.app W at h
    simpa only [Functor.comp_obj, Functor.comp_map, Functor.commShiftIso_comp_hom_app,
      Functor.whiskerLeft_app, tensorLeft, tensorRight, curriedTensor_obj_obj,
      curriedTensor_obj_map, Functor.flip_obj_obj, Functor.flip_obj_map,
      curriedTensor_map_app, Category.assoc] using h
  have h₁ := NatTrans.shift_app_comm
    ((curriedTensor _).flip.map ((G.commShiftIso b).hom.app L)) a (G.obj K)
  have h₂ := (shiftFunctorAdd' _ b a (a + b) (add_comm b a)).inv.naturality (δ K L)
  dsimp at h₁ h₂
  simp only [DerivedCategory.shiftTensorShiftIso, Iso.trans_hom, Functor.mapIso_hom,
    Iso.app_hom, Iso.symm_hom, Category.assoc, Functor.map_comp,
    G.commShiftIso_add' (add_comm b a), Functor.CommShift.isoAdd'_hom_app,
    curriedTensor_obj_obj]
  rw [← Functor.map_comp_assoc G (((shiftFunctorAdd' _ b a (a + b) _).inv.app _)),
    Iso.inv_hom_id_app, CategoryTheory.Functor.map_id, Category.id_comp, ← h₂]
  erw [Functor.commShiftIso_hom_naturality_assoc]
  rw [← Functor.map_comp_assoc, ← Functor.map_comp_assoc, Category.assoc]
  erw [hsecond K L b]
  simp only [Functor.map_comp, Category.assoc]
  erw [reassoc_of% hfirst K (L⟦b⟧) a]
  erw [reassoc_of% h₁]
  simp only [_root_.CategoryTheory.MonoidalCategory.tensorHom_def, Category.assoc]
  rfl

set_option maxHeartbeats 2000000 in
-- The two presentations expand the same localized bifunctor shift structure.
private theorem site_tensor_shift_eq
    (R : Type (u + 1)) [CommRing R] (T : Scheme.{u})
    (K L : DerivedCategoryModule R T) (a b : ℤ) :
    derivedTensorShiftIso (ModuleCat.{u + 1} R) K L a b =
      DerivedCategory.shiftTensorShiftIso
        (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} R)) K L a b := by
  unfold derivedTensorShiftIso DerivedCategory.shiftTensorShiftIso
  apply Iso.ext
  delta commShiftDerivedTensorFlipObj commShiftDerivedTensorObj
    DerivedCategory.commShiftTensorRight DerivedCategory.commShiftTensorLeft
  delta DerivedCategory.commShift₂CurriedTensor
  rfl

private theorem transpose_shift
    {C D : Type*} [Category C] [Category D] [HasShift C ℤ] [HasShift D ℤ]
    {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) [G.CommShift ℤ]
    {X : C} {Y : D} (f : F.obj X ⟶ Y) (n : ℤ) :
    (adj.homEquiv (X⟦n⟧) (Y⟦n⟧)).symm
        ((adj.homEquiv X Y f)⟦n⟧' ≫ (G.commShiftIso n).inv.app Y) =
      (Adjunction.LeftAdjointCommShift.iso adj n).hom.app X ≫ f⟦n⟧' := by
  let := adj.leftAdjointCommShift ℤ
  let := adj.commShift_of_rightAdjoint ℤ
  have hc : F.map ((G.commShiftIso n).inv.app Y) ≫ adj.counit.app (Y⟦n⟧) =
      (F.commShiftIso n).hom.app (G.obj Y) ≫ (adj.counit.app Y)⟦n⟧' := by
    rw [adj.shift_counit_app n Y]
    simp only [Iso.hom_inv_id_app_assoc]
  have hf : F.map ((adj.homEquiv X Y) f) ≫ adj.counit.app Y = f :=
    (adj.homEquiv X Y).symm_apply_apply f
  rw [Adjunction.homEquiv_counit, F.map_comp, Category.assoc, hc,
    ← Category.assoc, F.commShiftIso_hom_naturality]
  rw [Category.assoc, ← (shiftFunctor D n).map_comp, hf]
  rfl

/-- The derived transpose of the shifted ordinary insertion, using the inverse exact
restriction shift comparison. Source: Stacks Tag 07A6
(blueprint: lem-pur-tate-tensor-scalar-shift-coherence). -/
def shiftedScalarAdjointInsertion
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (T : Scheme.{u})
    (M : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A))
    (P : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} B))
    (η : M ⟶ (Sheaf.restrictScalars T.smallEtaleTopology φ).obj P) (a : ℤ) :
    (scalarExtension φ T).obj ((DerivedCategory.singleFunctor _ 0).obj M⟦a⟧) ⟶
      (DerivedCategory.singleFunctor _ 0).obj P⟦a⟧ :=
  let D := Sheaf.derivedRestrictScalars T.smallEtaleTopology φ
  let adj : scalarExtension φ T ⊣ D := Adjunction.ofIsRightAdjoint D
  let I := SheafExactDegreeZero.adjointInsertion
    (Sheaf.restrictScalars T.smallEtaleTopology φ) adj η
  let gη := (adj.homEquiv _ _) I
  let gn := (shiftFunctor (DerivedCategory (Sheaf T.smallEtaleTopology
      (ModuleCat.{u + 1} A))) a).map gη ≫
    (D.commShiftIso a).inv.app ((DerivedCategory.singleFunctor _ 0).obj P)
  (adj.homEquiv _ _).symm gn

set_option maxHeartbeats 2000000 in
-- Checking the derived scalar normalization compares large adjunction instances.
/-- The normalized scalar tensor comparison commutes with canonical integer shifts, and the
same scalar mate shift transports every exact-single adjunction insertion.

Source: `literature/blueprint/latest/blueprint/sec-smooth-purity/sk-thm-purity-transport/
sk-thm-purity-transport.proof.md`, Step 1 (blueprint: lem-pur-tate-tensor-scalar-shift-coherence).
Proof (Stacks Tags 06YY, 06YU, 07A4, 07A6 and More on Algebra Tag 0FNH):
1. Let `q_P : F(QP) ⟶ Q(EP)` be the canonical scalar representative, invertible on
   flat-term K-flat `P`. The representative adjunction has unit `x ↦ 1 ⊗ x`, and termwise
   scalar extension `E` and restriction commute with the reindexing shift (differential
   times `(-1)^n`), leaving this unit unchanged. By naturality, resolving localization and
   uniqueness of transposition, the localized reindexing shift is the mate shift
   `scalarShiftIso`, so `q_P` intertwines it with the termwise `E`-shift for every `n`.
2. Termwise `E` preserves flat-term K-flatness without flatness of `B` over `A`. The
   balancing map `b ⊗ (x ⊗ y) ↦ (b ⊗ x) ⊗ (1 ⊗ y)` commutes with the first-input shift
   (no sign) and the second-input shift by `n` (both paths multiply the summand of first
   degree `p` by `(-1)^(np)`, and `φ(-1) = -1`), for all `n` and unbounded `P, Q`.
3. Localize these squares and conjugate by the scalar and tensor representative
   isomorphisms. Uniqueness of the normalized comparison identifies the balancing map with
   `tensorIso`; derived tensor-shift descent identifies the localized tensor shifts with
   the fixed one-variable derived shifts. Step 1 identifies the scalar shifts. Hence both
   one-variable squares hold on arbitrary derived `K, L`.
4. Expand `derivedTensorShiftIso` as the first-variable shift, the shifted second-variable
   shift and the inverse shift-addition. Use the addition axiom of the CommShift structure
   `scalarShiftIso`, naturality of `s_a`, the two squares of Step 3 (the second under the
   shift `a`, the first at `K, L⟦b⟧`) and naturality of the first-variable shift in its
   fixed argument, then tensor interchange. The extraction order is never exchanged, so no
   sign `(-1)^(ab)` appears. This is the first conjunct.
5. Let `h` be `single(η)` followed by the inverse exact-single comparison, so
   `I(η) = F(h) ≫ ε` and `I_a(η) = F(h⟦a⟧ ≫ r⁻¹) ≫ ε` for the restriction shift `r`. The
   counit equation defining the mate, `F(r) ≫ s ≫ ε⟦a⟧ = ε`, and naturality of `s` at `h`
   give `I_a(η) = s ≫ I(η)⟦a⟧`, for zero, positive and negative `a`, with no flatness of
   `M` or `B`. This is the second conjunct.
-/
theorem normalizedScalarTensorShiftCoherence
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) (T : Scheme.{u})
    (K L : DerivedCategoryModule A T) (a b : ℤ)
    (M : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A))
    (P : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} B))
    (η : M ⟶ (Sheaf.restrictScalars T.smallEtaleTopology φ).obj P) :
    (scalarExtension φ T).map (derivedTensorShiftIso (ModuleCat.{u + 1} A) K L a b).hom ≫
        ((FiniteSmoothPurity.scalarShiftIso φ T (a + b)).hom.app
          (((derivedTensor (ModuleCat.{u + 1} A) T).obj K).obj L)) ≫
        (shiftFunctor _ (a + b)).map ((ExceptionalCoefficients.tensorIso φ T).hom.app (K, L)) =
      (ExceptionalCoefficients.tensorIso φ T).hom.app (K⟦a⟧, L⟦b⟧) ≫
        derivedTensorHom (ModuleCat.{u + 1} B)
          ((FiniteSmoothPurity.scalarShiftIso φ T a).hom.app K)
          ((FiniteSmoothPurity.scalarShiftIso φ T b).hom.app L) ≫
        (derivedTensorShiftIso (ModuleCat.{u + 1} B) ((scalarExtension φ T).obj K)
          ((scalarExtension φ T).obj L) a b).hom ∧
      shiftedScalarAdjointInsertion φ T M P η a =
        (FiniteSmoothPurity.scalarShiftIso φ T a).hom.app
          ((DerivedCategory.singleFunctor _ 0).obj M) ≫
        (shiftFunctor (DerivedCategory (Sheaf T.smallEtaleTopology
          (ModuleCat.{u + 1} B))) a).map
          (SheafExactDegreeZero.adjointInsertion
            (Sheaf.restrictScalars T.smallEtaleTopology φ)
            (Adjunction.ofIsRightAdjoint
              (Sheaf.derivedRestrictScalars T.smallEtaleTopology φ)) η) := by
  constructor
  · let E := ProEtale.etaleSheafExtendScalars φ T
    let U := Sheaf.restrictScalars T.smallEtaleTopology φ
    let adj : E ⊣ U := ProEtale.etaleSheafExtendScalarsAdjunction φ T
    let ad : scalarExtension φ T ⊣ U.mapDerivedCategory :=
      Adjunction.ofIsRightAdjoint _
    letI : E.IsLeftAdjoint := adj.isLeftAdjoint
    letI : E.PreservesFlat := extension_preservesFlat φ T
    letI : E.PreservesKFlatQuasiIso := extension_preservesKFlatQuasiIso φ T
    letI : E.OplaxMonoidal := adj.leftAdjointOplaxMonoidal
    letI : E.Monoidal := CategoryTheory.composeAndSheafifyMonoidal
      T.smallEtaleTopology (ModuleCat.extendRestrictScalarsAdj.{u + 1, u + 1, u + 1} φ)
    let bd : E.leftDerivedFunctor ⊣ U.mapDerivedCategory :=
      adj.derivedAdjunction.ofNatIsoRight U.rightDerivedFunctorIsoMapDerivedCategory
    let e : scalarExtension φ T ≅ E.leftDerivedFunctor := ad.leftAdjointUniq bd
    have hr : ∀ Q, scalarExtensionRepresentative φ T Q =
        e.hom.app (_root_.DerivedCategory.Q.obj Q) ≫ E.rightExact_cochainCounit Q := by
      intro Q
      unfold scalarExtensionRepresentative
      rw [← mapComplex_unit_formula]
      dsimp only [Functor.rightExact_cochainCounit]
      have hh := (Adjunction.leftDerivedCochainCounit E U adj ad Q).symm
      simp only [E, U, adj, ad, e, bd, Functor.id_obj, Iso.app_inv,
        Iso.app_hom] at hh ⊢
      exact hh
    have hμ := (etaleHomTensorComparison_existsUnique T φ).choose_spec.1
    letI := etaleHomScalarCommShift T φ
    have hgeneric := normalized_tensor_shifts E U adj (scalarExtension φ T) ad
      (scalarExtensionRepresentative φ T) hr
      (etaleHomTensorComparison T φ) hμ K L a b
    simpa only [site_tensor_shift_eq, FiniteSmoothPurity.scalarShiftIso,
      FiniteSmoothPurity.ordinaryScalar, Category.assoc, derivedTensorHom, derivedTensor,
      MonoidalCategory.tensorHom_def, curriedTensor_obj_obj,
      curriedTensor_obj_map, curriedTensor_map_app, Functor.comp_obj,
      Functor.prod_obj, scalar_tensor_eq φ T] using hgeneric
  · dsimp [shiftedScalarAdjointInsertion]
    exact transpose_shift
      (Adjunction.ofIsRightAdjoint
        (Sheaf.derivedRestrictScalars T.smallEtaleTopology φ))
      (SheafExactDegreeZero.adjointInsertion
        (Sheaf.restrictScalars T.smallEtaleTopology φ)
        (Adjunction.ofIsRightAdjoint
          (Sheaf.derivedRestrictScalars T.smallEtaleTopology φ)) η) a

end AlgebraicGeometry.Etale
