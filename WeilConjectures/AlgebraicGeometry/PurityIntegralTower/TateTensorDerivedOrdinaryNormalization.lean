/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.PurityIntegralTower.TateTensorOrdinaryTransition
public import WeilConjectures.CategoryTheory.Exact.ExactDegreeZeroAdjoint
public import WeilConjectures.AlgebraicGeometry.Etale.Hom.EtaleHomComparisonModels
public import WeilConjectures.AlgebraicGeometry.EtaleSingleCochainMonoidal
public import WeilConjectures.AlgebraicGeometry.EtaleSingleTensoratorFactorization
public import WeilConjectures.AlgebraicGeometry.ExceptionalCoefficients.ExceptionalCoefficientMaps
public import WeilConjectures.AlgebraicGeometry.FiniteGeneralRingOrdinaryScalarUnit
public import WeilConjectures.AlgebraicGeometry.FiniteSmoothPurity.CoefficientLineComparison.FiniteSmoothRootDerivedNormalization
public import WeilConjectures.AlgebraicGeometry.FiniteSmoothPurity.FiniteSmoothCoefficientArrows
public import WeilConjectures.AlgebraicGeometry.FiniteSmoothPurity.ScalarSingleAdjointInsertion
public import WeilConjectures.CategoryTheory.Adjunction.Derived.DerivedAdjointCochainCounit
public import WeilConjectures.CategoryTheory.Derived.DerivedTensorRightExact
public import WeilConjectures.CategoryTheory.Right.RightExactTensorShiftCancellation
public import WeilConjectures.SixFunctors.Etale.Derived.Shift
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.TensorShiftIso
public import WeilConjectures.SixFunctors.Finite.Coefficient.FiniteCoefficientUnitInsertion

/-! The ordinary single model of the normalized ordered derived root transition.

Source: smooth-purity transport, normalized Tate tower, Step 4.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Etale.FiniteSmoothPurity
namespace AlgebraicGeometry.Scheme.PurityIntegralTower

private theorem zero_shift_inverse
    {C D : Type*} [Category C] [Category D] [HasShift C ℤ] [HasShift D ℤ]
    (F : C ⥤ D) [F.CommShift ℤ] {U : C} {V : D} (l : F.obj U ⟶ V) :
    F.map ((shiftFunctorZero C ℤ).inv.app U) ≫
        (F.commShiftIso 0).hom.app U ≫ (shiftFunctor D 0).map l =
      l ≫ (shiftFunctorZero D ℤ).inv.app V := by
  apply (cancel_mono ((shiftFunctorZero D ℤ).hom.app V)).1
  simp only [Category.assoc, Iso.inv_hom_id_app]
  rw [zero_shift_map]
  rw [← F.map_comp_assoc, Iso.inv_hom_id_app, F.map_id, Category.id_comp]
  exact (Category.comp_id l).symm

private theorem lax_tensor_unit
    {C D : Type*} [Category C] [Category D]
    [MonoidalCategory C] [MonoidalCategory D]
    (R : C ⥤ D) [R.LaxMonoidal] {X : C} {Y : D} (f : Y ⟶ R.obj X) :
    (Functor.LaxMonoidal.ε R ⊗ₘ f) ≫ Functor.LaxMonoidal.μ R (𝟙_ C) X ≫
        R.map (λ_ X).hom = (λ_ Y).hom ≫ f := by
  rw [Functor.LaxMonoidal.ε_tensorHom_comp_μ_assoc]
  simp only [← R.map_comp, Iso.inv_hom_id, R.map_id, Category.comp_id]
  exact leftUnitor_naturality f

private theorem tensor_slide
    {C D E : Type*} [Category C] [Category D] [Category E]
    (F : C ⥤ D ⥤ E) {X Y Z : C} {P Q : D}
    (f : X ⟶ Y) (g : Y ⟶ Z) (h : P ⟶ Q) :
    (F.map f).app P ≫ (F.obj Y).map h ≫ (F.map g).app Q =
      (F.map (f ≫ g)).app P ≫ (F.obj Z).map h := by
  rw [(F.map g).naturality]
  simp only [Functor.map_comp, NatTrans.comp_app, Category.assoc]

private theorem tensor_naturality_first
    {C D : Type*} [Category C] [Category D]
    (F : C ⥤ C ⥤ C) (G : D ⥤ D ⥤ D) (H : C ⥤ D)
    (δ : Functor.uncurry.obj F ⋙ H ⟶ H.prod H ⋙ Functor.uncurry.obj G)
    {K K' : C} (f : K ⟶ K') (L : C) :
    H.map ((F.map f).app L) ≫ δ.app (K', L) =
      δ.app (K, L) ≫ (G.map (H.map f)).app (H.obj L) := by
  have h := δ.naturality (show (K, L) ⟶ (K', L) from (f, 𝟙 L))
  dsimp only [Functor.comp_map, Functor.prod_map, Functor.prod_obj,
    Functor.uncurry_obj_map] at h
  rw [(F.obj K').map_id L, Category.comp_id, H.map_id L,
    (G.obj (H.obj K')).map_id (H.obj L), Category.comp_id] at h
  exact h

private theorem insertion_naturality
    {V W : Type*} [Category V] [Category W] [Abelian V] [Abelian W]
    [HasDerivedCategory V] [HasDerivedCategory W]
    (R : W ⥤ V) [R.Additive] [PreservesFiniteLimits R] [PreservesFiniteColimits R]
    {L : DerivedCategory V ⥤ DerivedCategory W} (a : L ⊣ R.mapDerivedCategory)
    {F F' : V} {G G' : W} (f : F ⟶ F') (g : G ⟶ G')
    (η : F ⟶ R.obj G) (η' : F' ⟶ R.obj G')
    (h : η ≫ R.map g = f ≫ η') :
    SheafExactDegreeZero.adjointInsertion R a η ≫
        (DerivedCategory.singleFunctor W 0).map g =
      L.map ((DerivedCategory.singleFunctor V 0).map f) ≫
        SheafExactDegreeZero.adjointInsertion R a η' := by
  unfold SheafExactDegreeZero.adjointInsertion
  rw [← a.homEquiv_naturality_right_symm, ← a.homEquiv_naturality_left_symm]
  congr 1
  have hn := (R.mapDerivedCategorySingleFunctor 0).inv.naturality g
  dsimp only [Functor.comp_map] at hn
  rw [Category.assoc, ← hn]
  simpa only [Functor.map_comp, Category.assoc] using congrArg
    (fun k ↦ (DerivedCategory.singleFunctor V 0).map k ≫
      (R.mapDerivedCategorySingleFunctor 0).inv.app G') h

private theorem ordinary_product
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    {φ : A →+* B} {N M : ℕ} {hA : (N : A) = 0} {hB : (M : B) = 0}
    {T : Scheme.{u}} (r : CoefficientLineComparison φ N M hA hB T)
    (hN : 0 < N) (hM : 0 < M)
    (hNT : IsUnit (N : Γ(T, ⊤))) (hMT : IsUnit (M : Γ(T, ⊤))) (d : ℕ) :
    (finiteTateEtaleTransition r d ⊗ₘ finiteTateEtaleTransition r 1) ≫
        Functor.LaxMonoidal.μ (Sheaf.restrictScalars T.smallEtaleTopology φ) _ _ ≫
        (Sheaf.restrictScalars T.smallEtaleTopology φ).map
          (((Scheme.finiteEtaleTwistPullbackData B M hM hB).p T hMT d 1 ≪≫
            eqToIso (congrArg (Scheme.finiteEtaleTateSheaf B M T hB)
              (Int.natCast_add d 1).symm)).hom) =
      ((Scheme.finiteEtaleTwistPullbackData A N hN hA).p T hNT d 1 ≪≫
        eqToIso (congrArg (Scheme.finiteEtaleTateSheaf A N T hA)
          (Int.natCast_add d 1).symm)).hom ≫ finiteTateEtaleTransition r (d + 1) := by
  have ha0 := (Scheme.finiteEtaleTwistPullbackData A N hN hA).laws.2.2.2.2.2.2.2.2.1
  have hb0 := (Scheme.finiteEtaleTwistPullbackData B M hM hB).laws.2.2.2.2.2.2.2.2.1
  have hap := (Scheme.finiteEtaleTwistPullbackData A N hN hA).laws.2.2.2.2.2.2.2.2.2.2.1
  have hbp := (Scheme.finiteEtaleTwistPullbackData B M hM hB).laws.2.2.2.2.2.2.2.2.2.2.1
  cases d with
  | zero =>
    simp only [Int.natCast_zero, ha0, hb0, Iso.trans_hom, eqToIso.hom,
      eqToHom_refl, Category.comp_id, finiteTateEtaleTransition]
    unfold finiteTateEtaleTransition
    exact lax_tensor_unit (Sheaf.restrictScalars T.smallEtaleTopology φ)
      ((ProEtale.etaleSheafExtendScalarsAdjunction φ T).homEquiv _ _ r.sheafIso.hom)
  | succ d =>
    have ha := hap T hNT d
    have hb := hbp T hMT d
    simp only [Int.ofNat_eq_natCast] at ha hb
    rw [ha, hb]
    simp only [Int.natCast_add, Int.natCast_one, Iso.refl_hom,
      Iso.trans_hom, eqToIso.hom, eqToHom_refl,
      Category.id_comp, Category.comp_id, finiteTateEtaleTransition]
    erw [(Sheaf.restrictScalars T.smallEtaleTopology φ).map_id, Category.comp_id]
    rfl

-- Degree-zero tensor insertion, proved from the current representative normalization.

/-- Regrouping the ordered shifted root comparison is the shifted adjunction
insertion of its ordinary semilinear tensor map. This statement is entirely on
the small etale site, before comparison inverse image or coefficient realization.

Source: smooth-purity transport, normalized Tate tower, Step 1, tensor induction.
(blueprint: lem-pur-tate-tensor-derived-ordinary-normalization).

Proof: use the scalar unit insertion and the CommShift zero axiom at zero.
The ordinary product square follows from the lax restriction unit law at zero
and from the recursive ordinary transition and positive product normalization
in positive degrees. Adjoint insertion is natural in source and target by the
adjunction hom equivalence and the exact-single comparison. The scalar tensor
and shift coherence and tensor-shift naturality give a shifted insertion formula.
For its degree-zero tensor identity, factor the flat single comparisons through
Q and the cochain single tensor isomorphism. Apply the all-complex scalar tensor
normalization. On the sole nonzero tensor summand, the cochain comparison is the
ordinary scalar oplax tensorator. Representative naturality and the scalar-single
adjunct formula turn this into insertion; the ordinary monoidal adjunction
identifies its adjunct with the restriction lax tensorator following the tensor
of the two semilinear maps. Expand the successor clauses,
use bifunctor naturality, the induction hypothesis and the normalized root map,
and then apply that formula at shifts 2d and 2. Insertion naturality for the
ordinary product square and scalar-shift naturality give the required next
regrouping; the integer shift casts cancel by 2d + 2 = 2(d + 1). -/
theorem finiteTateEtaleTransition_derived
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    {phi : A →+* B} {N M : ℕ} {hA : (N : A) = 0} {hB : (M : B) = 0}
    {T : Scheme.{u}} (r : CoefficientLineComparison phi N M hA hB T)
    (hN : 0 < N) (hM : 0 < M)
    (hNT : IsUnit (N : Γ(T, ⊤))) (hMT : IsUnit (M : Γ(T, ⊤))) (d : ℕ) :
    (r.tensorPower d).hom ≫
        (Etale.CoordinateCounitArrows.baseTateIso B M hM hB T hMT d).hom =
      (ordinaryScalar phi T).map
          (Etale.CoordinateCounitArrows.baseTateIso A N hN hA T hNT d).hom ≫
        (scalarShiftIso phi T (2 * (d : ℤ))).hom.app _ ≫
        (shiftFunctor _ (2 * (d : ℤ))).map
          (SheafExactDegreeZero.scalarAdjointInsertion T.smallEtaleTopology phi
            (finiteTateEtaleTransition r d)) := by
  induction d with
  | zero =>
    let : (ordinaryScalar phi T).CommShift ℤ :=
      (Adjunction.ofIsRightAdjoint
        (Sheaf.derivedRestrictScalars T.smallEtaleTopology phi)).leftAdjointCommShift ℤ
    have hA0 : (Etale.CoordinateCounitArrows.baseTateIso A N hN hA T hNT 0).hom =
        (shiftFunctorZero _ ℤ).inv.app
          ((DerivedCategory.singleFunctor
            (Sheaf T.smallEtaleTopology (ModuleCat A)) 0).obj (𝟙_ _)) := by
      unfold Etale.CoordinateCounitArrows.baseTateIso
      rfl
    have hB0 : (Etale.CoordinateCounitArrows.baseTateIso B M hM hB T hMT 0).hom =
        (shiftFunctorZero _ ℤ).inv.app
          ((DerivedCategory.singleFunctor
            (Sheaf T.smallEtaleTopology (ModuleCat B)) 0).obj (𝟙_ _)) := by
      unfold Etale.CoordinateCounitArrows.baseTateIso
      rfl
    have hu : (r.tensorPower 0).hom =
        SheafExactDegreeZero.scalarAdjointInsertion T.smallEtaleTopology phi
          (Functor.LaxMonoidal.ε (Sheaf.restrictScalars T.smallEtaleTopology phi)) := by
      change (scalarZeroLineIso phi N M hA hB T).hom = _
      exact (ProEtale.ordinaryScalarUnitSandwich phi T).trans
        (WeilConjectures.finiteCoefficient_unit_eq_scalarInsertion phi T)
    rw [hA0, hB0, hu]
    unfold finiteTateEtaleTransition
    dsimp only [scalarShiftIso]
    exact (zero_shift_inverse (ordinaryScalar phi T)
      (SheafExactDegreeZero.scalarAdjointInsertion T.smallEtaleTopology phi
        (Functor.LaxMonoidal.ε (Sheaf.restrictScalars T.smallEtaleTopology phi)))).symm
  | succ d ih =>
    have hAstep :
        Etale.CoordinateCounitArrows.baseTateIso A N hN hA T hNT (d + 1) =
          Etale.CoordinateCounitArrows.baseTateStep A N hN hA T hNT d
            (Etale.CoordinateCounitArrows.baseTateIso A N hN hA T hNT d) := by
      unfold Etale.CoordinateCounitArrows.baseTateIso
      rfl
    have hBstep :
        Etale.CoordinateCounitArrows.baseTateIso B M hM hB T hMT (d + 1) =
          Etale.CoordinateCounitArrows.baseTateStep B M hM hB T hMT d
            (Etale.CoordinateCounitArrows.baseTateIso B M hM hB T hMT d) := by
      unfold Etale.CoordinateCounitArrows.baseTateIso
      rfl
    have hr : r.tensorPower (d + 1) = r.tensorPowerStep d (r.tensorPower d) := rfl
    let pA := (Scheme.finiteEtaleTwistPullbackData A N hN hA).p T hNT d 1 ≪≫
      eqToIso (congrArg (Scheme.finiteEtaleTateSheaf A N T hA)
        (Int.natCast_add d 1).symm)
    let pB := (Scheme.finiteEtaleTwistPullbackData B M hM hB).p T hMT d 1 ≪≫
      eqToIso (congrArg (Scheme.finiteEtaleTateSheaf B M T hB)
        (Int.natCast_add d 1).symm)
    have hi := insertion_naturality
      (Sheaf.restrictScalars T.smallEtaleTopology phi)
      (Adjunction.ofIsRightAdjoint
        (Sheaf.derivedRestrictScalars T.smallEtaleTopology phi))
      pA.hom pB.hom
      ((finiteTateEtaleTransition r d ⊗ₘ finiteTateEtaleTransition r 1) ≫
        Functor.LaxMonoidal.μ (Sheaf.restrictScalars T.smallEtaleTopology phi) _ _)
      (finiteTateEtaleTransition r (d + 1))
      (ordinary_product r hN hM hNT hMT d)
    have ht := shifted_tensor_insertion phi T
      (finiteEtaleTateTwist T N A hA d) (finiteEtaleTateLine T N A hA)
      (finiteEtaleTateTwist T M B hB d) (finiteEtaleTateLine T M B hB)
      (Etale.CoordinateCounitArrows.tateFlat A N hN hA T hNT d)
      (Etale.CoordinateCounitArrows.tateFlat A N hN hA T hNT 1)
      (Etale.CoordinateCounitArrows.tateFlat B M hM hB T hMT d)
      (Etale.CoordinateCounitArrows.tateFlat B M hM hB T hMT 1)
      (finiteTateEtaleTransition r d) (finiteTateEtaleTransition r 1) (2 * (d : ℤ)) 2
    have hn := tensor_naturality_first
      (Etale.derivedTensor (ModuleCat.{u + 1} A) T)
      (Etale.derivedTensor (ModuleCat.{u + 1} B) T) (Etale.scalarExtension phi T)
      (Etale.ExceptionalCoefficients.tensorIso phi T).hom
      (Etale.CoordinateCounitArrows.baseTateIso A N hN hA T hNT d).hom
      ((Etale.ordinaryFiniteLine A N hA T)⟦(2 : ℤ)⟧)
    have hroot : r.derivedIso.hom =
        SheafExactDegreeZero.scalarAdjointInsertion T.smallEtaleTopology phi
          (finiteTateEtaleTransition r 1) := by
      simpa only [finiteTateEtaleTransition, finiteEtaleTateTwist] using
        r.derived_eq_scalarInsertion
    let v := (scalarShiftIso phi T 2).hom.app (Etale.ordinaryFiniteLine A N hA T) ≫
      (shiftFunctor _ (2 : ℤ)).map
        (SheafExactDegreeZero.scalarAdjointInsertion T.smallEtaleTopology phi
          (finiteTateEtaleTransition r 1))
    have hm := tensor_slide (Etale.derivedTensor (ModuleCat.{u + 1} B) T)
      (r.tensorPower d).hom
      (Etale.CoordinateCounitArrows.baseTateIso B M hM hB T hMT d).hom v
    change _ = Etale.derivedTensorHom (ModuleCat.{u + 1} B)
      ((r.tensorPower d).hom ≫
        (Etale.CoordinateCounitArrows.baseTateIso B M hM hB T hMT d).hom) v at hm
    have hf : Etale.derivedTensorHom (ModuleCat.{u + 1} B)
        ((ordinaryScalar phi T).map
            (Etale.CoordinateCounitArrows.baseTateIso A N hN hA T hNT d).hom ≫
          (scalarShiftIso phi T (2 * (d : ℤ))).hom.app _ ≫
          (shiftFunctor _ (2 * (d : ℤ))).map
            (SheafExactDegreeZero.scalarAdjointInsertion T.smallEtaleTopology phi
              (finiteTateEtaleTransition r d))) v =
        ((Etale.derivedTensor (ModuleCat.{u + 1} B) T).map
          ((ordinaryScalar phi T).map
            (Etale.CoordinateCounitArrows.baseTateIso A N hN hA T hNT d).hom)).app _ ≫
        Etale.derivedTensorHom (ModuleCat.{u + 1} B)
          ((scalarShiftIso phi T (2 * (d : ℤ))).hom.app _ ≫
            (shiftFunctor _ (2 * (d : ℤ))).map
              (SheafExactDegreeZero.scalarAdjointInsertion T.smallEtaleTopology phi
                (finiteTateEtaleTransition r d))) v := by
      simp only [Etale.derivedTensorHom, Functor.map_comp, NatTrans.comp_app, Category.assoc]
    have hi :
        SheafExactDegreeZero.scalarAdjointInsertion T.smallEtaleTopology phi
            ((finiteTateEtaleTransition r d ⊗ₘ finiteTateEtaleTransition r 1) ≫
              Functor.LaxMonoidal.μ (Sheaf.restrictScalars T.smallEtaleTopology phi) _ _) ≫
            (DerivedCategory.singleFunctor _ 0).map pB.hom =
          (ordinaryScalar phi T).map ((DerivedCategory.singleFunctor _ 0).map pA.hom) ≫
            SheafExactDegreeZero.scalarAdjointInsertion T.smallEtaleTopology phi
              (finiteTateEtaleTransition r (d + 1)) := by
      unfold SheafExactDegreeZero.scalarAdjointInsertion
      exact hi
    simp only [pA, pB, Iso.trans_hom, eqToIso.hom,
      Int.natCast_add, Int.natCast_one, eqToHom_refl, Category.comp_id] at hi
    dsimp only [ordinaryScalar, line, Etale.ordinaryFiniteDegreeZero,
      Etale.SectionLocalDualizingComparisons.tateObject] at *
    rw [hAstep, hBstep, hr]
    unfold CoefficientLineComparison.tensorPowerStep Etale.CoordinateCounitArrows.baseTateStep
    simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom, Functor.map_comp,
      Category.assoc, Int.natCast_add, Int.natCast_one,
      eqToIso_refl, Iso.refl_hom, NatTrans.id_app, Category.comp_id]
    dsimp only [ordinaryScalar, line, Etale.ordinaryFiniteLine,
      Etale.ordinaryFiniteDegreeZero, Etale.SectionLocalDualizingComparisons.tateObject,
      Functor.prod_obj] at *
    rw [hroot]
    simp only [Etale.derivedTensorRight, Functor.flip_obj_map]
    rw [← Functor.map_comp_assoc]
    erw [reassoc_of% hm]
    rw [ih, hf]
    try simp only [Category.assoc]
    erw [← reassoc_of% hn]
    erw [reassoc_of% ht]
    try simp only [Category.assoc]
    rw [← (shiftFunctor (Etale.DerivedCategoryModule B T) (2 * (d : ℤ) + 2)).map_comp]
    erw [hi]
    rw [(shiftFunctor (Etale.DerivedCategoryModule B T) (2 * (d : ℤ) + 2)).map_comp]
    try simp only [Category.assoc]
    have hs := (scalarShiftIso phi T (2 * (d : ℤ) + 2)).hom.naturality
      ((DerivedCategory.singleFunctor _ 0).map pA.hom)
    dsimp only [Functor.comp_map, ordinaryScalar] at hs
    simp only [pA, Iso.trans_hom, eqToIso.hom,
      Int.natCast_add, Int.natCast_one, eqToHom_refl, Category.comp_id] at hs
    erw [← reassoc_of% hs]
    set_option maxRecDepth 8192 in rfl

end AlgebraicGeometry.Scheme.PurityIntegralTower
