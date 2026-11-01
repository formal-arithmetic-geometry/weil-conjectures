/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Etale.Brown.EtaleBrownProjectionRealization
public import WeilConjectures.AlgebraicGeometry.Proper.Open.ProperOpenCoefficientRefinement
public import Mathlib.CategoryTheory.Adjunction.Mates
public import WeilConjectures.Algebra.Homology.Coefficient.CoefficientSystemUnboundedComparison
public import WeilConjectures.AlgebraicGeometry.Etale.ProEtale.EtaleProEtaleScalarMateData
public import WeilConjectures.AlgebraicGeometry.EtaleBrownOrdinaryRightScalarCube
public import WeilConjectures.AlgebraicGeometry.EtaleRestrictScalarsAdjunctionIdentities
public import WeilConjectures.AlgebraicGeometry.Scalar.ScalarPullbackRepresentativeData
public import WeilConjectures.AlgebraicGeometry.Strict.Etale.StrictEtaleInverseTensorCoherence
public import WeilConjectures.CategoryTheory.Derived.DerivedAdjunctionCochainUnit
public import WeilConjectures.CategoryTheory.Derived.DerivedSquareIndependentUniverses

/-! # Open scalar transport decomposition

Source: Zheng, Construction 4.1, Constructions 5.14--5.15 and Lemma 5.16;
Stacks 03CY, 06YY and 07A4.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genCtorIdx false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite SheafOfModules
namespace AlgebraicGeometry
attribute [local instance 5000] strictEtaleSystemDerived strictEtaleLevelDerived
attribute [local instance] CoefficientSystemOrdinaryImage.inverseAdditive
  CoefficientSystemOrdinaryImage.rightAdditive
  CoefficientSystemOrdinaryImage.systemInverseAdditive
  CoefficientSystemOrdinaryImage.systemRightAdditive

private theorem mate_comparison_of_units
    (a₁ : L₁ ⊣ R₁) (a₂ : L₂ ⊣ R₂) (ad₁ : LD₁ ⊣ RD₁) (ad₂ : LD₂ ⊣ RD₂)
    (ε₁ : QA ⋙ LD₁ ⟶ L₁ ⋙ QB) (ε₂ : QC ⋙ LD₂ ⟶ L₂ ⋙ QD)
    (β₁ : R₁ ⋙ QA ⟶ QB ⋙ RD₁) (β₂ : R₂ ⋙ QC ⟶ QD ⋙ RD₂)
    (γ : QA ⋙ GD ≅ G ⋙ QC) (η : QB ⋙ HD ≅ H ⋙ QD)
    (h₁ : ∀ P K (f : L₁.obj P ⟶ K),
      ad₁.homEquiv _ _ (ε₁.app P ≫ QB.map f) =
        QA.map (a₁.homEquiv _ _ f) ≫ β₁.app K)
    (h₂ : ∀ P K (f : L₂.obj P ⟶ K),
      ad₂.homEquiv _ _ (ε₂.app P ≫ QD.map f) =
        QC.map (a₂.homEquiv _ _ f) ≫ β₂.app K)
    (τ : TwoSquare R₁ H G R₂) (τD : TwoSquare RD₁ HD GD RD₂)
    (hτ : ∀ K,
      GD.map (β₁.app K) ≫ τD.natTrans.app (QB.obj K) ≫ RD₂.map (η.hom.app K) =
        γ.hom.app (R₁.obj K) ≫ QC.map (τ.natTrans.app K) ≫ β₂.app (H.obj K))
    (ι : G ⋙ L₂ ⟶ L₁ ⋙ H)
    (hι : ∀ P, a₂.homEquiv _ _ (ι.app P) =
      G.map (a₁.unit.app P) ≫ τ.natTrans.app (L₁.obj P)) (P : AA) :
    ((mateEquiv ad₁ ad₂).symm τD).app (QA.obj P) ≫
        HD.map (ε₁.app P) ≫ η.hom.app (L₁.obj P) =
      LD₂.map (γ.hom.app P) ≫ ε₂.app (G.obj P) ≫ QD.map (ι.app P) := by
  apply (ad₂.homEquiv _ _).injective
  rw [← Category.assoc, ad₂.homEquiv_naturality_right, adjunctionMate_transpose]
  have he : ad₁.homEquiv _ _ (ε₁.app P) =
      QA.map (a₁.unit.app P) ≫ β₁.app (L₁.obj P) := by
    have hh := h₁ P (L₁.obj P) (𝟙 _)
    erw [QB.map_id, Category.comp_id, a₁.homEquiv_unit, R₁.map_id,
      Category.comp_id] at hh
    exact hh
  rw [he, GD.map_comp]
  simp only [Functor.comp_obj, Category.assoc]
  rw [hτ]
  change GD.map (QA.map (a₁.unit.app P)) ≫ γ.hom.app (R₁.obj (L₁.obj P)) ≫
    QC.map (τ.natTrans.app (L₁.obj P)) ≫ β₂.app (H.obj (L₁.obj P)) = _
  rw [← Functor.comp_map]
  erw [γ.hom.naturality_assoc]
  rw [ad₂.homEquiv_naturality_left]
  erw [h₂, hι, QC.map_comp]
  simp only [Category.assoc, Functor.comp_map, Functor.id_obj]

private theorem exact_left_transpose
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    [Abelian.HasKInjectiveResolutions D]
    {F : C ⥤ D} {G : D ⥤ C} [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (a : F ⊣ G) (P : CochainComplex C ℤ) (I : CochainComplex D ℤ)
    (f : (F.mapHomologicalComplex (.up ℤ)).obj P ⟶ I) :
    a.mapDerivedCategoryRightDerivedAdjunction.homEquiv _ _
        (F.mapDerivedCategoryFactors.hom.app P ≫ DerivedCategory.Q.map f) =
      DerivedCategory.Q.map ((a.mapHomologicalComplex (.up ℤ)).homEquiv _ _ f) ≫
        G.rightDerivedFunctorUnitQ I := by
  rw [Adjunction.homEquiv_unit, G.rightDerivedFunctor.map_comp, ← Category.assoc,
    derived_unit_cochain, Category.assoc, ← G.rightDerivedFunctorUnitQ_naturality]
  rw [← DerivedCategory.Q.map_comp_assoc, Adjunction.homEquiv_unit]

private theorem inverse_representative_of_right
    (O : Type (u + 1)) [CommRing O] (t : O)
    {V W : Scheme.{u}} (g : V ⟶ W) (n : ℕ)
    (A : StrictEtaleOrdinaryImage O t g)
    (B : CoefficientDerivedImage (A.lift n).modules (A.right n) (A.levelAdj n))
    {PV : StrictEtaleEvaluation V O t} {PW : StrictEtaleEvaluation W O t}
    (RV : StrictEtaleBrownRealization O t V PV)
    (RW : StrictEtaleBrownRealization O t W PW)
    (r : StrictEtaleBrownImageRealization O t g n A B RV RW) :
    let := RV.val.ordinaryAdditive
    let := RW.val.ordinaryAdditive
    ∀ K : CochainComplex (strictEtaleLevel W O t n) ℤ,
      (r.inverse).hom.app (DerivedCategory.Q.obj K) ≫
          (RV.derived n).map (B.inverseFactors.hom.app K) ≫
          (RV.factors n).hom.app
            (((A.lift n).modules.mapHomologicalComplex (.up ℤ)).obj K) =
        (Etale.upperStar (ModuleCat.{u + 1} (strictEtaleBrownRing O t n))
          g).mapDerivedCategory.map ((RW.factors n).hom.app K) ≫
          (Etale.upperStar (ModuleCat.{u + 1} (strictEtaleBrownRing O t n))
            g).mapDerivedCategoryFactors.hom.app
            (((strictEtaleBrownConstant O t W n).mapHomologicalComplex (.up ℤ)).obj K) ≫
          DerivedCategory.Q.map
            ((NatTrans.mapHomologicalComplex
              (((mateEquiv (A.levelAdj n) (Etale.upperStarLowerStarAdjunction
                (ModuleCat.{u + 1} (strictEtaleBrownRing O t n)) g)).symm
                (.mk _ _ _ _ r.val.ordinaryRight.hom)).natTrans) (.up ℤ)).app K) := by
  let := RV.val.ordinaryAdditive
  let := RW.val.ordinaryAdditive
  dsimp only
  intro K
  have hr : ((mateEquiv B.adjunction
      (Etale.upperStarLowerStarAdjunction
        (ModuleCat.{u + 1} (strictEtaleBrownRing O t n)) g
          ).mapDerivedCategoryRightDerivedAdjunction).symm
      (.mk _ _ _ _ r.right.hom)).natTrans = r.inverse.hom := by
    rw [← r.property.2.2]
    exact congrArg TwoSquare.natTrans (Equiv.symm_apply_apply _ _)
  rw [← hr]
  apply mate_comparison_of_units
    ((A.levelAdj n).mapHomologicalComplex (.up ℤ))
    ((Etale.upperStarLowerStarAdjunction
      (ModuleCat.{u + 1} (strictEtaleBrownRing O t n)) g).mapHomologicalComplex (.up ℤ))
    B.adjunction (Etale.upperStarLowerStarAdjunction
      (ModuleCat.{u + 1} (strictEtaleBrownRing O t n)) g
        ).mapDerivedCategoryRightDerivedAdjunction
    B.inverseFactors.hom
    (Etale.upperStar (ModuleCat.{u + 1} (strictEtaleBrownRing O t n))
      g).mapDerivedCategoryFactors.hom B.directUnit
    { app := fun I ↦ strictEtaleBrownRightUnit O t g n I
      naturality := fun _ _ f ↦
        (Etale.lowerStar (ModuleCat.{u + 1} (strictEtaleBrownRing O t n))
          g).rightDerivedFunctorUnitQ_naturality f }
    (RW.factors n) (RV.factors n) B.transpose
    (exact_left_transpose (Etale.upperStarLowerStarAdjunction
      (ModuleCat.{u + 1} (strictEtaleBrownRing O t n)) g))
    (.mk _ _ _ _ (r.val.ordinaryRight.hom.mapHomologicalComplex (.up ℤ)))
    (.mk _ _ _ _ r.right.hom) r.property.2.1
    (NatTrans.mapHomologicalComplex
      (((mateEquiv (A.levelAdj n) (Etale.upperStarLowerStarAdjunction
        (ModuleCat.{u + 1} (strictEtaleBrownRing O t n)) g)).symm
        (.mk _ _ _ _ r.val.ordinaryRight.hom)).natTrans) (.up ℤ))
    (by
      intro P
      rw [Adjunction.homEquiv_unit]
      ext i : 1
      exact (unit_mateEquiv_symm (A.levelAdj n)
        (Etale.upperStarLowerStarAdjunction
          (ModuleCat.{u + 1} (strictEtaleBrownRing O t n)) g)
        (.mk _ _ _ _ r.val.ordinaryRight.hom) (P.X i)).symm) K

private theorem mate_whisker_top
    {C D E F : Type*} [Category C] [Category D] [Category E] [Category F]
    {G G' : C ⥤ E} {H : D ⥤ F}
    {L₁ : C ⥤ D} {R₁ : D ⥤ C} {L₂ : E ⥤ F} {R₂ : F ⥤ E}
    (a₁ : L₁ ⊣ R₁) (a₂ : L₂ ⊣ R₂) (w : TwoSquare G' L₁ L₂ H) (t : G ⟶ G') :
    mateEquiv a₁ a₂ (w.whiskerTop t) = (mateEquiv a₁ a₂ w).whiskerRight t := by
  simpa [TwoSquare.whiskerBottom, TwoSquare.whiskerLeft] using
    mateEquiv_whiskerTop_whiskerBottom a₁ a₂ w t (𝟙 H)

private theorem inverse_mate_cube
    {CA DA CB DB EA FA EB FB : Type*}
    [Category CA] [Category DA] [Category CB] [Category DB]
    [Category EA] [Category FA] [Category EB] [Category FB]
    {LA : CA ⥤ DA} {RA : DA ⥤ CA} {LB : CB ⥤ DB} {RB : DB ⥤ CB}
    {LA' : EA ⥤ FA} {RA' : FA ⥤ EA} {LB' : EB ⥤ FB} {RB' : FB ⥤ EB}
    (aA : LA ⊣ RA) (aB : LB ⊣ RB) (bA : LA' ⊣ RA') (bB : LB' ⊣ RB')
    {U : CB ⥤ CA} {V : DB ⥤ DA} {U' : EB ⥤ EA} {V' : FB ⥤ FA}
    {GA : CA ⥤ EA} {HA : DA ⥤ FA} {GB : CB ⥤ EB} {HB : DB ⥤ FB}
    (aa : TwoSquare RA HA GA RA') (ab : TwoSquare RB HB GB RB')
    (k : TwoSquare U LB LA V) (i : TwoSquare U' LB' LA' V')
    (t : U ⋙ GA ⟶ GB ⋙ U') (s : V ⋙ HA ⟶ HB ⋙ V')
    (h : ∀ M : DB,
      t.app (RB.obj M) ≫ U'.map (ab.app M) ≫
          (mateEquiv bB bA i).app (HB.obj M) =
        GA.map ((mateEquiv aB aA k).app M) ≫
          aa.app (V.obj M) ≫ RA'.map (s.app M))
    (N : CB) :
    LA'.map (t.app N) ≫ i.app (GB.obj N) ≫
        V'.map (((mateEquiv aB bB).symm ab).app N) =
      ((mateEquiv aA bA).symm aa).app (U.obj N) ≫
        HA.map (k.app N) ≫ s.app (LB.obj N) := by
  have hc : (((mateEquiv aB bB).symm ab).hComp i).whiskerTop t =
      (k.hComp ((mateEquiv aA bA).symm aa)).whiskerBottom s := by
    apply (mateEquiv aB bA).injective
    rw [mate_whisker_top, mateEquiv_whiskerBottom,
      mateEquiv_vcomp aB bB bA, mateEquiv_vcomp aB aA bA,
      Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    ext M
    simpa only [TwoSquare.vComp, TwoSquare.whiskerRight, TwoSquare.whiskerLeft,
      NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Functor.associator_hom_app, Functor.associator_inv_app,
      Category.id_comp, Category.comp_id, Category.assoc] using h M
  simpa only [TwoSquare.hComp, TwoSquare.whiskerTop, TwoSquare.whiskerBottom,
    NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Category.id_comp, Category.comp_id, Category.assoc] using
    congrArg (fun w ↦ w.natTrans.app N) hc

private abbrev ordinary_inverse
    (O : Type (u + 1)) [CommRing O] (t : O)
    {V W : Scheme.{u}} (g : V ⟶ W) (A : StrictEtaleOrdinaryImage O t g) (n : ℕ)
    (q : A.right n ⋙ strictEtaleBrownConstant O t W n ≅
      strictEtaleBrownConstant O t V n ⋙
        Etale.lowerStar (ModuleCat.{u + 1} (strictEtaleBrownRing O t n)) g) :=
  ((mateEquiv (A.levelAdj n) (Etale.upperStarLowerStarAdjunction
    (ModuleCat.{u + 1} (strictEtaleBrownRing O t n)) g)).symm
      (.mk _ _ _ _ q.hom)).natTrans

private theorem ordinary_inverse_restriction_cube
    (O : Type (u + 1)) [CommRing O] (t : O)
    {V W : Scheme.{u}} (g : V ⟶ W) (A : StrictEtaleOrdinaryImage O t g)
    {PV : StrictEtaleEvaluation V O t} {PW : StrictEtaleEvaluation W O t}
    (RV : StrictEtaleBrownRealization O t V PV)
    (RW : StrictEtaleBrownRealization O t W PW)
    (q : ∀ n, A.right n ⋙ strictEtaleBrownConstant O t W n ≅
      strictEtaleBrownConstant O t V n ⋙
        Etale.lowerStar (ModuleCat.{u + 1} (strictEtaleBrownRing O t n)) g)
    (hq : ∀ n (M : strictEtaleLevel V O t n) (U : W.Etaleᵒᵖ)
      (x : ((A.right n).obj M).val.obj U),
      ((q n).hom.app M).hom.app U x =
        ((A.rightUnderlying n).hom.app M).hom.app U x)
    {m n : ℕ} (h : m ≤ n) (M : strictEtaleLevel W O t m) :
    (Etale.upperStar (ModuleCat.{u + 1} (strictEtaleBrownRing O t n)) g).map
        ((RW.val.ordinaryRestriction h).hom.app M) ≫
      (Etale.upperStarRestrictScalarsIsoSheaf (strictEtaleBrownRingMap O t h) g).hom.app
        ((strictEtaleBrownConstant O t W m).obj M) ≫
      (Sheaf.restrictScalars V.smallEtaleTopology (strictEtaleBrownRingMap O t h)).map
        ((ordinary_inverse O t g A m (q m)).app M) =
    (ordinary_inverse O t g A n (q n)).app
        ((coefficientRestriction (J := W.smallEtaleTopology) O t h).obj M) ≫
      (strictEtaleBrownConstant O t V n).map ((A.restrictInverse h).hom.app M) ≫
      (RV.val.ordinaryRestriction h).hom.app ((A.lift m).modules.obj M) := by
  apply inverse_mate_cube (A.levelAdj n) (A.levelAdj m)
    (Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} (strictEtaleBrownRing O t n)) g)
    (Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} (strictEtaleBrownRing O t m)) g)
    (U := coefficientRestriction (J := W.smallEtaleTopology) O t h)
    (V := coefficientRestriction (J := V.smallEtaleTopology) O t h)
    (U' := Sheaf.restrictScalars W.smallEtaleTopology (strictEtaleBrownRingMap O t h))
    (V' := Sheaf.restrictScalars V.smallEtaleTopology (strictEtaleBrownRingMap O t h))
    (GA := strictEtaleBrownConstant O t W n) (HA := strictEtaleBrownConstant O t V n)
    (GB := strictEtaleBrownConstant O t W m) (HB := strictEtaleBrownConstant O t V m)
    (.mk _ _ _ _ (q n).hom) (.mk _ _ _ _ (q m).hom)
    (.mk _ _ _ _ (A.restrictInverse h).hom)
    (.mk _ _ _ _
      (Etale.upperStarRestrictScalarsIsoSheaf (strictEtaleBrownRingMap O t h) g).hom)
    (RW.val.ordinaryRestriction h).hom (RV.val.ordinaryRestriction h).hom ?_ M
  intro N
  have hf := Etale.underived_mate (strictEtaleBrownRingMap O t h) g
  rw [show (mateEquiv
      (Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} (strictEtaleBrownRing O t m)) g)
      (Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} (strictEtaleBrownRing O t n)) g)
      (.mk _ _ _ _
        (Etale.upperStarRestrictScalarsIsoSheaf (strictEtaleBrownRingMap O t h) g).hom)).app
          ((strictEtaleBrownConstant O t V m).obj N) = 𝟙 _ from congr_app hf _]
  erw [Category.comp_id]
  exact etaleBrownOrdinaryRightScalar_cube O t g A RV RW q hq h N

private theorem normalized_cube (X₀ : DerivedCategory C) :
    cD.map (s1.app X₀) ≫ s2.app (dD.obj X₀) ≫ gD.map (s3.app X₀) =
      s4.app (aD.obj X₀) ≫ kD.map (s5.app X₀) ≫ s6.app (hD.obj X₀) := by
  have hc :
      whiskerRight s1 cD ≫ whiskerLeft dD s2 ≫ whiskerRight s3 gD =
        whiskerLeft aD s4 ≫ whiskerRight s5 kD ≫ whiskerLeft hD s6 := by
    apply Localization.natTrans_ext DerivedCategory.Q
      (HomologicalComplex.quasiIso C (.up ℤ))
    intro X
    simp only [NatTrans.comp_app, whiskerRight_app, whiskerLeft_app]
    apply (cancel_mono
      (gD.map (iD.map
          (φh.hom.app X)) ≫
        gD.map (φi.hom.app
          ((h.mapHomologicalComplex (.up ℤ)).obj X)) ≫
        φg.hom.app
          ((i.mapHomologicalComplex (.up ℤ)).obj
            ((h.mapHomologicalComplex (.up ℤ)).obj X)))).mp
    have h1X := h1 X
    have h2X := h2 ((d.mapHomologicalComplex (.up ℤ)).obj X)
    have h3X := h3 X
    have h4X := h4 ((a.mapHomologicalComplex (.up ℤ)).obj X)
    have h5X := h5 X
    have h6X := h6 ((h.mapHomologicalComplex (.up ℤ)).obj X)
    have n2 := s2.naturality (φd.hom.app X)
    have n4 := s4.naturality (φa.hom.app X)
    have n6 := s6.naturality (φh.hom.app X)
    dsimp only [Functor.comp_map] at n2 n4 n6
    have nl : cD.map (s1.app (DerivedCategory.Q.obj X)) ≫
        s2.app (dD.obj (DerivedCategory.Q.obj X)) ≫
        gD.map (s3.app (DerivedCategory.Q.obj X)) ≫
        gD.map (iD.map
          (φh.hom.app X)) ≫
        gD.map (φi.hom.app
          ((h.mapHomologicalComplex (.up ℤ)).obj X)) ≫
        φg.hom.app
          ((i.mapHomologicalComplex (.up ℤ)).obj
            ((h.mapHomologicalComplex (.up ℤ)).obj X)) =
        cD.map (bD.map
          (φa.hom.app X)) ≫
        cD.map (φb.hom.app
          ((a.mapHomologicalComplex (.up ℤ)).obj X)) ≫
        φc.hom.app
          ((b.mapHomologicalComplex (.up ℤ)).obj
            ((a.mapHomologicalComplex (.up ℤ)).obj X)) ≫
        DerivedCategory.Q.map
          ((c.mapHomologicalComplex (.up ℤ)).map
            ((NatTrans.mapHomologicalComplex q1 (.up ℤ)).app X) ≫
            (NatTrans.mapHomologicalComplex q2 (.up ℤ)).app
              ((d.mapHomologicalComplex (.up ℤ)).obj X) ≫
            (g.mapHomologicalComplex (.up ℤ)).map
              ((NatTrans.mapHomologicalComplex q3 (.up ℤ)).app X)) := by
      erw [← gD.map_comp_assoc, ← gD.map_comp_assoc]
      simp only [Category.assoc]
      erw [h3X]
      simp only [Functor.map_comp, Category.assoc]
      erw [φg.hom.naturality]
      erw [← reassoc_of% n2, reassoc_of% h2X]
      erw [← cD.map_comp_assoc, ← cD.map_comp_assoc]
      simp only [Category.assoc]
      erw [h1X]
      simp only [Functor.map_comp, Category.assoc]
      erw [φc.hom.naturality_assoc]
      simp only [Functor.comp_map]
    simp only [Category.assoc]
    erw [nl]
    erw [← reassoc_of% n6]
    erw [h6X]
    erw [← kD.map_comp_assoc, ← kD.map_comp_assoc]
    simp only [Category.assoc]
    erw [h5X]
    simp only [Functor.map_comp, Category.assoc]
    erw [φk.hom.naturality_assoc]
    erw [← reassoc_of% n4, reassoc_of% h4X]
    simp only [Functor.comp_map, ← Functor.map_comp]
    repeat' apply congrArg (fun t ↦ _ ≫ t)
    apply congrArg DerivedCategory.Q.map
    ext n
    exact comm (X.X n)
  simpa only [NatTrans.comp_app, whiskerRight_app, whiskerLeft_app] using
    congr_app hc X₀

private theorem scalar_inverse_mate_normalization
    (O : Type (u + 1)) [CommRing O] (t : O)
    {V W : Scheme.{u}} (g : V ⟶ W) (A : StrictEtaleOrdinaryImage O t g)
    (PW : StrictEtaleEvaluation W O t) (PV : StrictEtaleEvaluation V O t)
    (B : CoefficientSystemDerivedImage (J := W.smallEtaleTopology)
      (K := V.smallEtaleTopology) O t _ _ _ A PW PV)
    {m n : ℕ} (h : m ≤ n)
    (δ : (PW.scalar h).restriction ⋙ (B.level n).inverse ≅
      (B.level m).inverse ⋙ (PV.scalar h).restriction)
    (hδ : ∀ P,
      δ.hom.app (DerivedCategory.Q.obj P) ≫
        (PV.scalar h).restriction.map ((B.level m).inverseFactors.hom.app P) ≫
        (PV.scalar h).restrictionFactors.hom.app
          (((A.lift m).modules.mapHomologicalComplex (.up ℤ)).obj P) =
      (B.level n).inverse.map ((PW.scalar h).restrictionFactors.hom.app P) ≫
        (B.level n).inverseFactors.hom.app
          (((coefficientRestriction (J := W.smallEtaleTopology) O t h).mapHomologicalComplex
            (.up ℤ)).obj P) ≫
        DerivedCategory.Q.map
          ((NatIso.mapHomologicalComplex (A.restrictInverse h) (.up ℤ)).hom.app P)) :
    ((mateEquiv (PW.scalar h).derivedAdj (PV.scalar h).derivedAdj).symm
      (.mk _ _ _ _ δ.hom)).natTrans = (B.derivedTensor h).inv := by
  let μ := ((mateEquiv (PW.scalar h).derivedAdj (PV.scalar h).derivedAdj).symm
    (.mk _ _ _ _ δ.hom)).natTrans
  change μ = _
  apply hom_ext_flat W.smallEtaleTopology n
  intro P hk hf
  have hμ := derivedLeftSquare_rep (A.lift n).modules
    (coefficientTensor (J := W.smallEtaleTopology) (O := O) (ell := t) h)
    (coefficientRestriction (J := W.smallEtaleTopology) O t h)
    (coefficientTensor (J := V.smallEtaleTopology) (O := O) (ell := t) h)
    (coefficientRestriction (J := V.smallEtaleTopology) O t h)
    (coefficientTensorAdj (J := W.smallEtaleTopology) (O := O) (ell := t) h)
    (coefficientTensorAdj (J := V.smallEtaleTopology) (O := O) (ell := t) h)
    _ _ (PW.scalar h) (PV.scalar h) (A.lift m).modules
    (B.level n).inverse (B.level m).inverse
    (B.level n).inverseFactors (B.level m).inverseFactors
    (A.restrictInverse h) δ hδ (B.tensor h).symm
    (tensorSquare_transpose (A.lift n).modules
      (coefficientTensor (J := W.smallEtaleTopology) (O := O) (ell := t) h)
      (coefficientRestriction (J := W.smallEtaleTopology) O t h)
      (coefficientTensor (J := V.smallEtaleTopology) (O := O) (ell := t) h)
      (coefficientRestriction (J := V.smallEtaleTopology) O t h)
      (A.lift m).modules
      (coefficientTensorAdj (J := W.smallEtaleTopology) (O := O) (ell := t) h)
      (coefficientTensorAdj (J := V.smallEtaleTopology) (O := O) (ell := t) h)
      (A.restrictInverse h) (B.tensor h) (B.tensor_unit h)) P
  have hd := B.derivedTensor_rep h P hk hf
  let := (PW.scalar h).computes P hk
  apply (cancel_mono
    ((B.level m).inverse.map ((PW.scalar h).counit.app P) ≫
      (B.level m).inverseFactors.hom.app
        (((coefficientTensor (J := W.smallEtaleTopology)
          (O := O) (ell := t) h).mapHomologicalComplex (.up ℤ)).obj P))).1
  apply (cancel_epi ((B.derivedTensor h).hom.app (DerivedCategory.Q.obj P))).1
  simp only [Iso.hom_inv_id_app_assoc]
  change (B.derivedTensor h).hom.app (DerivedCategory.Q.obj P) ≫ (_ ≫ _ ≫ _) = _
  change μ.app (DerivedCategory.Q.obj P) ≫ _ = _ at hμ
  erw [hμ]
  erw [reassoc_of% hd]
  rw [← DerivedCategory.Q.map_comp]
  change _ ≫ _ ≫ DerivedCategory.Q.map
    ((NatIso.mapHomologicalComplex (B.tensor h) (.up ℤ)).hom.app P ≫
      (NatIso.mapHomologicalComplex (B.tensor h) (.up ℤ)).inv.app P) = _
  rw [Iso.hom_inv_id_app, DerivedCategory.Q.map_id, Category.comp_id]

private theorem inverse_mate_transport
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {L : A ⥤ B} {U : B ⥤ A} {M : C ⥤ D} {V : D ⥤ C}
    (a : L ⊣ U) (b : M ⊣ V)
    {G G' : A ⥤ C} {H H' : B ⥤ D}
    (x : TwoSquare U H G V) (e : G ≅ G') (f : H ≅ H') :
    ((mateEquiv a b).symm
      (TwoSquare.mk U H' G' V
        (Functor.whiskerLeft U e.inv ≫ x.natTrans ≫ Functor.whiskerRight f.hom V))).natTrans =
      Functor.whiskerRight e.inv M ≫ ((mateEquiv a b).symm x).natTrans ≫
        Functor.whiskerLeft L f.hom := by
  ext z
  simp only [mateEquiv_symm_apply, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, Functor.associator_hom_app, Functor.associator_inv_app,
    Functor.leftUnitor_inv_app, Functor.rightUnitor_hom_app,
    CategoryTheory.Functor.map_id, Category.id_comp, Functor.map_comp,
    Category.assoc]
  dsimp only [Functor.comp_obj, Functor.comp_map]
  simp only [Category.id_comp]
  have he := e.inv.naturality (a.unit.app z)
  dsimp only [Functor.comp_obj, Functor.id_obj] at he
  rw [← M.map_comp_assoc, he, M.map_comp]
  simp only [Category.assoc]
  have hf := b.counit.naturality (f.hom.app (L.obj z))
  dsimp only [Functor.comp_map, Functor.id_map] at hf
  erw [Category.comp_id]
  erw [Category.id_comp]
  rw [hf]

private theorem mateCube
    {C₀ C₁ C₂ C₃ D₀ D₁ D₂ D₃ : Type*}
    [Category C₀] [Category C₁] [Category C₂] [Category C₃]
    [Category D₀] [Category D₁] [Category D₂] [Category D₃]
    {S₀ : C₀ ⥤ D₀} {R₀ : D₀ ⥤ C₀} {S₁ : C₁ ⥤ D₁} {R₁ : D₁ ⥤ C₁}
    {S₂ : C₂ ⥤ D₂} {R₂ : D₂ ⥤ C₂} {S₃ : C₃ ⥤ D₃} {R₃ : D₃ ⥤ C₃}
    (a₀ : S₀ ⊣ R₀) (a₁ : S₁ ⊣ R₁) (a₂ : S₂ ⊣ R₂) (a₃ : S₃ ⊣ R₃)
    {J : C₀ ⥤ C₁} {H : C₁ ⥤ C₃} {G : C₀ ⥤ C₂} {I : C₂ ⥤ C₃}
    {J' : D₀ ⥤ D₁} {H' : D₁ ⥤ D₃} {G' : D₀ ⥤ D₂} {I' : D₂ ⥤ D₃}
    (qJ : R₀ ⋙ J ⟶ J' ⋙ R₁) (qH : R₁ ⋙ H ⟶ H' ⋙ R₃)
    (qG : R₀ ⋙ G ⟶ G' ⋙ R₂) (qI : R₂ ⋙ I ⟶ I' ⋙ R₃)
    (c : J ⋙ H ⟶ G ⋙ I) (d : J' ⋙ H' ⟶ G' ⋙ I')
    (hc : ∀ M, c.app (R₀.obj M) ≫ I.map (qG.app M) ≫ qI.app (G'.obj M) =
      H.map (qJ.app M) ≫ qH.app (J'.obj M) ≫ R₃.map (d.app M))
    (N : C₀) :
    S₃.map (c.app N) ≫
        ((mateEquiv a₂ a₃).symm (TwoSquare.mk _ _ _ _ qI)).natTrans.app (G.obj N) ≫
        I'.map (((mateEquiv a₀ a₂).symm (TwoSquare.mk _ _ _ _ qG)).natTrans.app N) =
      ((mateEquiv a₁ a₃).symm (TwoSquare.mk _ _ _ _ qH)).natTrans.app (J.obj N) ≫
        H'.map (((mateEquiv a₀ a₁).symm (TwoSquare.mk _ _ _ _ qJ)).natTrans.app N) ≫
        d.app (S₀.obj N) := by
  let lJ := ((mateEquiv a₀ a₁).symm (TwoSquare.mk _ _ _ _ qJ)).natTrans
  let lH := ((mateEquiv a₁ a₃).symm (TwoSquare.mk _ _ _ _ qH)).natTrans
  let lG := ((mateEquiv a₀ a₂).symm (TwoSquare.mk _ _ _ _ qG)).natTrans
  let lI := ((mateEquiv a₂ a₃).symm (TwoSquare.mk _ _ _ _ qI)).natTrans
  have hj (K : C₀) : J.map (a₀.unit.app K) ≫ qJ.app (S₀.obj K) =
      a₁.unit.app (J.obj K) ≫ R₁.map (lJ.app K) :=
    unit_mateEquiv_symm a₀ a₁ (TwoSquare.mk _ _ _ _ qJ) K
  have hh (K : C₁) : H.map (a₁.unit.app K) ≫ qH.app (S₁.obj K) =
      a₃.unit.app (H.obj K) ≫ R₃.map (lH.app K) :=
    unit_mateEquiv_symm a₁ a₃ (TwoSquare.mk _ _ _ _ qH) K
  have hg (K : C₀) : G.map (a₀.unit.app K) ≫ qG.app (S₀.obj K) =
      a₂.unit.app (G.obj K) ≫ R₂.map (lG.app K) :=
    unit_mateEquiv_symm a₀ a₂ (TwoSquare.mk _ _ _ _ qG) K
  have hi (K : C₂) : I.map (a₂.unit.app K) ≫ qI.app (S₂.obj K) =
      a₃.unit.app (I.obj K) ≫ R₃.map (lI.app K) :=
    unit_mateEquiv_symm a₂ a₃ (TwoSquare.mk _ _ _ _ qI) K
  change S₃.map (c.app N) ≫ lI.app (G.obj N) ≫ I'.map (lG.app N) =
    lH.app (J.obj N) ≫ H'.map (lJ.app N) ≫ d.app (S₀.obj N)
  apply (a₃.homEquiv _ _).injective
  simp only [Adjunction.homEquiv_unit, Functor.map_comp, Functor.comp_obj]
  have hn := a₃.unit.naturality (c.app N)
  dsimp only [Functor.id_map, Functor.comp_map, Functor.comp_obj] at hn
  rw [← reassoc_of% hn, ← reassoc_of% (hi (G.obj N))]
  have hq := qI.naturality (lG.app N)
  dsimp only [Functor.comp_map, Functor.comp_obj] at hq
  rw [← hq, ← I.map_comp_assoc, ← hg, I.map_comp]
  have hcn := c.naturality (a₀.unit.app N)
  dsimp only [Functor.comp_map, Functor.comp_obj] at hcn
  simp only [Category.assoc, Functor.id_obj] at hcn ⊢
  rw [← reassoc_of% hcn, hc]
  rw [← reassoc_of% (hh (J.obj N))]
  have hqn := qH.naturality (lJ.app N)
  dsimp only [Functor.comp_map, Functor.comp_obj] at hqn
  rw [← reassoc_of% hqn, ← H.map_comp_assoc, hj]
  simp only [Functor.map_comp, Category.assoc]

private theorem rotate_isomorphism_cube
    {C : Type*} [Category C] {X₀ X₁ X₂ X₃ X₄ X₅ : C}
    (a : X₀ ≅ X₁) (b : X₂ ≅ X₁) (c : X₂ ≅ X₃)
    (d : X₄ ≅ X₀) (e : X₄ ≅ X₅) (f : X₅ ≅ X₃)
    (h : a.hom ≫ b.inv ≫ c.hom = d.inv ≫ e.hom ≫ f.hom) :
    c.hom ≫ f.inv ≫ e.inv = b.hom ≫ a.inv ≫ d.inv := by
  apply (cancel_epi (a.hom ≫ b.inv)).1
  apply (cancel_mono (e.hom ≫ f.hom)).1
  simpa [Category.assoc] using h

private theorem mateCube_iso
    {C₀ C₁ C₂ C₃ D₀ D₁ D₂ D₃ : Type*}
    [Category C₀] [Category C₁] [Category C₂] [Category C₃]
    [Category D₀] [Category D₁] [Category D₂] [Category D₃]
    {S₀ : C₀ ⥤ D₀} {R₀ : D₀ ⥤ C₀} {S₁ : C₁ ⥤ D₁} {R₁ : D₁ ⥤ C₁}
    {S₂ : C₂ ⥤ D₂} {R₂ : D₂ ⥤ C₂} {S₃ : C₃ ⥤ D₃} {R₃ : D₃ ⥤ C₃}
    (a₀ : S₀ ⊣ R₀) (a₁ : S₁ ⊣ R₁) (a₂ : S₂ ⊣ R₂) (a₃ : S₃ ⊣ R₃)
    {J : C₀ ⥤ C₁} {H : C₁ ⥤ C₃} {G : C₀ ⥤ C₂} {I : C₂ ⥤ C₃}
    {J' : D₀ ⥤ D₁} {H' : D₁ ⥤ D₃} {G' : D₀ ⥤ D₂} {I' : D₂ ⥤ D₃}
    (qJ : R₀ ⋙ J ⟶ J' ⋙ R₁) (qH : R₁ ⋙ H ⟶ H' ⋙ R₃)
    (qG : R₀ ⋙ G ⟶ G' ⋙ R₂) (qI : R₂ ⋙ I ⟶ I' ⋙ R₃)
    (c : J ⋙ H ≅ G ⋙ I) (d : J' ⋙ H' ≅ G' ⋙ I')
    (eJ : S₀ ⋙ J' ≅ J ⋙ S₁) (eH : S₁ ⋙ H' ≅ H ⋙ S₃)
    (eG : S₀ ⋙ G' ≅ G ⋙ S₂) (eI : S₂ ⋙ I' ≅ I ⋙ S₃)
    (hJ : ((mateEquiv a₀ a₁).symm (.mk _ _ _ _ qJ)).natTrans = eJ.inv)
    (hH : ((mateEquiv a₁ a₃).symm (.mk _ _ _ _ qH)).natTrans = eH.inv)
    (hG : ((mateEquiv a₀ a₂).symm (.mk _ _ _ _ qG)).natTrans = eG.inv)
    (hI : ((mateEquiv a₂ a₃).symm (.mk _ _ _ _ qI)).natTrans = eI.inv)
    (hc : ∀ M, c.hom.app (R₀.obj M) ≫ I.map (qG.app M) ≫ qI.app (G'.obj M) =
      H.map (qJ.app M) ≫ qH.app (J'.obj M) ≫ R₃.map (d.hom.app M))
    (N : C₀) :
    I'.map (eG.inv.app N) ≫ d.inv.app (S₀.obj N) ≫ H'.map (eJ.hom.app N) =
      eI.hom.app (G.obj N) ≫ S₃.map (c.inv.app N) ≫ eH.inv.app (J.obj N) := by
  have hh := mateCube a₀ a₁ a₂ a₃ qJ qH qG qI c.hom d.hom hc N
  rw [hJ, hH, hG, hI] at hh
  apply rotate_isomorphism_cube (S₃.mapIso (c.app N)) (eI.app (G.obj N))
    (I'.mapIso (eG.symm.app N)) (eH.app (J.obj N))
    (H'.mapIso (eJ.symm.app N)) (d.app (S₀.obj N))
  simpa only [Functor.mapIso_hom, Iso.app_hom, Iso.app_inv, Iso.symm_hom] using hh

private theorem fixed_scalar_mate
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {V W : Scheme.{u}} (g : V ⟶ W) :
    ((mateEquiv
      (Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars W.smallEtaleTopology φ))
      (Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars V.smallEtaleTopology φ))).symm
      (.mk _ _ _ _ (Functor.mapDerivedCategorySquareIso
        (Etale.upperStarRestrictScalarsIsoSheaf φ g)).hom)).natTrans =
      (Etale.properOpenCoefficientPullbackIso φ g).inv := by
  let a := Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars W.smallEtaleTopology φ)
  let b := Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars V.smallEtaleTopology φ)
  let x := TwoSquare.mk _ _ _ _ (Etale.scalarRestrictionPullbackIso φ g).hom
  let e := Etale.leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) g
  let e' := Etale.leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} B) g
  have hx : ((mateEquiv a b).symm x).natTrans = (Etale.scalarPullbackIso φ g).inv := by
    simpa only [a, b, x, ProEtale.scalarPullbackReverseEtale,
      ProEtale.scalarPullbackEtaleIsoFromMate, Iso.symm_inv, asIso_hom]
      using congrArg Iso.inv (Etale.scalarPullback_eq φ g)
  have ht := inverse_mate_transport a b x e e'
  have he : TwoSquare.mk _ _ _ _
      (Functor.mapDerivedCategorySquareIso (Etale.upperStarRestrictScalarsIsoSheaf φ g)).hom =
      TwoSquare.mk _ _ _ _
        (Functor.whiskerLeft (Sheaf.derivedRestrictScalars W.smallEtaleTopology φ) e.inv ≫
          x.natTrans ≫ Functor.whiskerRight e'.hom
            (Sheaf.derivedRestrictScalars V.smallEtaleTopology φ)) := by
    ext M
    dsimp only [x, e, e', Etale.scalarRestrictionPullbackIso, NatTrans.comp_app,
      Functor.whiskerLeft_app, Functor.whiskerRight_app, Iso.trans_hom,
      Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom, Iso.symm_hom]
    simp only [Category.assoc, Iso.inv_hom_id_app_assoc,
      ← Functor.map_comp, Iso.inv_hom_id_app]
    erw [(Sheaf.restrictScalars V.smallEtaleTopology φ).mapDerivedCategory.map_id,
      Category.comp_id]
  rw [← he, hx] at ht
  simpa only [a, b, e, e', Etale.properOpenCoefficientPullbackIso, Iso.trans_inv,
    Iso.symm_inv, Functor.isoWhiskerRight_inv, Functor.isoWhiskerLeft_inv,
    Category.assoc, Etale.scalarExtension, ProEtale.pbcFixedScalarExtension,
    Sheaf.derivedRestrictScalars] using ht

private theorem exact_square_forward_rep
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    [Abelian A] [Abelian B] [Abelian C] [Abelian D]
    [HasDerivedCategory A] [HasDerivedCategory B]
    [HasDerivedCategory C] [HasDerivedCategory D]
    {F₁ : A ⥤ B} {F₂ : B ⥤ D} {G₁ : A ⥤ C} {G₂ : C ⥤ D}
    [F₁.Additive] [F₂.Additive] [G₁.Additive] [G₂.Additive]
    [PreservesFiniteLimits F₁] [PreservesFiniteColimits F₁]
    [PreservesFiniteLimits F₂] [PreservesFiniteColimits F₂]
    [PreservesFiniteLimits G₁] [PreservesFiniteColimits G₁]
    [PreservesFiniteLimits G₂] [PreservesFiniteColimits G₂]
    (e : F₁ ⋙ F₂ ≅ G₁ ⋙ G₂) (P : CochainComplex A ℤ) :
    (Functor.mapDerivedCategorySquareIso e).hom.app (DerivedCategory.Q.obj P) ≫
      G₂.mapDerivedCategory.map (G₁.mapDerivedCategoryFactors.hom.app P) ≫
      G₂.mapDerivedCategoryFactors.hom.app ((G₁.mapHomologicalComplex (.up ℤ)).obj P) =
    F₂.mapDerivedCategory.map (F₁.mapDerivedCategoryFactors.hom.app P) ≫
      F₂.mapDerivedCategoryFactors.hom.app ((F₁.mapHomologicalComplex (.up ℤ)).obj P) ≫
      DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex e.hom (.up ℤ)).app P) := by
  apply (cancel_epi
    (F₂.mapDerivedCategoryFactors.inv.app ((F₁.mapHomologicalComplex (.up ℤ)).obj P) ≫
      F₂.mapDerivedCategory.map (F₁.mapDerivedCategoryFactors.inv.app P))).1
  simp only [Category.assoc, ← Functor.map_comp_assoc, Iso.inv_hom_id_app]
  erw [F₂.mapDerivedCategory.map_id, Category.id_comp, Iso.inv_hom_id_app_assoc]
  exact Functor.square_cochain_fac e P

private theorem inverse_mate_of_mate_eq
    {C₀ D₀ C₁ D₁ : Type*}
    [Category C₀] [Category D₀] [Category C₁] [Category D₁]
    {S₀ : C₀ ⥤ D₀} {R₀ : D₀ ⥤ C₀} {S₁ : C₁ ⥤ D₁} {R₁ : D₁ ⥤ C₁}
    (a : S₀ ⊣ R₀) (b : S₁ ⊣ R₁) {G : C₀ ⥤ C₁} {H : D₀ ⥤ D₁}
    (e : S₀ ⋙ H ≅ G ⋙ S₁) (q : R₀ ⋙ G ⟶ H ⋙ R₁)
    (hq : mateEquiv a b (.mk _ _ _ _ e.inv) = .mk _ _ _ _ q) :
    ((mateEquiv a b).symm (.mk _ _ _ _ q)).natTrans = e.inv := by
  rw [← hq]
  exact congrArg TwoSquare.natTrans (Equiv.symm_apply_apply _ _)

private theorem derived_inverse_restriction_cube
    (O : Type (u + 1)) [CommRing O] (t : O)
    {V W : Scheme.{u}} (g : V ⟶ W)
    (A : StrictEtaleOrdinaryImage O t g)
    (PW : StrictEtaleEvaluation W O t) (PV : StrictEtaleEvaluation V O t)
    (B : CoefficientSystemDerivedImage (J := W.smallEtaleTopology)
      (K := V.smallEtaleTopology) O t _ _ _ A PW PV)
    (RV : StrictEtaleBrownRealization O t V PV)
    (RW : StrictEtaleBrownRealization O t W PW)
    (r : ∀ n, StrictEtaleBrownImageRealization O t g n A (B.level n) RV RW)
    {m n : ℕ} (h : m ≤ n)
    (δ : (PW.scalar h).restriction ⋙ (B.level n).inverse ≅
      (B.level m).inverse ⋙ (PV.scalar h).restriction)
    (hδ : ∀ P,
      δ.hom.app (DerivedCategory.Q.obj P) ≫
        (PV.scalar h).restriction.map ((B.level m).inverseFactors.hom.app P) ≫
        (PV.scalar h).restrictionFactors.hom.app
          (((A.lift m).modules.mapHomologicalComplex (.up ℤ)).obj P) =
      (B.level n).inverse.map ((PW.scalar h).restrictionFactors.hom.app P) ≫
        (B.level n).inverseFactors.hom.app
          (((coefficientRestriction (J := W.smallEtaleTopology) O t h).mapHomologicalComplex
            (.up ℤ)).obj P) ≫
        DerivedCategory.Q.map
          ((NatIso.mapHomologicalComplex (A.restrictInverse h) (.up ℤ)).hom.app P))
    (M : DerivedCategory (strictEtaleLevel W O t m)) :
    (Etale.upperStar (ModuleCat.{u + 1} (strictEtaleBrownRing O t n))
        g).mapDerivedCategory.map ((RW.val.restriction h).hom.app M) ≫
      (Functor.mapDerivedCategorySquareIso
        (Etale.upperStarRestrictScalarsIsoSheaf (strictEtaleBrownRingMap O t h) g)).hom.app
          ((RW.derived m).obj M) ≫
      (Sheaf.derivedRestrictScalars V.smallEtaleTopology
        (strictEtaleBrownRingMap O t h)).map ((r m).inverse.hom.app M) =
    (r n).inverse.hom.app ((PW.scalar h).restriction.obj M) ≫
      (RV.derived n).map (δ.hom.app M) ≫
      (RV.val.restriction h).hom.app ((B.level m).inverse.obj M) := by
  let := RV.val.ordinaryAdditive
  let := RW.val.ordinaryAdditive
  let ord := Etale.upperStarRestrictScalarsIsoSheaf (strictEtaleBrownRingMap O t h) g
  let fixed := Functor.mapDerivedCategorySquareIso ord
  exact normalized_cube
    (C := strictEtaleLevel W O t m) (D := strictEtaleLevel W O t n)
    (E := Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} (strictEtaleBrownRing O t n)))
    (F := Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} (strictEtaleBrownRing O t n)))
    (G := Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} (strictEtaleBrownRing O t m)))
    (H := Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} (strictEtaleBrownRing O t m)))
    (I := strictEtaleLevel V O t m) (J := strictEtaleLevel V O t n)
    (coefficientRestriction (J := W.smallEtaleTopology) O t h)
    (strictEtaleBrownConstant O t W n)
    (Etale.upperStar (ModuleCat.{u + 1} (strictEtaleBrownRing O t n)) g)
    (strictEtaleBrownConstant O t W m)
    (Sheaf.restrictScalars W.smallEtaleTopology (strictEtaleBrownRingMap O t h))
    (Etale.upperStar (ModuleCat.{u + 1} (strictEtaleBrownRing O t m)) g)
    (Sheaf.restrictScalars V.smallEtaleTopology (strictEtaleBrownRingMap O t h))
    (A.lift m).modules (strictEtaleBrownConstant O t V m)
    (A.lift n).modules (strictEtaleBrownConstant O t V n)
    (coefficientRestriction (J := V.smallEtaleTopology) O t h)
    (PW.scalar h).restriction (RW.derived n)
    (Etale.upperStar (ModuleCat.{u + 1} (strictEtaleBrownRing O t n)) g).mapDerivedCategory
    (RW.derived m)
    (Sheaf.derivedRestrictScalars W.smallEtaleTopology (strictEtaleBrownRingMap O t h))
    (Etale.upperStar (ModuleCat.{u + 1} (strictEtaleBrownRing O t m)) g).mapDerivedCategory
    (Sheaf.derivedRestrictScalars V.smallEtaleTopology (strictEtaleBrownRingMap O t h))
    (B.level m).inverse (RV.derived m) (B.level n).inverse (RV.derived n)
    (PV.scalar h).restriction
    (PW.scalar h).restrictionFactors (RW.factors n)
    (Etale.upperStar (ModuleCat.{u + 1} (strictEtaleBrownRing O t n))
      g).mapDerivedCategoryFactors (RW.factors m)
    (Sheaf.restrictScalars W.smallEtaleTopology
      (strictEtaleBrownRingMap O t h)).mapDerivedCategoryFactors
    (Etale.upperStar (ModuleCat.{u + 1} (strictEtaleBrownRing O t m))
      g).mapDerivedCategoryFactors
    (Sheaf.restrictScalars V.smallEtaleTopology
      (strictEtaleBrownRingMap O t h)).mapDerivedCategoryFactors
    (B.level m).inverseFactors (RV.factors m) (B.level n).inverseFactors (RV.factors n)
    (PV.scalar h).restrictionFactors
    (RW.val.ordinaryRestriction h).hom (RW.val.restriction h).hom
    ord.hom fixed.hom
    (ordinary_inverse O t g A m (r m).val.ordinaryRight) (r m).inverse.hom
    (ordinary_inverse O t g A n (r n).val.ordinaryRight) (r n).inverse.hom
    (A.restrictInverse h).hom δ.hom
    (RV.val.ordinaryRestriction h).hom (RV.val.restriction h).hom
    (RW.property.2.1 h)
    (fun P ↦ exact_square_forward_rep ord P)
    (inverse_representative_of_right O t g m A (B.level m) RV RW (r m))
    (inverse_representative_of_right O t g n A (B.level n) RV RW (r n))
    hδ (RV.property.2.1 h)
    (ordinary_inverse_restriction_cube O t g A RV RW
      (fun n ↦ (r n).val.ordinaryRight) (fun n ↦ (r n).property.1) h) M

/-- Scalar extension respects a normalized inverse-image realization.
Source: Zheng Construction 4.1 and Lemma 5.16; Stacks 03CY, 06YY and 07A4.
(blueprint: lem-pur-etale-brown-scalar-inverse-realization-cube).

Proof: reconstruct the ordinary inverse comparison as the inverse mate of the
normalized ordinary right-image comparison. The derived direct-unit equation and
Hom transpose normalizations give its inverse representative equation. Take
geometric mates of the ordinary restriction cube: levelTranspose and
restrictInverseUnderlying identify the underlying restriction mate, and the section
normalizations for ordinaryRight and ordinaryRestriction identify its two paths.
Localize the ordinary restriction/inverse square. Its inverse scalar mate has the
ordinary tensor representative equation by derivedMate_comparison and tensor_unit.
Compare with derivedTensor_rep on flat-term K-flat sources and cancel the source
scalar computation counit; resolution naturality gives equality on all objects.
The six face normalizations localize the ordinary cube. The published fixed scalar
comparison is the inverse scalar mate of its restriction face. Apply scalar mates
to the localized cube and cancel the realization isomorphisms. The supplied e and
he are unnecessary for this route. No finiteness, coefficient flatness, boundedness
or open-immersion hypothesis is used. -/
theorem etaleBrownScalarInverseRealization_cube
    (O : Type (u + 1)) [CommRing O] (t : O)
    {V W : Scheme.{u}} (g : V ⟶ W)
    (A : StrictEtaleOrdinaryImage O t g)
    (PW : StrictEtaleEvaluation W O t) (PV : StrictEtaleEvaluation V O t)
    (B : CoefficientSystemDerivedImage (J := W.smallEtaleTopology)
      (K := V.smallEtaleTopology) O t _ _ _ A PW PV)
    (RV : StrictEtaleBrownRealization O t V PV)
    (RW : StrictEtaleBrownRealization O t W PW)
    (r : ∀ n, StrictEtaleBrownImageRealization O t g n A (B.level n) RV RW)
    (e : ∀ n, (A.lift n).modules ⋙ strictEtaleBrownConstant O t V n ≅
        strictEtaleBrownConstant O t W n ⋙
          Etale.upperStar (ModuleCat.{u + 1} (strictEtaleBrownRing O t n)) g)
    (he : letI := RV.val.ordinaryAdditive
      letI := RW.val.ordinaryAdditive
      ∀ n (K : CochainComplex (strictEtaleLevel W O t n) ℤ),
        (r n).inverse.inv.app (DerivedCategory.Q.obj K) ≫
          (Etale.upperStar (ModuleCat.{u + 1} (strictEtaleBrownRing O t n))
            g).mapDerivedCategory.map ((RW.factors n).hom.app K) ≫
          (Etale.upperStar (ModuleCat.{u + 1} (strictEtaleBrownRing O t n))
            g).mapDerivedCategoryFactors.hom.app
            (((strictEtaleBrownConstant O t W n).mapHomologicalComplex (.up ℤ)).obj K) =
        (RV.derived n).map ((B.level n).inverseFactors.hom.app K) ≫
          (RV.factors n).hom.app (((A.lift n).modules.mapHomologicalComplex (.up ℤ)).obj K) ≫
          DerivedCategory.Q.map ((NatIso.mapHomologicalComplex (e n) (.up ℤ)).hom.app K))
    {m n : ℕ} (h : m ≤ n) (K : DerivedCategory (strictEtaleLevel W O t n)) :
    (RV.derived m).map ((B.derivedTensor h).inv.app K) ≫
      (r m).inverse.inv.app ((PW.scalar h).derived.obj K) ≫
      (Etale.upperStar (ModuleCat.{u + 1} (strictEtaleBrownRing O t m))
        g).mapDerivedCategory.map ((RW.scalar h).hom.app K) =
    (RV.scalar h).hom.app ((B.level n).inverse.obj K) ≫
      (Etale.scalarExtension (strictEtaleBrownRingMap O t h) V).map ((r n).inverse.inv.app K) ≫
      (Etale.properOpenCoefficientPullbackIso (strictEtaleBrownRingMap O t h) g).inv.app
        ((RW.derived n).obj K) := by
  have _he := he
  clear _he he e
  let := RV.val.ordinaryAdditive
  let := RW.val.ordinaryAdditive
  obtain ⟨δ, hδ⟩ := exists_derivedSquare_independentUniverses
    (A := strictEtaleLevel W O t m) (B := strictEtaleLevel W O t n)
    (C := strictEtaleLevel V O t m) (D := strictEtaleLevel V O t n)
    (coefficientRestriction (J := W.smallEtaleTopology) O t h)
    (A.lift m).modules (A.lift n).modules
    (coefficientRestriction (J := V.smallEtaleTopology) O t h)
    (PW.scalar h).restriction (B.level m).inverse (B.level n).inverse
    (PV.scalar h).restriction
    (PW.scalar h).restrictionFactors (B.level m).inverseFactors
    (B.level n).inverseFactors (PV.scalar h).restrictionFactors (A.restrictInverse h)
  let ord := Etale.upperStarRestrictScalarsIsoSheaf (strictEtaleBrownRingMap O t h) g
  let fixed := Functor.mapDerivedCategorySquareIso ord
  have hc := derived_inverse_restriction_cube O t g A PW PV B RV RW r h δ hδ
  let aw := (PW.scalar h).derivedAdj
  let av := (PV.scalar h).derivedAdj
  let bw := Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars W.smallEtaleTopology
    (strictEtaleBrownRingMap O t h))
  let bv := Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars V.smallEtaleTopology
    (strictEtaleBrownRingMap O t h))
  have hw := inverse_mate_of_mate_eq aw bw (RW.scalar h)
    (RW.val.restriction h).hom (RW.property.2.2 h)
  have hv := inverse_mate_of_mate_eq av bv (RV.scalar h)
    (RV.val.restriction h).hom (RV.property.2.2 h)
  have ht := scalar_inverse_mate_normalization O t g A PW PV B h δ hδ
  exact mateCube_iso aw bw av bv
      (J := RW.derived n)
      (H := (Etale.upperStar (ModuleCat.{u + 1} (strictEtaleBrownRing O t n))
        g).mapDerivedCategory)
      (G := (B.level n).inverse) (I := RV.derived n)
      (J' := RW.derived m)
      (H' := (Etale.upperStar (ModuleCat.{u + 1} (strictEtaleBrownRing O t m))
        g).mapDerivedCategory)
      (G' := (B.level m).inverse) (I' := RV.derived m)
      (RW.val.restriction h).hom fixed.hom δ.hom (RV.val.restriction h).hom
      (r n).inverse (r m).inverse (RW.scalar h)
      (Etale.properOpenCoefficientPullbackIso (strictEtaleBrownRingMap O t h) g)
      (B.derivedTensor h) (RV.scalar h)
      hw (fixed_scalar_mate (strictEtaleBrownRingMap O t h) g) ht hv
      (fun M ↦ (hc M).symm) K

end AlgebraicGeometry
