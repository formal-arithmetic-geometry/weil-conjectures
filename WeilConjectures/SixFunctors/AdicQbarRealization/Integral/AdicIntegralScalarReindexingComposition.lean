/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.AdicQbarRealization.AdicRealizationFamilyData
import WeilConjectures.SixFunctors.AdicQbarRealization.Integral.AdicIntegralScalarOrdinaryComposition
import all WeilConjectures.CategoryTheory.Exact.ExactEquivalenceDerivedSquares
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate

/-! # Composition of balanced integral scalar reindexing

This square concerns ambient integral derived modules and extension of scalars only.
It contains neither common-stage realization comparisons nor completion-unit inverses.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [local irreducible] HasDerivedCategory.standard
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme
namespace WeilConjectures.AdicQbarRealization
variable (l : ℕ) [Fact l.Prime] (D : FiniteFieldDatum.{u})

attribute [local irreducible] coefficientMap pbcExtensionCounit
  integralCoefficientLinear completedIntegralCoefficientSheafUnrestricted pbcTensorSection

private theorem derived_square_ext
    {A B H : Type*} [Category* A] [Category* B] [Category* H]
    [Abelian A] [Abelian B] [HasDerivedCategory A] [HasDerivedCategory B]
    (F : A ⥤ B) [F.Additive] [F.IsEquivalence]
    (FD : DerivedCategory A ⥤ DerivedCategory B) [FD.IsEquivalence]
    (e : DerivedCategory.Q ⋙ FD ≅
      F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q) (LF : DerivedCategory B ⥤ H)
    (L : CochainComplex B ℤ ⥤ H) (ε : DerivedCategory.Q ⋙ LF ⟶ L)
    [LF.IsRightKanExtension ε]
    {S : DerivedCategory A ⥤ H} (α β : S ⟶ FD ⋙ LF)
    (h : ∀ P : CochainComplex A ℤ,
      α.app (DerivedCategory.Q.obj P) ≫ LF.map (e.hom.app P) ≫
        ε.app ((F.mapHomologicalComplex (.up ℤ)).obj P) =
      β.app (DerivedCategory.Q.obj P) ≫ LF.map (e.hom.app P) ≫
        ε.app ((F.mapHomologicalComplex (.up ℤ)).obj P)) : α = β := by
  let c := kanSquareCounit (F.asEquivalence.mapHomologicalComplex (.up ℤ))
    FD.asEquivalence DerivedCategory.Q DerivedCategory.Q L LF ε e
  have : (FD ⋙ LF).IsRightKanExtension c :=
    kanSquare_universal (F.asEquivalence.mapHomologicalComplex (.up ℤ))
      FD.asEquivalence DerivedCategory.Q DerivedCategory.Q L LF ε e
  apply (FD ⋙ LF).hom_ext_of_isRightKanExtension c
  ext P
  simpa only [c, kanSquareCounit, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.associator_inv_app, Functor.associator_hom_app,
    Category.id_comp, Category.comp_id, Category.assoc, Functor.asEquivalence,
    Equivalence.mapHomologicalComplex, Equivalence.mk] using h P

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

private theorem triangle_factors
    {A B C : Type*} [Category* A] [Category* B] [Category* C]
    [Abelian A] [Abelian B] [Abelian C]
    [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory C]
    (F : A ⥤ B) (G : B ⥤ C) (J : A ⥤ C)
    [F.Additive] [G.Additive] [J.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits J] [PreservesFiniteColimits J]
    (e : J ≅ F ⋙ G) (Q : CochainComplex A ℤ) :
    (Functor.mapDerivedCategoryNatIso e ≪≫ Functor.mapDerivedCategoryCompIso F G).hom.app
        (DerivedCategory.Q.obj Q) ≫
      G.mapDerivedCategory.map (F.mapDerivedCategoryFactors.hom.app Q) ≫
      G.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj Q) =
    J.mapDerivedCategoryFactors.hom.app Q ≫
      DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex e.hom (.up ℤ)).app Q) := by
  simp only [Iso.trans_hom, NatTrans.comp_app, Category.assoc]
  rw [Functor.mapDerivedCategoryCompIso_hom_app_factors,
    Functor.mapDerivedCategoryNatIso_fac]

private theorem scalar_counit_natural {X : Scheme.{u}}
    {R S : Sheaf (ProEt.topology X) CommRingCat.{u + 1}} (j : R ⟶ S)
    {P Q : CochainComplex (pbcModules X R) ℤ} (f : P ⟶ Q) :
    (pbcDerivedExtend j).map (DerivedCategory.Q.map f) ≫ pbcComplexCounit j Q =
      pbcComplexCounit j P ≫
        DerivedCategory.Q.map (((pbcExtend j).mapHomologicalComplex (.up ℤ)).map f) := by
  let ε := derivedCochainCounit (pbcExtend j) (pbcDerivedExtend j) (pbcExtensionCounit j)
  have he (P : CochainComplex (pbcModules X R) ℤ) : ε.app P = pbcComplexCounit j P := by
    simp [ε, derivedCochainCounit, derivedCochainComparisonFactors, pbcComplexCounit]
  simpa only [Functor.comp_map, he] using ε.naturality f

attribute [local irreducible] Functor.mapDerivedCategory
  Functor.mapDerivedCategoryFactors Functor.mapDerivedCategoryNatIso
  Functor.mapDerivedCategoryCompIso
attribute [local irreducible] modulePull podCompletedModuleInverseImage
  completedIntegralCommRingSheafUnrestricted
attribute [local implicit_reducible] Functor.mapHomologicalComplex
  NatIso.mapHomologicalComplex derivedPull podCompletedDerivedInverseImage

set_option maxHeartbeats 600000 in
-- The cochain comparison uses six exact functors and their localization factors.
private theorem derived_forward_composition
    (C : FamilyCore l D) (T U V : GeometricSpace D)
    (g : T.base.left ≅ U.base.left) (h : U.base.left ≅ V.base.left)
    (hs : ∀ (M : modules l V.base.left (C.data V).realization)
      (W : T.base.left.ProEtᵒᵖ)
      (x : ((modulePull l T.base.left (g ≪≫ h).hom
        (C.ring T V (g ≪≫ h))).obj M).val.obj W),
      HEq (((C.moduleComp T U V g h).hom.app M).val.app W x) x)
    (E : AlgebraicallyClosedCoefficients.Index l (PadicAlgCl l))
    (K : DerivedCategory (integralTowerModules l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) V.base.left)) :
    (C.integral T V (g ≪≫ h) E).derived.hom.app K ≫
      (pbcDerivedExtend (coefficientMap l T.base.left (C.data T).realization E)).map
        ((podCompletedDerivedComp l
          (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E)
          h.hom g.hom).hom.app K) =
    (Functor.mapDerivedCategoryNatIso (C.moduleComp T U V g h) ≪≫
        Functor.mapDerivedCategoryCompIso _ _).hom.app
          ((pbcDerivedExtend (coefficientMap l V.base.left (C.data V).realization E)).obj K) ≫
      (derivedPull l T.base.left g.hom (C.ring T U g)).map
        ((C.integral U V h E).derived.hom.app K) ≫
      (C.integral T U g E).derived.hom.app
        ((podCompletedDerivedInverseImage l
          (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) h.hom).obj K) := by
  let A := AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E
  let F := podCompletedModuleInverseImage l A g.hom
  let H := podCompletedModuleInverseImage l A h.hom
  let J := podCompletedModuleInverseImage l A (g ≪≫ h).hom
  let G := modulePull l T.base.left g.hom (C.ring T U g)
  let N := modulePull l U.base.left h.hom (C.ring U V h)
  let P := modulePull l T.base.left (g ≪≫ h).hom (C.ring T V (g ≪≫ h))
  let jT := coefficientMap l T.base.left (C.data T).realization E
  let jU := coefficientMap l U.base.left (C.data U).realization E
  let jV := coefficientMap l V.base.left (C.data V).realization E
  let LT := pbcDerivedExtend jT
  let LU := pbcDerivedExtend jU
  let LV := pbcDerivedExtend jV
  let cF := podCompletedDerivedComp l A h.hom g.hom
  let cG := Functor.mapDerivedCategoryNatIso (C.moduleComp T U V g h) ≪≫
    Functor.mapDerivedCategoryCompIso N G
  let d0 := (C.integral T V (g ≪≫ h) E).derived
  let dh := (C.integral U V h E).derived
  let dg := (C.integral T U g E).derived
  let ε := derivedCochainCounit (pbcExtend jT) LT (pbcExtensionCounit jT)
  have : LT.IsLeftDerivedFunctor (pbcExtensionCounit jT)
      (HomotopyCategory.quasiIso (integralTowerModules l A T.base.left) (.up ℤ)) :=
    pbcDerivedExtension_universal jT
  have : LT.IsRightKanExtension ε := cochainCounit_universal _ _ _
  have hε (Q : CochainComplex (integralTowerModules l A T.base.left) ℤ) :
      ε.app Q = pbcComplexCounit jT Q := by
    simp [ε, LT, derivedCochainCounit, derivedCochainComparisonFactors, pbcComplexCounit]
  have : H.IsEquivalence := (podCompletedInverseImage_equivalence l A h.hom).1
  have : F.IsEquivalence := (podCompletedInverseImage_equivalence l A g.hom).1
  have : H.mapDerivedCategory.IsEquivalence :=
    (podCompletedInverseImage_equivalence l A h.hom).2
  have : F.mapDerivedCategory.IsEquivalence :=
    (podCompletedInverseImage_equivalence l A g.hom).2
  let e : DerivedCategory.Q ⋙ (H.mapDerivedCategory ⋙ F.mapDerivedCategory) ≅
      (H ⋙ F).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q :=
    Functor.isoWhiskerLeft DerivedCategory.Q
        (Functor.mapDerivedCategoryCompIso H F).symm ≪≫
      (H ⋙ F).mapDerivedCategoryFactors
  have he (Q : CochainComplex (integralTowerModules l A V.base.left) ℤ) :
      e.hom.app Q =
        F.mapDerivedCategory.map (H.mapDerivedCategoryFactors.hom.app Q) ≫
          F.mapDerivedCategoryFactors.hom.app ((H.mapHomologicalComplex (.up ℤ)).obj Q) := by
    dsimp only [e, Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
      Functor.whiskerLeft_app, Iso.symm_hom]
    rw [← Functor.mapDerivedCategoryCompIso_hom_app_factors H F Q]
    simp only [Iso.inv_hom_id_app_assoc]
  let α : LV ⋙ P.mapDerivedCategory ⟶
      (H.mapDerivedCategory ⋙ F.mapDerivedCategory) ⋙ LT :=
    d0.hom ≫ Functor.whiskerRight cF.hom LT
  let β : LV ⋙ P.mapDerivedCategory ⟶
      (H.mapDerivedCategory ⋙ F.mapDerivedCategory) ⋙ LT :=
    Functor.whiskerLeft LV cG.hom ≫
      Functor.whiskerRight dh.hom G.mapDerivedCategory ≫
        Functor.whiskerLeft H.mapDerivedCategory dg.hom
  have hαβ : α = β := by
    apply derived_square_ext (H ⋙ F) (H.mapDerivedCategory ⋙ F.mapDerivedCategory)
      e LT _ ε α β
    intro Q
    simp only [he Q, hε]
    dsimp only [α, β, NatTrans.comp_app, Functor.whiskerRight_app,
      Functor.whiskerLeft_app]
    let Qh := (H.mapHomologicalComplex (.up ℤ)).obj Q
    have r0 := (C.integral T V (g ≪≫ h) E).representative Q
    have rh := (C.integral U V h E).representative Q
    have rg := (C.integral T U g E).representative Qh
    have cf := triangle_factors H F J (podCompletedModuleComp l A h.hom g.hom) Q
    have cg := triangle_factors N G P (C.moduleComp T U V g h)
      (((pbcExtend jV).mapHomologicalComplex (.up ℤ)).obj Q)
    have ne := scalar_counit_natural jT
      ((NatTrans.mapHomologicalComplex
        (podCompletedModuleComp l A h.hom g.hom).hom (.up ℤ)).app Q)
    have nd := dg.hom.naturality (H.mapDerivedCategoryFactors.hom.app Q)
    have ng := G.mapDerivedCategoryFactors.hom.naturality
      ((NatTrans.mapHomologicalComplex (C.integral U V h E).balance.hom (.up ℤ)).app Q)
    have nc := cG.hom.naturality (pbcComplexCounit jV Q)
    have ho :
        ((NatTrans.mapHomologicalComplex (C.integral T V (g ≪≫ h) E).balance.hom
          (.up ℤ)).app Q) ≫
          ((pbcExtend jT).mapHomologicalComplex (.up ℤ)).map
            ((NatTrans.mapHomologicalComplex
              (podCompletedModuleComp l A h.hom g.hom).hom (.up ℤ)).app Q) =
        ((NatTrans.mapHomologicalComplex (C.moduleComp T U V g h).hom (.up ℤ)).app
          (((pbcExtend jV).mapHomologicalComplex (.up ℤ)).obj Q)) ≫
          (G.mapHomologicalComplex (.up ℤ)).map
            ((NatTrans.mapHomologicalComplex (C.integral U V h E).balance.hom
              (.up ℤ)).app Q) ≫
          ((NatTrans.mapHomologicalComplex (C.integral T U g E).balance.hom
            (.up ℤ)).app Qh) := by
      apply HomologicalComplex.hom_ext
      intro n
      exact integralScalarReindexing_balance_composition l D C T U V g h hs E (Q.X n)
    simp only [LT.map_comp, Category.assoc]
    change d0.hom.app (DerivedCategory.Q.obj Q) ≫
        LT.map (cF.hom.app (DerivedCategory.Q.obj Q)) ≫
        LT.map (F.mapDerivedCategory.map (H.mapDerivedCategoryFactors.hom.app Q)) ≫
        LT.map (F.mapDerivedCategoryFactors.hom.app Qh) ≫
        pbcComplexCounit jT ((F.mapHomologicalComplex (.up ℤ)).obj Qh) =
      cG.hom.app (LV.obj (DerivedCategory.Q.obj Q)) ≫
        G.mapDerivedCategory.map (dh.hom.app (DerivedCategory.Q.obj Q)) ≫
        dg.hom.app (H.mapDerivedCategory.obj (DerivedCategory.Q.obj Q)) ≫
        LT.map (F.mapDerivedCategory.map (H.mapDerivedCategoryFactors.hom.app Q)) ≫
        LT.map (F.mapDerivedCategoryFactors.hom.app Qh) ≫
        pbcComplexCounit jT ((F.mapHomologicalComplex (.up ℤ)).obj Qh)
    dsimp only [derivedPull, podCompletedDerivedInverseImage,
      Functor.comp_obj, Functor.comp_map] at r0 rh rg nd nc ng
    have cf' := congrArg LT.map cf
    simp only [Functor.map_comp] at cf'
    conv_lhs => rhs; erw [reassoc_of% cf']
    conv_lhs => rhs; rhs; erw [ne]
    conv_lhs => erw [reassoc_of% r0]
    conv_rhs => rhs; rhs; erw [← reassoc_of% nd]
    conv_rhs => rhs; rhs; rhs; erw [rg]
    conv_rhs =>
      rhs
      erw [← G.mapDerivedCategory.map_comp_assoc,
        ← G.mapDerivedCategory.map_comp_assoc]
      simp only [Category.assoc]
    conv_rhs => rhs; erw [rh]
    conv_rhs =>
      rhs
      erw [G.mapDerivedCategory.map_comp_assoc, G.mapDerivedCategory.map_comp_assoc]
    conv_rhs => rhs; rhs; erw [reassoc_of% ng]
    conv_rhs => erw [← reassoc_of% nc]
    conv_rhs => rhs; erw [reassoc_of% cg]
    simp only [← DerivedCategory.Q.map_comp]
    conv_rhs => rhs; erw [← ho]
    rfl
  exact NatTrans.congr_app hαβ K

/-- The balanced scalar comparison respects the section-normalized compositors.
Source: Bhatt--Scholze, Remark 6.8.15, explicit inverse-image formula;
Stacks 03EL, 07A4 and 0941. This is its scalar-composition refinement.
Proof: use the scalar adjunction to test ordinary module maps on tensors 1 tensor x.
The section normalization identifies each inverse balanced comparison on these tensors.
The scalar-adjunction unit is natural, and both ordinary module compositors are
identity on sections, with the site-composition transport retained by HEq. This proves
the ordinary square. Invert it and apply the equation termwise to complexes.
The representative equations of the three IntegralReindex data identify their
derived maps after the universal scalar-extension cochain counits. The exact
inverse-image factorization and its compositor identify the remaining factors.
Uniqueness for the total left derived functor transports this cochain equality
to every ambient derived module. Invert the forward square and whisker its
isomorphisms to obtain the displayed inverse equation. No completeness or
constructibility is used.
(blueprint: lem-sf-adic-integral-scalar-reindexing-composition)
-/
theorem integralScalarReindexing_composition
    (C : FamilyCore l D) (T U V : GeometricSpace D)
    (g : T.base.left ≅ U.base.left) (h : U.base.left ≅ V.base.left)
    (h_sections : ∀ (M : modules l V.base.left (C.data V).realization)
      (W : T.base.left.ProEtᵒᵖ)
      (x : ((modulePull l T.base.left (g ≪≫ h).hom
        (C.ring T V (g ≪≫ h))).obj M).val.obj W),
      HEq (((C.moduleComp T U V g h).hom.app M).val.app W x) x)
    (E : AlgebraicallyClosedCoefficients.Index l (PadicAlgCl l))
    (K : DerivedCategory (integralTowerModules l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) V.base.left)) :
    (C.integral T V (g ≪≫ h) E).derived.inv.app K ≫
      (Functor.mapDerivedCategoryNatIso (C.moduleComp T U V g h) ≪≫
        Functor.mapDerivedCategoryCompIso _ _).hom.app
          ((pbcDerivedExtend (coefficientMap l V.base.left (C.data V).realization E)).obj K) =
    (pbcDerivedExtend (coefficientMap l T.base.left (C.data T).realization E)).map
        ((podCompletedDerivedComp l
          (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E)
          h.hom g.hom).hom.app K) ≫
      (C.integral T U g E).derived.inv.app
        ((podCompletedDerivedInverseImage l
          (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) h.hom).obj K) ≫
      (derivedPull l T.base.left g.hom (C.ring T U g)).map
        ((C.integral U V h E).derived.inv.app K) := by
  have hf := derived_forward_composition l D C T U V g h h_sections E K
  apply (cancel_epi ((C.integral T V (g ≪≫ h) E).derived.hom.app K)).1
  simp only [Iso.hom_inv_id_app_assoc]
  rw [← Category.assoc _
    ((pbcDerivedExtend (coefficientMap l T.base.left (C.data T).realization E)).map _), hf]
  have hm :
      (derivedPull l T.base.left g.hom (C.ring T U g)).map
          ((C.integral U V h E).derived.hom.app K) ≫
        (derivedPull l T.base.left g.hom (C.ring T U g)).map
          ((C.integral U V h E).derived.inv.app K) = 𝟙 _ :=
    ((derivedPull l T.base.left g.hom (C.ring T U g)).mapIso
      ((C.integral U V h E).derived.app K)).hom_inv_id
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc]
  rw [hm]
  exact (Category.comp_id _).symm

end WeilConjectures.AdicQbarRealization
