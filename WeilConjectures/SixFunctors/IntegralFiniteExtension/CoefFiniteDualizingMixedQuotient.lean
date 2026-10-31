/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralFiniteExtension.CoefScalarReductionExchange
public import WeilConjectures.SixFunctors.IntegralFiniteExtension.CoefIntegralFiniteExtensionModels

import WeilConjectures.SixFunctors.Finite.Coefficient.FiniteCoefficientUnitComposition
import WeilConjectures.AlgebraicGeometry.SystemProjection.EtaleSingleCoefficientProjection
import WeilConjectures.SixFunctors.IntegralFiniteExtension.CoefFiniteRealizationRestrictionSquare
import WeilConjectures.CategoryTheory.Adjunction.SixFunctors.CoefficientCounitMateCocycle
import WeilConjectures.AlgebraicGeometry.Proper.ProperFiniteCoefficientExtension

/-! # The finite dualizing mixed quotient square

Source: current blueprint lem-coef-integral-finite-extension, paragraphs 2--3.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.IntegralFiniteExtension

private theorem adjunct_conjugate
    {A B : Type*} [Category A] [Category B]
    {T₁ T₂ : A ⥤ B} {R₁ R₂ : B ⥤ A}
    (a₁ : T₁ ⊣ R₁) (a₂ : T₂ ⊣ R₂) (α : T₂ ⟶ T₁)
    (K : A) (H : B) (f : T₁.obj K ⟶ H) :
    a₂.homEquiv K H (α.app K ≫ f) =
      a₁.homEquiv K H f ≫ (conjugateEquiv a₁ a₂ α).app H := by
  simp only [Adjunction.homEquiv_unit, Functor.map_comp, ← Category.assoc]
  rw [← unit_conjugateEquiv, Category.assoc, ← (conjugateEquiv a₁ a₂ α).naturality]
  simp only [Category.assoc]

private theorem adjunct_comp
    {A B C : Type*} [Category A] [Category B] [Category C]
    {T₁ : A ⥤ B} {R₁ : B ⥤ A} {T₂ : B ⥤ C} {R₂ : C ⥤ B}
    {T₃ : A ⥤ C} {R₃ : C ⥤ A}
    (a₁ : T₁ ⊣ R₁) (a₂ : T₂ ⊣ R₂) (a₃ : T₃ ⊣ R₃)
    (c : R₂ ⋙ R₁ ≅ R₃) {K : A} {H : B} {N : C}
    (v : T₁.obj K ⟶ H) (w : T₂.obj H ⟶ N) (z : T₃.obj K ⟶ N)
    (h : T₂.map v ≫ w = (a₁.leftAdjointCompIso a₂ a₃ c).hom.app K ≫ z) :
    a₃.homEquiv K N z ≫ c.inv.app N =
      a₁.homEquiv K H v ≫ R₁.map (a₂.homEquiv H N w) := by
  have hh := congrArg ((a₁.comp a₂).homEquiv K N) h
  rw [adjunct_conjugate a₃ (a₁.comp a₂)] at hh
  simp only [Adjunction.leftAdjointCompIso_hom, Adjunction.leftAdjointCompNatTrans,
    Equiv.apply_symm_apply] at hh
  rw [Adjunction.comp_homEquiv] at hh
  change (a₁.homEquiv K _) ((a₂.homEquiv _ _) (T₂.map v ≫ w)) = _ at hh
  rw [a₂.homEquiv_naturality_left, a₁.homEquiv_naturality_right] at hh
  exact hh.symm

-- Keep the natural transformation named while taking its component at a large object.
private theorem mixed_mate
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {T : A ⥤ B} {R : B ⥤ A} {T' : C ⥤ D} {R' : D ⥤ C}
    (a : T ⊣ R) (b : T' ⊣ R') (F : A ⥤ C) (G : B ⥤ D)
    (τ : R ⋙ F ⟶ G ⋙ R') (δ : F ⋙ T' ⟶ T ⋙ G)
    (hδ : δ = ((mateEquiv a b).symm (TwoSquare.mk _ _ _ _ τ)).natTrans)
    {K : C} {M : A} {N : B} {P : D}
    (f : K ⟶ F.obj M) (v : T.obj M ⟶ N) (w : T'.obj K ⟶ P)
    (t : P ⟶ G.obj N)
    (h : f ≫ F.map (a.homEquiv _ _ v) ≫ τ.app N =
      b.homEquiv _ _ w ≫ R'.map t) :
    b.homEquiv _ _
        (T'.map f ≫ δ.app M ≫ G.map v) =
      b.homEquiv _ _ (w ≫ t) := by
  rw [hδ]
  rw [b.homEquiv_naturality_left, b.homEquiv_naturality_right,
    b.homEquiv_naturality_right]
  rw [Adjunction.homEquiv_unit]
  have hu := unit_mateEquiv_symm a b (TwoSquare.mk _ _ _ _ τ) M
  symm at hu
  change b.unit.app (F.obj M) ≫
    R'.map (((mateEquiv a b).symm (TwoSquare.mk _ _ _ _ τ)).natTrans.app M) =
      F.map (a.unit.app M) ≫ τ.app (T.obj M) at hu
  rw [← Category.assoc, hu]
  have hn := τ.naturality v
  dsimp only [Functor.comp_map] at hn
  simp only [Category.assoc]
  rw [← hn]
  simpa only [Adjunction.homEquiv_unit, Functor.map_comp, Functor.comp_map,
    Category.assoc] using h

private theorem realize_square
    {A B C D A' B' C' D' : Type*}
    [Category A] [Category B] [Category C] [Category D]
    [Category A'] [Category B'] [Category C'] [Category D']
    (FA : A ⥤ A') (FB : B ⥤ B') (FC : C ⥤ C') (FD : D ⥤ D')
    (RAB : B ⥤ A) (RBD : D ⥤ B) (RAC : C ⥤ A) (RCD : D ⥤ C)
    (RAB' : B' ⥤ A') (RBD' : D' ⥤ B') (RAC' : C' ⥤ A') (RCD' : D' ⥤ C')
    (cAB : FB ⋙ RAB' ≅ RAB ⋙ FA) (cBD : FD ⋙ RBD' ≅ RBD ⋙ FB)
    (cAC : FC ⋙ RAC' ≅ RAC ⋙ FA) (cCD : FD ⋙ RCD' ≅ RCD ⋙ FC)
    (η : RBD ⋙ RAB ≅ RCD ⋙ RAC) (η' : RBD' ⋙ RAB' ≅ RCD' ⋙ RAC')
    {KA : A} {KB : B} {KC : C} {KD : D}
    (sAB : KA ⟶ RAB.obj KB) (sBD : KB ⟶ RBD.obj KD)
    (sAC : KA ⟶ RAC.obj KC) (sCD : KC ⟶ RCD.obj KD)
    (hs : sAB ≫ RAB.map sBD ≫ η.hom.app KD = sAC ≫ RAC.map sCD)
    (hc : FA.map (η.hom.app KD) ≫ cAC.inv.app (RCD.obj KD) ≫
        RAC'.map (cCD.inv.app KD) =
      cAB.inv.app (RBD.obj KD) ≫ RAB'.map (cBD.inv.app KD) ≫ η'.hom.app (FD.obj KD)) :
    (FA.map sAB ≫ cAB.inv.app KB) ≫
        RAB'.map (FB.map sBD ≫ cBD.inv.app KD) ≫ η'.hom.app (FD.obj KD) =
      (FA.map sAC ≫ cAC.inv.app KC) ≫ RAC'.map (FC.map sCD ≫ cCD.inv.app KD) := by
  have hnAB := cAB.inv.naturality sBD
  have hnAC := cAC.inv.naturality sCD
  dsimp only [Functor.comp_map] at hnAB hnAC
  simp only [Functor.map_comp, Category.assoc]
  rw [← Category.assoc (cAB.inv.app KB), ← hnAB]
  simp only [Category.assoc]
  rw [← hc]
  simp only [← Functor.map_comp_assoc]
  rw [hs]
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% hnAC]

private theorem conjugate_square
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    (RAB : B ⥤ A) (RBD : D ⥤ B) (RAC : C ⥤ A) (RCD : D ⥤ C)
    (η : RBD ⋙ RAB ≅ RCD ⋙ RAC)
    {KA LA : A} {KB LB : B} {KC LC : C} {KD LD : D}
    (eA : KA ≅ LA) (eB : KB ≅ LB) (eC : KC ≅ LC) (eD : KD ≅ LD)
    (sAB : KA ⟶ RAB.obj KB) (sBD : KB ⟶ RBD.obj KD)
    (sAC : KA ⟶ RAC.obj KC) (sCD : KC ⟶ RCD.obj KD)
    (hs : sAB ≫ RAB.map sBD ≫ η.hom.app KD = sAC ≫ RAC.map sCD) :
    (eA.inv ≫ sAB ≫ RAB.map eB.hom) ≫
        RAB.map (eB.inv ≫ sBD ≫ RBD.map eD.hom) ≫ η.hom.app LD =
      (eA.inv ≫ sAC ≫ RAC.map eC.hom) ≫
        RAC.map (eC.inv ≫ sCD ≫ RCD.map eD.hom) := by
  simp only [Functor.map_comp, Category.assoc]
  rw [← RAB.map_comp_assoc eB.hom eB.inv, Iso.hom_inv_id, RAB.map_id,
    Category.id_comp, ← RAC.map_comp_assoc eC.hom eC.inv, Iso.hom_inv_id,
    RAC.map_id, Category.id_comp]
  have hn := η.hom.naturality eD.hom
  dsimp only [Functor.comp_map] at hn
  rw [hn]
  simpa only [Category.assoc] using
    congrArg (fun f ↦ eA.inv ≫ f ≫ RAC.map (RCD.map eD.hom)) hs

private theorem compact_isIso
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {X S : Scheme.{u}} [IsNoetherian S] {f : X ⟶ S}
    (c : Compactification f) (K : Etale.DerivedCategoryModule A X) :
    IsIso (Etale.ExceptionalCoefficients.compactSupportMap φ c K) := by
  have : IsLocallyNoetherian c.Z := LocallyOfFiniteType.isLocallyNoetherian c.g
  have : CompactSpace c.Z := QuasiCompact.compactSpace_of_compactSpace c.g
  have : IsNoetherian c.Z := ⟨⟩
  have := (Etale.properFiniteCoefficientExtension φ c.g).1
    ((Etale.openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i).mapDerivedCategory.obj K)
  unfold Etale.ExceptionalCoefficients.compactSupportMap
  infer_instance

private theorem compact_comp
    {A B C : Type (u + 1)} [CommRing A] [CommRing B] [CommRing C]
    [Finite A] [Finite B] [Finite C]
    (φ : A →+* B) (ψ : B →+* C) (χ : A →+* C) (hχ : χ = ψ.comp φ)
    {X S : Scheme.{u}} {f : X ⟶ S} (c : Compactification f)
    (K : Etale.DerivedCategoryModule A X) :
    (Etale.scalarExtension ψ S).map
        (Etale.ExceptionalCoefficients.compactSupportMap φ c K) ≫
      Etale.ExceptionalCoefficients.compactSupportMap ψ c
        ((Etale.scalarExtension φ X).obj K) ≫
      (Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} C) c).map
        ((ProEtale.pbcFixedScalarExtensionComp X.smallEtaleTopology φ ψ χ hχ).hom.app K) =
    (ProEtale.pbcFixedScalarExtensionComp S.smallEtaleTopology φ ψ χ hχ).hom.app
        ((Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).obj K) ≫
      Etale.ExceptionalCoefficients.compactSupportMap χ c K := by
  subst χ
  have hc := (Etale.SystemProjection.etaleSingleCoefficientProjection c 0).2
    (CommRingCat.of A) (CommRingCat.of B) (CommRingCat.of C)
    inferInstance inferInstance inferInstance
    ⟨1, by simp⟩ ⟨1, by simp⟩ ⟨1, by simp⟩
    (CommRingCat.ofHom φ) (CommRingCat.ofHom ψ)
  have he := congrArg (fun z ↦
    (ProEtale.pbcFixedScalarExtensionComp S.smallEtaleTopology
      φ ψ (ψ.comp φ) rfl).hom.app
        ((Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).obj K) ≫
      z.app K) hc
  simpa only [Etale.SystemProjection.singlePath, Etale.compactScalarMap,
    NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    CommRingCat.hom_comp, CommRingCat.hom_ofHom, Functor.comp_obj,
    Category.assoc, Iso.hom_inv_id_app_assoc] using he.symm

private abbrev coefficientOmega (A : Type (u + 1)) [CommRing A] [Finite A]
    {X S : Scheme.{u}} (f : X ⟶ S) [HasCompactification f] :=
  (Etale.rightDerivedUpperShriek A f).obj
    (Etale.constantComplex A S)

private abbrev coefficientAdjunction (A : Type (u + 1)) [CommRing A] [Finite A]
    {X S : Scheme.{u}} (f : X ⟶ S) [HasCompactification f] :=
  Etale.rightDerivedUpperShriekAdjunction A f

private def coefficientU
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {X S : Scheme.{u}} (f : X ⟶ S) [HasCompactification f] :
    (Etale.scalarExtension φ X).obj (coefficientOmega A f) ⟶ coefficientOmega B f :=
  (coefficientAdjunction B f).homEquiv _ (Etale.constantComplex B S)
    (Etale.ExceptionalCoefficients.comparisonInverse φ
        (HasCompactification.compactification f) (coefficientOmega A f) ≫
      (Etale.scalarExtension φ S).map
        ((coefficientAdjunction A f).counit.app (Etale.constantComplex A S)) ≫
      (Etale.ExceptionalCoefficients.unitIso φ S).hom)

private theorem coefficientU_comp
    {A B C : Type (u + 1)} [CommRing A] [CommRing B] [CommRing C]
    [Finite A] [Finite B] [Finite C]
    (φ : A →+* B) (ψ : B →+* C) (χ : A →+* C) (hχ : χ = ψ.comp φ)
    {X S : Scheme.{u}} [IsNoetherian S] (f : X ⟶ S) [HasCompactification f] :
    (Etale.scalarExtension ψ X).map (coefficientU φ f) ≫ coefficientU ψ f =
      (ProEtale.pbcFixedScalarExtensionComp X.smallEtaleTopology φ ψ χ hχ).hom.app
          (coefficientOmega A f) ≫
        coefficientU χ f := by
  let c := HasCompactification.compactification f
  have hc := compact_comp φ ψ χ hχ c
  have hN := finiteCoefficient_unit_composition φ ψ χ hχ S
  have hiAB : IsIso ((Etale.compactScalarMap φ c).app
      (coefficientOmega A f)) := compact_isIso φ c
    (coefficientOmega A f)
  have hiBC : IsIso ((Etale.compactScalarMap ψ c).app
      (coefficientOmega B f)) := compact_isIso ψ c
    (coefficientOmega B f)
  have hiAC : IsIso ((Etale.compactScalarMap χ c).app
      (coefficientOmega A f)) := compact_isIso χ c
    (coefficientOmega A f)
  have hiBC' : IsIso ((Etale.compactScalarMap ψ c).app
      ((Etale.scalarExtension φ X).obj (coefficientOmega A f))) :=
    compact_isIso ψ c ((Etale.scalarExtension φ X).obj (coefficientOmega A f))
  have he := Adjunction.coefficientCounitMate_cocycle
    (coefficientAdjunction A f) (coefficientAdjunction B f) (coefficientAdjunction C f)
    (Etale.scalarExtension φ X) (Etale.scalarExtension φ S)
    (Etale.scalarExtension ψ X) (Etale.scalarExtension ψ S)
    (Etale.scalarExtension χ X) (Etale.scalarExtension χ S)
    (ProEtale.pbcFixedScalarExtensionComp X.smallEtaleTopology φ ψ χ hχ)
    (ProEtale.pbcFixedScalarExtensionComp S.smallEtaleTopology φ ψ χ hχ)
    (Etale.constantComplex A S) (Etale.constantComplex B S) (Etale.constantComplex C S)
    (Etale.ExceptionalCoefficients.unitIso φ S) (Etale.ExceptionalCoefficients.unitIso ψ S)
    (Etale.ExceptionalCoefficients.unitIso χ S) hN
    (Etale.compactScalarMap φ c) (Etale.compactScalarMap ψ c)
    (Etale.compactScalarMap χ c) (hc _)
  have hAB := compact_isIso φ c (coefficientOmega A f)
  have hBC := compact_isIso ψ c (coefficientOmega B f)
  have hAC := compact_isIso χ c (coefficientOmega A f)
  have he' : coefficientU χ f =
      (ProEtale.pbcFixedScalarExtensionComp X.smallEtaleTopology φ ψ χ hχ).inv.app
          (coefficientOmega A f) ≫
        (Etale.scalarExtension ψ X).map (coefficientU φ f) ≫ coefficientU ψ f := by
    simpa only [coefficientU, Etale.ExceptionalCoefficients.comparisonInverse,
      Etale.compactScalarMap, dif_pos hAB, dif_pos hBC, dif_pos hAC, c] using he
  rw [he']
  simp only [Iso.hom_inv_id_app_assoc]

private theorem coefficientU_restrict_comp
    {A B C : Type (u + 1)} [CommRing A] [CommRing B] [CommRing C]
    [Finite A] [Finite B] [Finite C]
    (φ : A →+* B) (ψ : B →+* C) (χ : A →+* C) (hχ : χ = ψ.comp φ)
    {X S : Scheme.{u}} [IsNoetherian S] (f : X ⟶ S) [HasCompactification f] :
    (Adjunction.ofIsRightAdjoint
        (Sheaf.derivedRestrictScalars X.smallEtaleTopology χ)).homEquiv _ _
        (coefficientU χ f) ≫
      (Sheaf.derivedRestrictScalarsCompIso X.smallEtaleTopology hχ).inv.app
        (coefficientOmega C f) =
    (Adjunction.ofIsRightAdjoint
        (Sheaf.derivedRestrictScalars X.smallEtaleTopology φ)).homEquiv _ _
        (coefficientU φ f) ≫
      (Sheaf.derivedRestrictScalars X.smallEtaleTopology φ).map
        ((Adjunction.ofIsRightAdjoint
          (Sheaf.derivedRestrictScalars X.smallEtaleTopology ψ)).homEquiv _ _
          (coefficientU ψ f)) := by
  exact adjunct_comp
    (Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars X.smallEtaleTopology φ))
    (Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars X.smallEtaleTopology ψ))
    (Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars X.smallEtaleTopology χ))
    (Sheaf.derivedRestrictScalarsCompIso X.smallEtaleTopology hχ)
    (coefficientU φ f) (coefficientU ψ f) (coefficientU χ f)
    (coefficientU_comp φ ψ χ hχ f)

private theorem coefficientU_restrict_square
    {A B C V : Type (u + 1)}
    [CommRing A] [CommRing B] [CommRing C] [CommRing V]
    [Finite A] [Finite B] [Finite C] [Finite V]
    (qA : A →+* B) (iB : B →+* V) (iA : A →+* C) (qB : C →+* V)
    (hq : qB.comp iA = iB.comp qA)
    {X S : Scheme.{u}} [IsNoetherian S] (f : X ⟶ S) [HasCompactification f] :
    (Adjunction.ofIsRightAdjoint
        (Sheaf.derivedRestrictScalars X.smallEtaleTopology qA)).homEquiv _ _
        (coefficientU qA f) ≫
      (Sheaf.derivedRestrictScalars X.smallEtaleTopology qA).map
        ((Adjunction.ofIsRightAdjoint
          (Sheaf.derivedRestrictScalars X.smallEtaleTopology iB)).homEquiv _ _
          (coefficientU iB f)) ≫
      ((Sheaf.derivedRestrictScalarsCompIso X.smallEtaleTopology hq) ≪≫
        (Sheaf.derivedRestrictScalarsCompIso X.smallEtaleTopology
          (rfl : qB.comp iA = qB.comp iA)).symm).hom.app
        (coefficientOmega V f) =
    (Adjunction.ofIsRightAdjoint
        (Sheaf.derivedRestrictScalars X.smallEtaleTopology iA)).homEquiv _ _
        (coefficientU iA f) ≫
      (Sheaf.derivedRestrictScalars X.smallEtaleTopology iA).map
        ((Adjunction.ofIsRightAdjoint
          (Sheaf.derivedRestrictScalars X.smallEtaleTopology qB)).homEquiv _ _
          (coefficientU qB f)) := by
  rw [← Category.assoc, ← coefficientU_restrict_comp qA iB (qB.comp iA) hq f,
    ← coefficientU_restrict_comp iA qB (qB.comp iA) rfl f]
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Category.assoc,
    Iso.inv_hom_id_app_assoc]

variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (L : Type u) [Field L] [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
  (ι : E →ₐ[Padic l] L) (X : Scheme.{u})
  (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)

variable [X.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
  [QuasiCompact (X ↘ Spec (.of D.k))] [IsSeparated (X ↘ Spec (.of D.k))]

private theorem finiteCoefficient_square {m n : ℕ} (h : n ≤ m) :
    (finiteDualizingQuotient l L h).comp
        (RingHom.ulift.{u + 1, u + 1} (integralScalarQuotientMap l E L ι m)) =
      (RingHom.ulift.{u + 1, u + 1} (integralScalarQuotientMap l E L ι n)).comp
        (finiteDualizingQuotient l E h) := by
  apply RingHom.ext
  intro ⟨x⟩
  induction x using Quotient.inductionOn' with
  | h x => rfl

private theorem finite_restricted_square {m n : ℕ} (h : n ≤ m) :
    integralDualizingExceptionalTransition l E D X hl h ≫
        (normalizedDVRRes l E X h).map
          ((pbcDerivedScalarAdjunction
            (integralScalarQuotientSheafMap l E L ι X n)).homEquiv _ _
              (finiteU l E L ι X D n)) ≫
        (scalarRestrictionSquare l E L ι X h).hom.app
          (integralDualizingFiniteTerm l L D X n) =
      (pbcDerivedScalarAdjunction
          (integralScalarQuotientSheafMap l E L ι X m)).homEquiv _ _
          (finiteU l E L ι X D m) ≫
        (pbcDerivedRestrict (integralScalarQuotientSheafMap l E L ι X m)).map
          (integralDualizingExceptionalTransition l L D X hl h) := by
  let qE := finiteDualizingQuotient l E h
  let qL := finiteDualizingQuotient l L h
  let iM := RingHom.ulift.{u + 1, u + 1} (integralScalarQuotientMap l E L ι m)
  let iN := RingHom.ulift.{u + 1, u + 1} (integralScalarQuotientMap l E L ι n)
  let R (A B : Type (u + 1)) [CommRing A] [CommRing B] (φ : A →+* B) :=
    Sheaf.derivedRestrictScalars X.smallEtaleTopology φ
  let a (A B : Type (u + 1)) [CommRing A] [CommRing B] (φ : A →+* B) :=
    Adjunction.ofIsRightAdjoint (R A B φ)
  have hq := finiteCoefficient_square l E L ι h
  let η := (Sheaf.derivedRestrictScalarsCompIso X.smallEtaleTopology hq) ≪≫
    (Sheaf.derivedRestrictScalarsCompIso X.smallEtaleTopology
      (rfl : qL.comp iM = qL.comp iM)).symm
  let sN := (a _ _ iN).homEquiv _ _ (finiteEtaleU l E L ι X D n)
  let sM := (a _ _ iM).homEquiv _ _ (finiteEtaleU l E L ι X D m)
  let := (finiteDualizingCompactification D X).hasCompactification
  have hs := coefficientU_restrict_square qE iN iM qL hq (X ↘ Spec (.of D.k))
  change finiteDualizingEtaleTransition l E D X h ≫ (R _ _ qE).map sN ≫
      η.hom.app (finiteDualizingEtaleTerm l L D X n) =
    sM ≫ (R _ _ iM).map (finiteDualizingEtaleTransition l L D X h) at hs
  have hr := realize_square
    (finiteDualizingRealization l E X m) (finiteDualizingRealization l E X n)
    (finiteDualizingRealization l L X m) (finiteDualizingRealization l L X n)
    (R _ _ qE) (R _ _ iN) (R _ _ iM) (R _ _ qL)
    (normalizedDVRRes l E X h)
    (pbcDerivedRestrict (integralScalarQuotientSheafMap l E L ι X n))
    (pbcDerivedRestrict (integralScalarQuotientSheafMap l E L ι X m))
    (normalizedDVRRes l L X h)
    (finiteDualizingRealizationRestriction l E X h)
    (finiteRealizationRestriction l E L ι X n)
    (finiteRealizationRestriction l E L ι X m)
    (finiteDualizingRealizationRestriction l L X h)
    η (scalarRestrictionSquare l E L ι X h)
    (finiteDualizingEtaleTransition l E D X h) sN sM
    (finiteDualizingEtaleTransition l L D X h) hs
    (finiteRealization_restriction_square l E L ι X h hq
      (finiteDualizingEtaleTerm l L D X n))
  have hr' := conjugate_square
    (normalizedDVRRes l E X h)
    (pbcDerivedRestrict (integralScalarQuotientSheafMap l E L ι X n))
    (pbcDerivedRestrict (integralScalarQuotientSheafMap l E L ι X m))
    (normalizedDVRRes l L X h) (scalarRestrictionSquare l E L ι X h)
    (finiteDualizingOrigin l E D X m) (finiteDualizingOrigin l E D X n)
    (finiteDualizingOrigin l L D X m) (finiteDualizingOrigin l L D X n)
    _ _ _ _ hr
  simpa only [finiteU, integralDualizingExceptionalTransition, Equiv.apply_symm_apply,
    sN, sM, a, R, Category.assoc] using hr'

/-- The scalar adjuncts of the two finite dualizing mixed quotient paths agree.
Source: lem-coef-integral-finite-extension, quotient compatibility, paragraphs 2--3.
(blueprint: lem-sf-finite-dualizing-mixed-quotient-mate)

Proof: on the ordinary etale site the lifted ring square commutes by quotient
induction. The existing proper/open coefficient-chain theorem proves compact-support
composition. Proper finite coefficient extension makes the comparison components
invertible. Combine this composition with the normalized scalar-unit composition
law, and apply the coefficient counit-mate cocycle to obtain exceptional coefficient
composition. Taking scalar adjuncts gives the ordinary semilinear restriction square.
The coefficient-only realization restriction-square law transports that square to
the intrinsic categories. Conjugating by the four finiteDualizingOrigin isomorphisms
cancels their middle inverse pairs, giving finiteU and the actual exceptional
transitions. Finally, the unit equation for the mate of scalarRestrictionSquare
identifies the left boundary with the adjunct of the displayed mixed map.
No invertibility of scalarReductionExchange is needed. -/
theorem finiteU_quotient_transition_mate {m n : ℕ} (h : n ≤ m) :
    (pbcDerivedScalarAdjunction
      (integralScalarQuotientSheafMap l E L ι X m)).homEquiv _ _
      ((pbcDerivedExtend (integralScalarQuotientSheafMap l E L ι X m)).map
          (integralDualizingExceptionalTransition l E D X hl h) ≫
        (scalarReductionExchange l E L ι X h).app
          (integralDualizingFiniteTerm l E D X n) ≫
        (normalizedDVRRes l L X h).map
          (finiteU l E L ι X D n)) =
    (pbcDerivedScalarAdjunction
      (integralScalarQuotientSheafMap l E L ι X m)).homEquiv _ _
      (finiteU l E L ι X D m ≫
        integralDualizingExceptionalTransition l L D X hl h) := by
  apply mixed_mate
    (pbcDerivedScalarAdjunction (integralScalarQuotientSheafMap l E L ι X n))
    (pbcDerivedScalarAdjunction (integralScalarQuotientSheafMap l E L ι X m))
    (normalizedDVRRes l E X h) (normalizedDVRRes l L X h)
    (scalarRestrictionSquare l E L ι X h).hom
    (scalarReductionExchange l E L ι X h) rfl
    (K := integralDualizingFiniteTerm l E D X m)
    (M := integralDualizingFiniteTerm l E D X n)
    (N := integralDualizingFiniteTerm l L D X n)
    (P := integralDualizingFiniteTerm l L D X m)
    (integralDualizingExceptionalTransition l E D X hl h)
    (finiteU l E L ι X D n) (finiteU l E L ι X D m)
    (integralDualizingExceptionalTransition l L D X hl h)
  exact finite_restricted_square l E L ι X D hl h

/-- Cross-field finite dualizing counit maps commute with the actual exceptional
quotient transitions through the mixed scalar/quotient map.
Source: lem-coef-integral-finite-extension, quotient compatibility, paragraphs 2--3.
(blueprint: lem-sf-finite-dualizing-mixed-quotient)

Proof: the scalar-adjunction hom equivalence at level m is injective. The mate
calculation finiteU_quotient_transition_mate identifies the images of the two paths. -/
theorem finiteU_quotient_transition {m n : ℕ} (h : n ≤ m) :
    (pbcDerivedExtend (integralScalarQuotientSheafMap l E L ι X m)).map
        (integralDualizingExceptionalTransition l E D X hl h) ≫
      (scalarReductionExchange l E L ι X h).app (integralDualizingFiniteTerm l E D X n) ≫
      (normalizedDVRRes l L X h).map (finiteU l E L ι X D n) =
    finiteU l E L ι X D m ≫ integralDualizingExceptionalTransition l L D X hl h := by
  apply Equiv.injective ((pbcDerivedScalarAdjunction
    (integralScalarQuotientSheafMap l E L ι X m)).homEquiv _ _)
  exact finiteU_quotient_transition_mate l E L ι X D hl h

end WeilConjectures.IntegralFiniteExtension
