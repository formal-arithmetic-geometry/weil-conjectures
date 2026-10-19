/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NP
-/
module
public import Sheaf.Paper.OrdinaryCompactCohomology
public import Sheaf.Paper.CompactSupportCoefficientAction
public import Sheaf.Paper.SfDerivedDirectImage
public import Sheaf.AlgebraicGeometry.ProEtaleConstantDerivedDirectImage
public import Sheaf.Paper.SfIntegralReductionTower
public import Sheaf.Paper.DerivedScalarExtensionRestrictionAdjunction
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import WeilConjectures.Compactification.RefinementCategory
import Sheaf.AlgebraicGeometry.SfIntrinsicCompactSupport
import Sheaf.Paper.CompactificationCoherence
import Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients
import Sheaf.Paper.QcqsCompactSupportRealization
import Sheaf.AlgebraicGeometry.SfOpenExceptionalBaseChange
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Proper
import Sheaf.Paper.FiniteDirectImageComposition
import Sheaf.Paper.FieldShriekCompositionQcqs
import Sheaf.Paper.CompactSupportFiniteFieldIndependence
import Sheaf.Paper.SystemOperationExchangeRealization
/-!
# Proper coincidence of compact-support and ordinary cohomology

Source: literature/blueprint/main-20261015/blueprint/sec-zeta-weil/sk-input-weights/
prop-weil-proper-compact-coincidence.md (blueprint: prop-weil-proper-compact-coincidence).

## Main statements

* `WeilConjectures.properCompactPointOver`: the identity structure morphism on the point.
* `WeilConjectures.properCompactCoincidence`: proper comparison for all four coefficients.
-/
@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures
open AlgebraicallyClosedCoefficients (Coefficient)

/-- The point has its identity structure morphism over the fixed geometric field.
Source: blueprint structure morphism a_Y and its point s = Spec k
(blueprint: prop-weil-proper-compact-coincidence). -/
instance properCompactPointOver (D : FiniteFieldDatum.{u}) :
    (Spec (CommRingCat.of D.k)).Over (Spec (CommRingCat.of D.k)) :=
  ⟨𝟙 _⟩

private def properCompactSheafId (X : Scheme.{u}) :
    proEtaleSheafDirectImage (𝟙 X) CommRingCat.{u + 1} ≅ 𝟭 _ :=
  Functor.sheafPushforwardContinuousId'
    (MorphismProperty.Over.pullbackId (P := @WeaklyEtale) (Q := ⊤) X)
    CommRingCat.{u + 1} (ProEt.topology X)

private theorem properCompactConstantId (X : Scheme.{u}) (A : Type u) [CommRing A] :
    proEtaleCoefficientDirectImageMap (𝟙 X) A =
      (properCompactSheafId X).inv.app (proEtaleConstantRing X A) := by
  apply ((sheafificationAdjunction (ProEt.topology X) CommRingCat.{u + 1}).homEquiv
    _ _).injective
  refine ((sheafificationAdjunction (ProEt.topology X) CommRingCat.{u + 1}).homEquiv
    _ _ |>.apply_symm_apply _).trans ?_
  apply NatTrans.ext
  funext U
  change (toSheafify (ProEt.topology X)
    ((Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{u + 1, u} A)))).app
      ((proEtaleBaseChange (𝟙 X)).op.obj U) = _
  change _ = (toSheafify (ProEt.topology X)
    ((Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{u + 1, u} A)))).app U ≫
      (proEtaleConstantRing X A).obj.map
        ((MorphismProperty.Over.pullbackId (P := @WeaklyEtale) (Q := ⊤) X).hom.app U.unop).op
  have h := (toSheafify (ProEt.topology X)
    ((Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{u + 1, u} A)))).naturality
      ((MorphismProperty.Over.pullbackId (P := @WeaklyEtale) (Q := ⊤) X).hom.app U.unop).op
  dsimp only [Functor.const_obj_map, Functor.id_obj] at h
  erw [Category.id_comp] at h
  exact h

private theorem properCompactCompletedPush_eq
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] {X Z : Scheme.{u}} (f : X ⟶ Z) :
    proEtaleRingModuleDirectImage f
        ((PurCompactSupport.completed l E).ring Z)
        ((PurCompactSupport.completed l E).ring X)
        ((PurCompactSupport.completed l E).pull f) = sfCompletedModuleDirectImage l E f := by
  have h : proEtaleRingDirectImageMap f
      ((PurCompactSupport.completed l E).ring Z)
      ((PurCompactSupport.completed l E).ring X)
      ((PurCompactSupport.completed l E).pull f) = sfCompletedCoefficientMap l E f :=
    (proEtaleSheafAdjunction f CommRingCat.{u + 1}).homEquiv _ _
      |>.apply_symm_apply (sfCompletedCoefficientMap l E f)
  unfold proEtaleRingModuleDirectImage sfCompletedModuleDirectImage
  rw [h]

private theorem properCompactCompletedMapId
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (X : Scheme.{u}) :
    sfCompletedCoefficientMap l E (𝟙 X) =
      (properCompactSheafId X).inv.app (completedIntegralCommRingSheafUnrestricted l E X) := by
  apply (sfCompletedCoefficientMap_existsUnique l E (𝟙 X)).unique
    (sfCompletedCoefficientMap_existsUnique l E (𝟙 X)).exists.choose_spec
  intro n
  rw [properCompactConstantId]
  exact ((properCompactSheafId X).inv.naturality _).symm

private def properCompactCompletedPushId
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (X : Scheme.{u}) :
    sfCompletedModuleDirectImage l E (𝟙 X) ≅ 𝟭 _ := by
  let : (𝟭 (MorphismProperty.Over @WeaklyEtale ⊤ X)).IsContinuous
      (ProEt.topology X) (ProEt.topology X) := Functor.isContinuous_id _
  let A := (sheafCompose (ProEt.topology X)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
      (completedIntegralCommRingSheafUnrestricted l E X)
  let e := MorphismProperty.Over.pullbackId (P := @WeaklyEtale) (Q := ⊤) X
  let t : A ⟶ ((proEtaleBaseChange (𝟙 X)).sheafPushforwardContinuous
      RingCat.{u + 1} (ProEt.topology X) (ProEt.topology X)).obj A :=
    ⟨Functor.whiskerRight (sfCompletedCoefficientMap l E (𝟙 X)).hom
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})⟩
  have ht : t ≫ (Functor.sheafPushforwardContinuousNatTrans e.inv _ _ _).app A = 𝟙 A := by
    dsimp only [t]
    rw [properCompactCompletedMapId]
    ext U x
    change ((completedIntegralCommRingSheafUnrestricted l E X).obj.map
      (e.hom.app U.unop).op ≫ (completedIntegralCommRingSheafUnrestricted l E X).obj.map
        (e.inv.app U.unop).op) x = x
    rw [← Functor.map_comp, ← CategoryTheory.op_comp, Iso.inv_hom_id_app,
      CategoryTheory.op_id]
    have h := (completedIntegralCommRingSheafUnrestricted l E X).obj.map_id U
    exact congrArg (fun q ↦ q.hom x) h
  exact SheafOfModules.pushforwardCongr₂ (φ := t) e.symm ht ≪≫
    SheafOfModules.pushforwardId A

private def properCompactCompletedOpenId
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (X : Scheme.{u}) :
    (PurCompactSupport.openExtension (PurCompactSupport.completed l E) (𝟙 X)).mapDerivedCategory
      ≅ 𝟭 _ := by
  let h := (proEtaleRingModuleAdjunction (𝟙 X)
    ((PurCompactSupport.completed l E).ring X) ((PurCompactSupport.completed l E).ring X)
      ((PurCompactSupport.completed l E).pull (𝟙 X))).leftAdjointIdIso
        (eqToIso (properCompactCompletedPush_eq l E (𝟙 X)) ≪≫
          properCompactCompletedPushId l E X)
  exact Functor.mapDerivedCategoryNatIso
    ((PurCompactSupport.openAdjunction (PurCompactSupport.completed l E) (𝟙 X)).leftAdjointIdIso h)
      ≪≫ Functor.mapDerivedCategoryIdIso _


private def properCompactFiniteIso (A : Type u) [CommRing A] [Finite A]
    {X Z : Scheme.{u}} (f : X ⟶ Z) [IsProper f] (c : Compactification f) :
    sfIntrinsicCompactSupport c A ≅ proEtaleConstantDerivedDirectImage f A := by
  let M := ModuleCat.{u + 1} (ULift.{u + 1, u} A)
  have : IsIso (ProEtale.openImmersionLowerShriekToLowerStar M c.i) :=
    ProEtale.isIso_openImmersionLowerShriekToLowerStar_of_isClosed_range M c.i
      (c.isClopen_range_openImmersion inferInstance).isClosed
  have : (ProEtale.lowerStar M c.i).PreservesKInjectiveComplexes :=
    (ProEtale.upperStarLowerStarAdjunction M c.i).preservesKInjectiveComplexes
  have : (ProEtale.openImmersionLowerShriek M c.i).PreservesKInjectiveComplexes :=
    Functor.preservesKInjectiveComplexes_of_iso
      (asIso (ProEtale.openImmersionLowerShriekToLowerStar M c.i)).symm
  have : PreservesFiniteColimits (ProEtale.lowerStar M c.i) :=
    preservesFiniteColimits_of_natIso
      (asIso (ProEtale.openImmersionLowerShriekToLowerStar M c.i))
  let fixed : ProEtale.sfFixedCompactSupport A c ≅
      (ProEtale.lowerStar M f).rightDerivedFunctor :=
    Functor.isoWhiskerRight
        (Functor.mapDerivedCategoryNatIso
          (asIso (ProEtale.openImmersionLowerShriekToLowerStar M c.i)) ≪≫
            (ProEtale.lowerStar M c.i).rightDerivedFunctorIsoMapDerivedCategory.symm) _ ≪≫
      (ProEtale.finiteDirectImageComposition _ c.i c.g).symm ≪≫
      (eqToIso (congrArg (fun g ↦ (ProEtale.lowerStar M g).rightDerivedFunctor)
        c.comm.symm))
  let e := sfIntrinsicDerivedEquivalence X A
  let R := proEtaleConstantDerivedDirectImage f A
  let F := sfIntrinsicCompactSupport c A
  let comparison : e.functor ⋙ F ≅ e.functor ⋙ R :=
    ProEtale.sfIntrinsicCompactSupportComparison A c ≪≫
      Functor.isoWhiskerRight fixed (sfIntrinsicDerivedEquivalence Z A).functor ≪≫
        (sfIntrinsicDerivedDirectImageComparison f A).symm
  exact (Functor.leftUnitor F).symm ≪≫
    Functor.isoWhiskerRight e.counitIso.symm F ≪≫ Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft e.inverse comparison ≪≫ (Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight e.counitIso R ≪≫ Functor.leftUnitor R

private theorem properCompactIntegralChange
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (Y : Scheme.{u}) [Y.Over (Spec (.of D.k))]
    [IsProper (Y ↘ Spec (.of D.k))]
    (c d : Compactification (Y ↘ Spec (.of D.k))) :
    Nonempty (sfCompactSupportFiniteIntegralFunctor l D.k
        (finiteFieldDatumPrimeUnit D l hl) c E ≅
      sfCompactSupportFiniteIntegralFunctor l D.k (finiteFieldDatumPrimeUnit D l hl) d E) := by
  let ci := Compactification.ofIsProper (𝟙 Y)
  have comparison (g : Y ⟶ Spec (.of D.k)) [g.IsOver (Spec (.of D.k))]
      [IsProper g] (h : 𝟙 Y ≫ (Y ↘ Spec (.of D.k)) = g)
      (a b : Compactification g) :
      Nonempty (sfCompactSupportFiniteIntegralFunctor l D.k
          (finiteFieldDatumPrimeUnit D l hl) a E ≅
        sfCompactSupportFiniteIntegralFunctor l D.k (finiteFieldDatumPrimeUnit D l hl) b E) := by
    subst g
    exact ⟨(sfFieldShriekCompositionIntegral D l hl ci c a E).symm ≪≫
      sfFieldShriekCompositionIntegral D l hl ci c b E⟩
  exact comparison _ (Category.id_comp _) c d

private theorem properCompactIntegralFunctor
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (Y : Scheme.{u}) [Y.Over (Spec (.of D.k))]
    [IsProper (Y ↘ Spec (.of D.k))]
    (c : Compactification (Y ↘ Spec (.of D.k))) :
    Nonempty (sfCompactSupportFiniteIntegralFunctor l D.k
        (finiteFieldDatumPrimeUnit D l hl) c E ⋙
          (sfIntegralConstructible l E (Spec (.of D.k))).ι ≅
      (sfIntegralConstructible l E Y).ι ⋙
        sfCompletedDerivedDirectImage l E (Y ↘ Spec (.of D.k))) := by
  let f := Y ↘ Spec (.of D.k)
  let c₀ := Compactification.ofIsProper f
  obtain ⟨e⟩ := properCompactIntegralChange D l hl E Y c c₀
  let direct := proEtaleRingModuleDirectImage f
    ((PurCompactSupport.completed l E).ring (Spec (.of D.k)))
    ((PurCompactSupport.completed l E).ring Y) ((PurCompactSupport.completed l E).pull f)
  have : (sfCompletedModuleDirectImage l E f).Additive :=
    sfCompletedModuleDirectImage_additive l E f
  let derivedIso : direct.rightDerivedFunctor ≅ sfCompletedDerivedDirectImage l E f :=
    Functor.rightDerivedFunctorNatIso (eqToIso (properCompactCompletedPush_eq l E f))
  let ambient : PurCompactSupport.image (PurCompactSupport.completed l E) c₀ ≅
      sfCompletedDerivedDirectImage l E f :=
    Functor.isoWhiskerRight (properCompactCompletedOpenId l E Y) direct.rightDerivedFunctor ≪≫
      Functor.leftUnitor direct.rightDerivedFunctor ≪≫ derivedIso
  exact ⟨Functor.isoWhiskerRight e (sfIntegralConstructible l E (Spec (.of D.k))).ι ≪≫
    (sfQcqsCompactSupportRealization l E D.k (finiteFieldDatumPrimeUnit D l hl) c₀).symm ≪≫
      Functor.isoWhiskerLeft (sfIntegralConstructible l E Y).ι ambient⟩

private theorem properCompactRationalChange
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (Y : Scheme.{u}) [Y.Over (Spec (.of D.k))]
    [IsProper (Y ↘ Spec (.of D.k))]
    (c d : Compactification (Y ↘ Spec (.of D.k))) :
    Nonempty (sfCompactSupportFiniteFunctor l D.k
        (finiteFieldDatumPrimeUnit D l hl) c E ≅
      sfCompactSupportFiniteFunctor l D.k (finiteFieldDatumPrimeUnit D l hl) d E) := by
  let ci := Compactification.ofIsProper (𝟙 Y)
  have comparison (g : Y ⟶ Spec (.of D.k)) [g.IsOver (Spec (.of D.k))]
      [IsProper g] (h : 𝟙 Y ≫ (Y ↘ Spec (.of D.k)) = g)
      (a b : Compactification g) :
      Nonempty (sfCompactSupportFiniteFunctor l D.k
          (finiteFieldDatumPrimeUnit D l hl) a E ≅
        sfCompactSupportFiniteFunctor l D.k (finiteFieldDatumPrimeUnit D l hl) b E) := by
    subst g
    exact ⟨(sfFieldShriekCompositionRational D l hl ci c a E).symm ≪≫
      sfFieldShriekCompositionRational D l hl ci c b E⟩
  exact comparison _ (Category.id_comp _) c d

private theorem properCompactQbarChange
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (Ω : Type u) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    (Y : Scheme.{u}) [Y.Over (Spec (.of D.k))]
    [IsProper (Y ↘ Spec (.of D.k))]
    (c d : Compactification (Y ↘ Spec (.of D.k)))
    (S : SfCompactSupportCoefficientAction l D.k (finiteFieldDatumPrimeUnit D l hl) Ω c)
    (T : SfCompactSupportCoefficientAction l D.k (finiteFieldDatumPrimeUnit D l hl) Ω d) :
    Nonempty (S.system.functor ≅ T.system.functor) := by
  let ci := Compactification.ofIsProper (𝟙 Y)
  obtain ⟨Si, _⟩ := sfCompactSupportFiniteFieldIndependence l D.k
    (finiteFieldDatumPrimeUnit D l hl) Ω ci
  have comparison (g : Y ⟶ Spec (.of D.k)) [g.IsOver (Spec (.of D.k))]
      [IsProper g] (h : 𝟙 Y ≫ (Y ↘ Spec (.of D.k)) = g)
      (a b : Compactification g)
      (Sa : SfCompactSupportCoefficientAction l D.k (finiteFieldDatumPrimeUnit D l hl) Ω a)
      (Sb : SfCompactSupportCoefficientAction l D.k (finiteFieldDatumPrimeUnit D l hl) Ω b) :
      Nonempty (Sa.system.functor ≅ Sb.system.functor) := by
    subst g
    exact ⟨(sfFieldShriekCompositionQbar_existsUnique D l hl ci c a Ω Si S Sa).exists.choose.symm ≪≫
      (sfFieldShriekCompositionQbar_existsUnique D l hl ci c b Ω Si S Sb).exists.choose⟩
  exact comparison _ (Category.id_comp _) c d S T

private theorem properCompactIntegralValue
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (Y : Scheme.{u}) [Y.Over (Spec (.of D.k))]
    [IsProper (Y ↘ Spec (.of D.k))]
    (c : Compactification (Y ↘ Spec (.of D.k)))
    (K : sfIntegralConstructibleCategory l E Y) :
    Nonempty (sfIntegralCompactSupportValue l E D.k (finiteFieldDatumPrimeUnit D l hl) c K ≅
      integralImage D l hl E Y K) := by
  let : ∀ x : Y, Invertible (l : Y.residueField x) := fun x ↦
    (show IsUnit (l : Y.residueField x) by
      simpa using (finiteFieldDatumPrimeUnit D l hl).map
        ((Y ↘ Spec (.of D.k)).residueFieldAlgebraMap x)).invertible
  let : ∀ x : Spec (.of D.k), Invertible (l : (Spec (.of D.k)).residueField x) := fun x ↦
    (show IsUnit (l : (Spec (.of D.k)).residueField x) by
      simpa using (finiteFieldDatumPrimeUnit D l hl).map
        ((Spec (.of D.k) ↘ Spec (.of D.k)).residueFieldAlgebraMap x)).invertible
  let f := Y ↘ Spec (.of D.k)
  let c₀ := Compactification.ofIsProper f
  obtain ⟨e⟩ := properCompactIntegralChange D l hl E Y c c₀
  let openId : FrobeniusExchange.systemDerivedOpen l E (𝟙 Y) ≅ 𝟭 _ :=
    ((FrobeniusExchange.systemDerivedOpenAdjunction l E (𝟙 Y)).ofNatIsoRight
      (integralComparisonSystemUnit l E Y)).leftAdjointUniq Adjunction.id
  let ambient := FrobeniusExchange.compactRealization l E D.k
    (finiteFieldDatumPrimeUnit D l hl) f c₀ ≪≫
      Functor.isoWhiskerLeft (sfIntegralConstructible l E Y).ι
        (Functor.isoWhiskerRight
          (Functor.isoWhiskerLeft (FrobeniusExchange.reduction l E Y)
            (Functor.isoWhiskerRight openId (FrobeniusExchange.systemDirect l E f) ≪≫
              Functor.leftUnitor _))
          (coefficientSequenceLimit l E (Spec (.of D.k))))
  obtain ⟨hp, M, hM⟩ := FrobeniusExchange.directImage_roos l E D.k
    (finiteFieldDatumPrimeUnit D l hl) f K
  let : HasProduct (sfDirectImageTerm l E f K.obj) := hp
  have hordinary : IsDerivedLimit (sfDirectImageTransition l E f K.obj)
      (integralImage D l hl E Y K).obj := by
    let h := sfIntegralDirectImage_constructible D.k l (finiteFieldDatumPrimeUnit D l hl)
      E f K.obj K.property
    exact ⟨_, _, h.1.choose_spec.some.roos⟩
  obtain ⟨q⟩ := (exists_isDerivedLimit_and_iso (sfDirectImageTerm l E f K.obj)
    (sfDirectImageTransition l E f K.obj)).2 M.obj (integralImage D l hl E Y K).obj
      ⟨M.projection, M.boundary, M.roos⟩ hordinary
  refine ⟨(eqToIso (sfCompactSupportFiniteIntegralFunctor_obj l D.k
    (finiteFieldDatumPrimeUnit D l hl) c E K)).symm ≪≫ e.app K ≪≫ ?_⟩
  exact ObjectProperty.isoMk _ (ambient.app K ≪≫ (eqToIso hM).symm ≪≫ q)

private theorem properCompactRationalValue
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (Y : Scheme.{u}) [Y.Over (Spec (.of D.k))]
    [IsProper (Y ↘ Spec (.of D.k))]
    (c : Compactification (Y ↘ Spec (.of D.k)))
    (K : sfRationalConstructibleCategory l E Y) :
    Nonempty (sfRationalCompactSupportValue l E D.k (finiteFieldDatumPrimeUnit D l hl) c K.obj ≅
      rationalImage D l hl E Y K) := by
  obtain ⟨e⟩ := properCompactIntegralValue D l hl E Y c K.obj
  exact ⟨(sfRationalConstructibleLocalization l E (Spec (.of D.k))).mapIso e⟩

/-- For a proper structure morphism over the geometric field of the finite-field
datum, compact-support and ordinary direct images agree for finite, integral,
rational, and algebraically closed coefficients. Their sections and cohomology
objects are consequently isomorphic for every bounded constructible input.
For rational and algebraically closed coefficients the ordinary functor is
represented by the compact-support formula at the identity compactification;
the algebraically closed clause holds for every normalized coefficient action at
`c` and at the identity compactification, not only for some choice of them;
the image clauses also compare with the recorded ordinary tower values.

Source: literature/blueprint/main-20261015/blueprint/sec-zeta-weil/sk-input-weights/
prop-weil-proper-compact-coincidence.proof.md (blueprint: prop-weil-proper-compact-coincidence).
Proof: (1) Use the finite-field and coefficient data of
`def-weil-ordinary-compact-cohomology`; properness of the structure morphism is
`def-weil-proper-morphism`.  The identity compactification is supplied by
`def-weil-compactifications-refinements`.  For its identity open immersion,
`def-weil-extension-by-zero` identifies extension by zero with the identity,
so `def-compact-support-direct-image-detailed` gives the finite-level direct-image
isomorphism.  The etale-origin and compactification-coherence clauses are those
of `lem-sf-proetale-constructible-origin` and
`prop-compactification-coherence-detailed`.
(2) For integral coefficients, `def-weil-integral-rational-qbar-compact-support`
and `def-weil-derived-direct-image` give the two towers.  Their terms and
transition maps agree by `lem-sf-compact-support-restriction-of-scalars`, since
the identity extension is literally the identity.
(3) Localization through `def-weil-rationalization-karoubi` preserves the
comparison, and `def-weil-algebraically-closed-coefficients` transports it to
common finite stages, yielding the rational and algebraically closed clauses.
(4) Applying the geometric-point fibre and degreewise cohomology in
`def-weil-ordinary-compact-cohomology` gives each displayed cohomology
isomorphism, naturally in the input and in the degree.
-/
theorem properCompactCoincidence
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (Ω : Type u) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    (E₀ : Padic.FiniteCoefficientFields l Ω) (Y : Scheme.{u})
    [Y.Over (Spec (CommRingCat.of D.k))]
    [IsProper (Y ↘ Spec (CommRingCat.of D.k))]
    (c : Compactification (Y ↘ Spec (CommRingCat.of D.k)))
    (n : ℕ) (hn : 1 ≤ n) :
    Nonempty ((intrinsicFiniteTorsionConstructible l (Coefficient.{u} l Ω E₀)
        n hn Y).ι ⋙ @sfIntrinsicCompactSupport Y (Spec (CommRingCat.of D.k))
          (Y ↘ Spec (CommRingCat.of D.k)) c
          (Padic.coefficientExtensionRing l (Coefficient.{u} l Ω E₀) n)
          _ (Padic.finite_coefficientExtensionRing l (Coefficient.{u} l Ω E₀) n hn) ≅
      (intrinsicFiniteTorsionConstructible l (Coefficient.{u} l Ω E₀) n hn Y).ι ⋙
        proEtaleConstantDerivedDirectImage (Y ↘ Spec (CommRingCat.of D.k))
          (Padic.coefficientExtensionRing l (Coefficient.{u} l Ω E₀) n)) ∧
    Nonempty (sfCompactSupportFiniteIntegralFunctor l D.k (finiteFieldDatumPrimeUnit D l hl)
        c (Coefficient.{u} l Ω E₀) ⋙
          (sfIntegralConstructible l (Coefficient.{u} l Ω E₀) (Spec (.of D.k))).ι ≅
      (sfIntegralConstructible l (Coefficient.{u} l Ω E₀) Y).ι ⋙
        sfCompletedDerivedDirectImage l (Coefficient.{u} l Ω E₀) (Y ↘ Spec (.of D.k))) ∧
    Nonempty (sfCompactSupportFiniteFunctor l D.k (finiteFieldDatumPrimeUnit D l hl)
        c (Coefficient.{u} l Ω E₀) ≅
      sfCompactSupportFiniteFunctor l D.k (finiteFieldDatumPrimeUnit D l hl)
        (Compactification.ofIsProper (Y ↘ Spec (.of D.k))) (Coefficient.{u} l Ω E₀)) ∧
    (∀ S : SfCompactSupportCoefficientAction l D.k (finiteFieldDatumPrimeUnit D l hl) Ω c,
      ∀ S₀ : SfCompactSupportCoefficientAction l D.k (finiteFieldDatumPrimeUnit D l hl) Ω
          (Compactification.ofIsProper (Y ↘ Spec (.of D.k))),
        Nonempty (S.system.functor ≅ S₀.system.functor)) ∧
    (∀ K : (intrinsicFiniteTorsionConstructible l (Coefficient.{u} l Ω E₀) n hn
        Y).FullSubcategory,
      Nonempty (finiteCompactSections D l (Coefficient.{u} l Ω E₀) Y c n hn K.obj ≅
        finiteOrdinarySections D l (Coefficient.{u} l Ω E₀) Y n hn K.obj) ∧
      ∀ i : ℤ, Nonempty (finiteCompactCohomology D l
        (Coefficient.{u} l Ω E₀) Y c n hn K.obj i ≅
          finiteOrdinaryCohomology D l (Coefficient.{u} l Ω E₀) Y n hn K.obj i)) ∧
    (∀ K : sfIntegralConstructibleCategory l (Coefficient.{u} l Ω E₀) Y,
      Nonempty (sfIntegralCompactSupportValue l (Coefficient.{u} l Ω E₀) D.k
        (finiteFieldDatumPrimeUnit D l hl) c K ≅
          integralImage D l hl (Coefficient.{u} l Ω E₀) Y K) ∧
      Nonempty (integralCompactSections D l hl (Coefficient.{u} l Ω E₀) Y c K ≅
        integralOrdinarySections D l hl (Coefficient.{u} l Ω E₀) Y K) ∧
      ∀ i : ℤ, Nonempty (integralCompactCohomology D l hl (Coefficient.{u} l Ω E₀)
        Y c K i ≅ integralOrdinaryCohomology D l hl (Coefficient.{u} l Ω E₀) Y K i)) ∧
    (∀ K : sfRationalConstructibleCategory l (Coefficient.{u} l Ω E₀) Y,
      Nonempty (sfRationalCompactSupportValue l (Coefficient.{u} l Ω E₀) D.k
        (finiteFieldDatumPrimeUnit D l hl) c K.obj ≅
          rationalImage D l hl (Coefficient.{u} l Ω E₀) Y K) ∧
      Nonempty (rationalCompactSections D l hl (Coefficient.{u} l Ω E₀) Y c K ≅
        rationalOrdinarySections D l hl (Coefficient.{u} l Ω E₀) Y K) ∧
      ∀ i : ℤ, Nonempty (rationalCompactCohomology D l hl (Coefficient.{u} l Ω E₀)
        Y c K i ≅ rationalOrdinaryCohomology D l hl (Coefficient.{u} l Ω E₀) Y K i)) ∧
    (∀ K : generalAlgebraicallyClosedConstructibleCategory l Ω Y,
      Nonempty (sfQbarCompactSupportValue l D.k (finiteFieldDatumPrimeUnit D l hl)
        Ω c K.stage K.obj.obj ≅ qbarImage D l hl Y Ω K) ∧
      Nonempty (qbarCompactSections D l hl Y Ω c K ≅ qbarOrdinarySections D l hl Y Ω K) ∧
      ∀ i : ℤ, Nonempty (qbarCompactCohomology D l hl Y Ω c K i ≅
        qbarOrdinaryCohomology D l hl Y Ω K i)) := by
  let E := Coefficient.{u} l Ω E₀
  let A := Padic.coefficientExtensionRing l E n
  let : Finite A := Padic.finite_coefficientExtensionRing l E n hn
  let finiteIso := Functor.isoWhiskerLeft (intrinsicFiniteTorsionConstructible l E n hn Y).ι
    (properCompactFiniteIso A (Y ↘ Spec (.of D.k)) c)
  refine ⟨⟨finiteIso⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact properCompactIntegralFunctor D l hl E Y c
  · exact properCompactRationalChange D l hl E Y c _
  · intro S S₀
    exact properCompactQbarChange D l hl Ω Y c _ S S₀
  · intro K
    let e := ((pointFiniteSections D.k A).mapDerivedCategory).mapIso (finiteIso.app K)
    refine ⟨⟨e⟩, fun i ↦ ⟨?_⟩⟩
    exact (DerivedCategory.homologyFunctor (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) i).mapIso e
  · intro K
    obtain ⟨e⟩ := properCompactIntegralValue D l hl E Y c K
    let sections := (pointIntegralFibre D l hl E).mapIso e
    exact ⟨⟨e⟩, ⟨sections⟩, fun i ↦
      ⟨(DerivedCategory.coefficientFgCohomology _ _ i).mapIso sections⟩⟩
  · intro K
    obtain ⟨e⟩ := properCompactRationalValue D l hl E Y c K
    let sections := (pointRationalFibre D l hl E).mapIso e
    exact ⟨⟨e⟩, ⟨sections⟩, fun i ↦
      ⟨(DerivedCategory.coefficientFdCohomology E i).mapIso sections⟩⟩
  · intro K
    obtain ⟨e⟩ := properCompactRationalValue D l hl (Coefficient l Ω K.stage) Y c K.obj
    let q := (GeneralAlgebraicallyClosedCoefficients.inclusion
      (Y := Spec (.of D.k)) K.stage).mapIso e
    let sections := (pointQbarFibre D l hl Ω).mapIso q
    exact ⟨⟨q⟩, ⟨sections⟩, fun i ↦
      ⟨(DerivedCategory.coefficientQbarCohomology l Ω i).mapIso sections⟩⟩

end WeilConjectures
