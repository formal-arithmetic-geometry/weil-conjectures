/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedFiniteTorConstructible
public import WeilConjectures.AlgebraicGeometry.CondensedGeometricPoint.IntrinsicCondensedCoefficientPoint
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.CategoryTheory.RingObjects.EllAdic
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriek
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.Derived
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.DerivedStalk
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.Algebra.CharP.CharAndCard
public import WeilConjectures.AlgebraicGeometry.Etale.Derived.EtaleDerivedScalarTensor
public import WeilConjectures.AlgebraicGeometry.ExceptionalCoefficients.ExceptionalCoefficientMaps
public import WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinary.FiniteCoefficientHeartTensor
public import WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinary.FiniteDiscreteOrdinaryEncodingSupplement
public import WeilConjectures.AlgebraicGeometry.ModuleRingedComparison.ProEtaleSectionModuleFunctors
public import WeilConjectures.AlgebraicGeometry.Proper.ProperFiniteCoefficientExtension
public import WeilConjectures.CategoryTheory.Constant.ConstantScalarRestrictionTensorSupplement
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.CommIsoComp
public import WeilConjectures.CategoryTheory.DerivedCategory.TorAmplitudeMapDerivedCategory
public import WeilConjectures.CategoryTheory.InternalSectionTensorComparison
public import WeilConjectures.CategoryTheory.Sites.SheafComposeForgetModule
public import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvr
public import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.CoefficientDevissage
public import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.CompactSupport
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependence
public import WeilConjectures.SixFunctors.Etale.Derived.TorAmplitudeResidue
public import WeilConjectures.SixFunctors.ProEtale.Comparison.CohomologicalDimension
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.HomComparison
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriekComparison
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.FinitePointScalarRealization
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.EtaleOrigin
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.Scalars
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.UpperStar

/-!
# Compact-support perfectness in the condensed model

Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/
sec-poincare-duality/sec-perfect-complexes-on-the-point-and-two-exchange-formulas/
sk-lem-finite/sk-prop-sf-trace-perfectness/
prop-trf-compact-support-perfectness.md and prop-trf-compact-support-perfectness.proof.md
(blueprint: prop-trf-compact-support-perfectness).

This statement binds the finite-field datum, coefficient stage, geometric scheme, and
condensed coefficient ring inline, as in the landed finite compact-support and geometric
stalk perfectness declaration. No parallel convention structure is introduced.
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped CategoryTheory.Obj

namespace WeilConjectures

private theorem heartEncoding_monoidal : Nonempty (heartEncoding A X).Monoidal := by
  obtain ⟨ms, _⟩ := section_monoidal_normalized
    (Scheme.ProEt.topology X) (condensedRingObj (Profinite.continuousMapRingObj A) X)
  let := ms
  have := scalarRingMap_isIso A X
  let := HasDerivedCategory.standard
    (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} (ULift.{u + 1} A)))
  let := HasDerivedCategory.standard
    (SheafOfModules.{u + 1} ((sheafCompose (Scheme.ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (canonicalSectionRing A X)))
  let := HasDerivedCategory.standard
    (SheafOfModules.scalarModules (Scheme.ProEt.topology X)
      (realizationRing (Scheme.ProEt.topology X) (ULift.{u + 1} A)))
  obtain ⟨r⟩ := SheafOfModules.ringIso_tensor_transport (asIso (scalarRingMap A X))
  let : (SheafOfModules.restrictScalars ((sheafCompose (Scheme.ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map (scalarRingMap A X))).Monoidal :=
    r.monoidal.toMonoidal
  let : (ConstantScalarRestriction.restriction (Scheme.ProEt.topology X)
      (ULift.{u + 1} A)).Monoidal :=
    (ConstantScalarRestriction.ordinary (Scheme.ProEt.topology X)
      (ULift.{u + 1} A)).braided.toMonoidal
  let : (heartEncoding A X).Monoidal := by
    unfold heartEncoding
    infer_instance
  exact ⟨inferInstance⟩

/-- The scalar action calculation identifies the explicit section encoding with the
canonical finite-coefficient functor. Transport its proved strong monoidal structure. -/
private theorem monoidal
    (A : Type) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [DiscreteTopology A] [Finite A] (X : Scheme.{u}) :
    Nonempty (finiteCoefficientModEquivalence X A).functor.Monoidal := by
  obtain ⟨m⟩ := heartEncoding_monoidal A X
  let := m
  exact ⟨Functor.Monoidal.transport (heartCanonicalIso A X)⟩

private noncomputable def derivedStalk_etaleOrigin
    {X : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (A : Type (u + 1)) [CommRing A] (x : Spec (.of Ω) ⟶ X)
    (G : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (hG : DerivedCategory.TStructure.t.plus G) :
    (ProEtale.derivedGeometricStalk (ModuleCat.{u + 1} A) x).obj
        ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory.obj G) ≅
      (Etale.rightDerivedGlobalSections (ModuleCat.{u + 1} A) (Spec (.of Ω))).obj
        ((Etale.upperStar (ModuleCat.{u + 1} A) x).leftDerivedFunctor.obj G) := by
  let C := ModuleCat.{u + 1} A
  let P := Spec (.of Ω)
  let H := (Etale.upperStar C x).mapDerivedCategory.obj G
  have hH : DerivedCategory.TStructure.t.plus H := by
    obtain ⟨a, ha⟩ := hG
    exact ⟨a, (Etale.upperStar C x).isGE_mapDerivedCategory_obj G a⟩
  have := ProEtale.isIso_derivedComparisonAdjunction_unit_app C P H hH
  let ep : (ProEtale.comparisonUpperStar C X).mapDerivedCategory ⋙
      (ProEtale.upperStar C x).mapDerivedCategory ≅
      (Etale.upperStar C x).mapDerivedCategory ⋙
        (ProEtale.comparisonUpperStar C P).mapDerivedCategory :=
    (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
      Functor.mapDerivedCategoryNatIso (ProEtale.comparisonUpperStarCompUpperStarIso C x) ≪≫
        Functor.mapDerivedCategoryCompIso _ _
  exact (ProEtale.rightDerivedGlobalSections C P).mapIso
      (((ProEtale.upperStar C x).leftDerivedFunctorIsoMapDerivedCategory.app _) ≪≫
        ep.app G) ≪≫
    ((ProEtale.comparisonLowerStarCompRightDerivedGlobalSectionsIso C P).app _).symm ≪≫
    (Etale.rightDerivedGlobalSections C P).mapIso
      ((asIso ((ProEtale.derivedComparisonAdjunction C P).unit.app H)).symm ≪≫
        ((Etale.upperStar C x).leftDerivedFunctorIsoMapDerivedCategory.app G).symm)

private theorem boundedConstructible_of_restrictScalars
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) (X : Scheme.{u}) (G : Etale.DerivedCategoryModule B X)
    (hG : Etale.DerivedCategory.boundedConstructible (ModuleCat.{u + 1} A) X
      ((Sheaf.restrictScalars X.smallEtaleTopology φ).mapDerivedCategory.obj G)) :
    Etale.DerivedCategory.boundedConstructible (ModuleCat.{u + 1} B) X G := by
  let U := Sheaf.restrictScalars X.smallEtaleTopology φ
  refine ⟨U.bounded_of_bounded_mapDerivedCategory_obj hG.1, fun i ↦ ?_⟩
  apply (Scheme.isConstructibleSheaf_restrictScalars_iff_of_finite φ _).1
  exact @Scheme.IsConstructibleSheaf.of_iso _ _ _ _ _ _ _ _ _ _ _
    ((U.mapDerivedCategoryHomologyFunctorIso i).app G).symm (hG.2 i)

private noncomputable def scalarResidueCoefficientIso
    (A : Type (u + 1)) [CommRing A] (X : Scheme.{u}) :
    Etale.scalarCoefficientSheaf (Ideal.Quotient.mk (Ring.jacobson A)) X ≅
      (constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)).obj
        (ModuleCat.of A (A ⧸ Ring.jacobson A)) :=
  (constantCommuteCompose X.smallEtaleTopology
    (ModuleCat.restrictScalars.{u + 1} (Ideal.Quotient.mk (Ring.jacobson A)))).app
      (ModuleCat.of (A ⧸ Ring.jacobson A) (A ⧸ Ring.jacobson A))

private theorem etale_compactSupport_perfect
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f]
    [HasCompactification f] [HasInvertibleExponent A X]
    (G : Etale.DerivedCategoryModule A X)
    (hG : Etale.DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} A) X G) :
    @DerivedCategory.IsPerfect.{u + 1} A _
      (HasDerivedCategory.ofIsGrothendieckAbelian _)
      ((Etale.rightDerivedGlobalSections (ModuleCat.{u + 1} A) (Spec (.of k))).obj
        ((Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).obj G)) := by
  let C := ModuleCat.{u + 1} A
  let Y := Spec (.of k)
  let B := A ⧸ Ring.jacobson A
  let φ := Ideal.Quotient.mk (Ring.jacobson A)
  let : Finite B := Finite.of_surjective φ Ideal.Quotient.mk_surjective
  let SX := Etale.scalarExtension φ X
  let SY := Etale.scalarExtension φ Y
  let UX := Sheaf.restrictScalars X.smallEtaleTopology φ
  let UY := Sheaf.restrictScalars Y.smallEtaleTopology φ
  let F := Etale.rightDerivedLowerShriek C f
  let d := HasCompactification.compactification f
  have hF := Etale.boundedConstructible_rightDerivedLowerShriek A f f (𝟙 Y)
    (Category.comp_id f) G hG.1
  have : HasInvertibleExponent B X := by
    obtain ⟨n, hn, hz, hu⟩ := HasInvertibleExponent.exists_isUnit_natCast (Λ := A) (X := X)
    exact ⟨n, hn, by simpa only [map_natCast, map_zero] using congrArg φ hz, hu⟩
  have : IsLocallyNoetherian d.Z := LocallyOfFiniteType.isLocallyNoetherian d.g
  have : CompactSpace d.Z := QuasiCompact.compactSpace_of_compactSpace d.g
  have : IsNoetherian d.Z := ⟨⟩
  -- The residue input is bounded constructible, first after scalar restriction.
  have hc : Scheme.IsConstructibleSheaf (Etale.scalarCoefficientSheaf φ X) := by
    have := Scheme.isConstructibleSheaf_constantSheaf
      (X := X) (ModuleCat.of A B)
    exact Scheme.IsConstructibleSheaf.of_iso (scalarResidueCoefficientIso A X).symm
  obtain ⟨β⟩ := Etale.nonempty_iso_derivedTensor_flip C X
  have hred := (Etale.DerivedCategory.boundedConstructible C X).prop_of_iso
    (((β.app _).app G) ≪≫ ((Etale.scalarTensorIso φ X).app G).symm)
    (Etale.boundedConstructible_tensor A X
      (Etale.DerivedCategory.boundedConstructible_singleFunctor_obj _ 0) hG.1 hG.2)
  have hB := boundedConstructible_of_restrictScalars φ X (SX.obj G) hred
  have hFB := Etale.boundedConstructible_rightDerivedLowerShriek B f f (𝟙 Y)
    (Category.comp_id f) (SX.obj G) hB
  -- Apply the actual B-linear proper/open coefficient comparison only at the residue ring.
  have := (Etale.properFiniteCoefficientExtension φ d.g).1
    ((Etale.openImmersionLowerShriek C d.i).mapDerivedCategory.obj G)
  have hcomp : IsIso (Etale.ExceptionalCoefficients.compactSupportMap φ d G) := by
    unfold Etale.ExceptionalCoefficients.compactSupportMap
    infer_instance
  let e : UY.mapDerivedCategory.obj (SY.obj (F.obj G)) ≅
      UY.mapDerivedCategory.obj
        ((Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} B) f).obj (SX.obj G)) :=
    UY.mapDerivedCategory.mapIso (asIso (Etale.ExceptionalCoefficients.compactSupportMap φ d G))
  have hres : DerivedCategory.TStructure.t.bounded
      (((Etale.derivedTensor C Y).obj (F.obj G)).obj
        ((DerivedCategory.singleFunctor _ 0).obj
          ((constantSheaf Y.smallEtaleTopology C).obj (ModuleCat.of A B)))) := by
    let er := ((Etale.scalarTensorIso φ Y).app (F.obj G)).symm ≪≫ e
    let er' := er.symm ≪≫ ((Etale.derivedTensor C Y).obj (F.obj G)).mapIso
      ((DerivedCategory.singleFunctor _ 0).mapIso (scalarResidueCoefficientIso A Y))
    obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := UY.bounded_mapDerivedCategory_obj hFB.1
    let := ha
    let := hb
    exact ⟨⟨a, DerivedCategory.TStructure.t.isGE_of_iso er' a⟩,
      ⟨b, DerivedCategory.TStructure.t.isLE_of_iso er' b⟩⟩
  obtain ⟨a, b, hab⟩ :=
    (DerivedCategory.exists_homologyConcentratedIn_iff_bounded _).2 hres
  have htor : Etale.DerivedCategory.torAmplitudeIn C Y a b (F.obj G) :=
    (Etale.DerivedCategory.torAmplitudeIn_iff_tensorSingleConcentratedIn (Λ := A) a b _).2 hab
  exact Etale.isPerfect_rightDerivedGlobalSections_of_isSepClosed _ ⟨hF, a, b, htor⟩

private theorem fixedStalkPerfect
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {Y : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (x : Spec (.of Ω) ⟶ Y)
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} A)))
    (hK : ProEtale.DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} A) Y K) :
    DerivedCategory.IsPerfectRingComplex
      ((ProEtale.derivedGeometricStalk (ModuleCat.{u + 1} A) x).obj K) := by
  obtain ⟨hbc, a, b, ht⟩ := hK
  obtain ⟨G, hG, ⟨e⟩⟩ := (ProEtale.DerivedCategory.boundedConstructible_iff _ _ K).1 hbc
  have hEt := ProEtale.DerivedCategory.torAmplitudeIn_of_mapDerivedCategory A
    ((ProEtale.DerivedCategory.torAmplitudeIn _ Y a b).prop_of_iso e.symm ht)
  have hp := Etale.isPerfect_geometricStalk A x G ⟨hG, a, b, hEt⟩
  obtain ⟨P, r, t, hr, ht, hP, ⟨eP⟩⟩ := hp
  exact ⟨P, r, t, hr, ht, hP,
    ⟨(ProEtale.derivedGeometricStalk (ModuleCat.{u + 1} A) x).mapIso e.symm ≪≫
      derivedStalk_etaleOrigin A x G hG.1.1 ≪≫ eP⟩⟩

private noncomputable def fixedSupportComparison
    (A : Type) [CommRing A] [Finite A] [TopologicalSpace A]
    [DiscreteTopology A] [IsTopologicalRing A]
    {Y Z : Scheme.{u}} {f : Y ⟶ Z} (c : Compactification f) :
    ProEtale.CondensedRing.rightDerivedLowerShriekOfCompactification
        (Profinite.continuousMapRingObj A) c ⋙
        (ProEtale.finiteCoefficientDerivedEquivalence Z A).functor ≅
      (ProEtale.finiteCoefficientDerivedEquivalence Y A).functor ⋙
        ProEtale.rightDerivedLowerShriekOfCompactification
          (ModuleCat.{u + 1} (ULift.{u + 1} A)) c := by
  let Λ := Profinite.continuousMapRingObj.{u} A
  let C := ModuleCat.{u + 1} (ULift.{u + 1} A)
  let FY := ProEtale.finiteCoefficientModEquivalence Y A
  let FW := ProEtale.finiteCoefficientModEquivalence c.Z A
  let ei := ProEtale.upperStarFiniteCoefficientModEquivalenceIso c.i A
  let er := Iso.inverseCompIso
    (Iso.isoCompInverse ei ≪≫ Functor.associator _ _ _)
  let eopen := ((conjugateIsoEquiv
    ((ProEtale.CondensedRing.openImmersionLowerShriekUpperStarAdjunction Λ c.i).comp
      FW.toAdjunction)
    (FY.toAdjunction.comp
      (ProEtale.openImmersionLowerShriekUpperStarAdjunction C c.i))).symm er).symm
  let eo := (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryNatIso eopen ≪≫ Functor.mapDerivedCategoryCompIso _ _
  let ep := Functor.rightDerivedFunctorCommIso
    (ProEtale.lowerStarFiniteCoefficientModEquivalenceIso c.g A)
  exact Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _ ep ≪≫
    (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight eo _ ≪≫
      Functor.associator _ _ _

private theorem constants_injective (T : Type) [TopologicalSpace T] [CommRing T]
    [IsTopologicalRing T] : Function.Injective (Profinite.continuousMapConstRingHom.{u} T) := by
  intro x y h
  have hs := congrArg (fun z : MonObj.Γ (Profinite.continuousMapRingObj.{u} T) ↦
    Functor.LaxMonoidal.ε (sheafToPresheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) ≫
      (sheafToPresheaf (coherentTopology Profinite.{u}) Ab.{u + 1}).map z.hom) h
  dsimp only [Profinite.continuousMapConstRingHom] at hs
  simp only [Sheaf.ε_comp_ringHomΓSheafCompose_hom
    (coherentTopology Profinite.{u}) (Profinite.continuousMapRingSheaf T)
    (Profinite.continuousMapConstSectionRingHom T) (fun _ _ ↦ rfl)] at hs
  have hh := congrArg (fun f ↦
    f.app (Opposite.op (Profinite.of PUnit.{u + 1})) (ULift.up 1)) hs
  change ((1 : ℤ) : ULift.{u + 1} C(PUnit.{u + 1}, T)) *
    ULift.up (ContinuousMap.const PUnit.{u + 1} x) =
      ((1 : ℤ) : ULift.{u + 1} C(PUnit.{u + 1}, T)) *
        ULift.up (ContinuousMap.const PUnit.{u + 1} y) at hh
  simp only [Int.cast_one, one_mul] at hh
  exact congrArg (fun f ↦ f.down PUnit.unit) hh

private noncomputable def finiteScalarEquiv
    (A : Type) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] :
    ULift.{u + 1} A ≃+* MonObj.Γ (Profinite.continuousMapRingObj.{u} A) :=
  ULift.ringEquiv.trans (RingEquiv.ofBijective (Profinite.continuousMapConstRingHom A)
    ⟨constants_injective A, Profinite.continuousMapConstRingHom_surjective A⟩)

private noncomputable def fixedSectionsComparison
    (A : Type) [CommRing A] [Finite A] [TopologicalSpace A]
    [DiscreteTopology A] [IsTopologicalRing A] (Y : Scheme.{u}) :
    ProEtale.CondensedRing.condensedRingCoefficientSections
        (Profinite.continuousMapRingObj A) Y ⋙
        ModuleCat.restrictScalars (finiteScalarEquiv.{u} A).toRingHom ≅
      (ProEtale.finiteCoefficientModEquivalence Y A).functor ⋙
        Sheaf.Γ (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} (ULift.{u + 1} A)) := by
  let F := (ProEtale.finiteCoefficientModEquivalence Y A).functor
  let T := Scheme.ProEt.mk (𝟙 Y)
  let hT := Scheme.ProEt.isTerminalMkId Y
  let σ := (finiteScalarEquiv.{u} A).toRingHom
  let S := ProEtale.CondensedRing.condensedRingCoefficientSections
    (Profinite.continuousMapRingObj A) Y ⋙ ModuleCat.restrictScalars σ
  let E := (sheafSections (Scheme.ProEt.topology Y)
    (ModuleCat.{u + 1} (ULift.{u + 1} A))).obj (Opposite.op T)
  let e (M : _) : S.obj M ≅ E.obj (F.obj M) := by
    apply LinearEquiv.toModuleIso (X₁ := S.obj M) (X₂ := E.obj (F.obj M))
    refine AddEquiv.toLinearEquiv ((Mod.regularHomAddEquiv M).trans
      (Sheaf.unitHomEvalAddEquiv hT M.X)) ?_
    intro a x
    obtain ⟨a⟩ := a
    let τ := (ProEtale.CondensedRing.condensedRingScalarSections
      (Profinite.continuousMapRingObj A) Y) (Profinite.continuousMapConstRingHom A a)
    refine (congrArg (Sheaf.unitHomEval (J := Scheme.ProEt.topology Y) T (F := M.X))
      (Mod.one_comp_regularLift_comp_hom.{u + 1, u + 2} τ.hom x)).trans ?_
    exact (Sheaf.unitHomEval_comp T _ (Mod.globalSmul τ.hom M)).trans
      (ProEtale.finiteCoefficientModEquivalence_smul Y A M _ a _).symm
  exact (NatIso.ofComponents e (by
      intro M N f
      ext x
      exact ProEtale.regularHomEquivSections_comp A Y x f)) ≪≫
    Functor.isoWhiskerLeft F (Sheaf.ΓNatIsoSheafSections _ _ hT).symm

private noncomputable def fixedDerivedSectionsComparison
    (A : Type) [CommRing A] [Finite A] [TopologicalSpace A]
    [DiscreteTopology A] [IsTopologicalRing A] (Y : Scheme.{u}) :
    (ProEtale.CondensedRing.condensedRingCoefficientSections
        (Profinite.continuousMapRingObj A) Y).rightDerivedFunctor ⋙
        (ModuleCat.restrictScalars (finiteScalarEquiv.{u} A).toRingHom).mapDerivedCategory ≅
      (ProEtale.finiteCoefficientDerivedEquivalence Y A).functor ⋙
        ProEtale.rightDerivedGlobalSections (ModuleCat.{u + 1} (ULift.{u + 1} A)) Y :=
  Functor.rightDerivedFunctorCommIso (fixedSectionsComparison A Y)

private theorem coefficientPrimeUnit
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p) :
    IsUnit (l : D.k) := by
  classical
  let _ : Fintype D.k₀ := Fintype.ofFinite D.k₀
  have hc : Fintype.card D.k₀ = D.q := by
    simpa only [Nat.card_eq_fintype_card] using D.card_base
  have _ : Fact D.p.Prime := ⟨D.prime⟩
  have _ : CharP D.k₀ D.p :=
    charP_of_card_eq_prime_pow (hc.trans D.cardinality_eq)
  have _ : CharP D.k D.p := charP_of_injective_algebraMap' D.k₀ D.p
  have hne : (l : D.k) ≠ 0 := by
    intro h
    have hdvd : D.p ∣ l := by
      exact (CharP.cast_eq_zero_iff D.k D.p l).mp h
    obtain h | h := (Nat.dvd_prime (Fact.out : l.Prime)).mp hdvd
    · exact D.prime.ne_one h
    · exact hl h.symm
  exact isUnit_iff_ne_zero.mpr hne

private theorem coefficient_has_invertible_exponent
    (l : ℕ) [Fact l.Prime] (E : Type) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] (K₀ : Type u) [Field K₀] (hl : IsUnit (l : K₀))
    (n : ℕ) (_hn : 1 ≤ n) :
    HasInvertibleExponent (ULift.{u + 1} (Padic.coefficientExtensionRing l E n))
      (Spec (.of K₀)) := by
  let v := Padic.coefficientExtensionAbsoluteValue l E
  have hv := spectralNorm_extends (K := Padic l) (L := E)
  have h := (Padic.extension_integers_dvr l E v hv).choose_spec.choose_spec
  have hm : (l : Padic.coefficientExtensionIntegers l E) ∈
      Padic.coefficientExtensionMaximalIdeal l E := by
    apply (h.2.1 _).2
    change v (l : E) < 1
    rw [← map_natCast (algebraMap (Padic l) E) l]
    change spectralNorm (Padic l) E ((algebraMap (Padic l) E) (l : Padic l)) < 1
    rw [hv]
    exact Padic.norm_p_lt_one
  have hgen : Ideal.span ({Padic.coefficientExtensionUniformizer l E} :
      Set (Padic.coefficientExtensionIntegers l E)) =
        Padic.coefficientExtensionMaximalIdeal l E :=
    h.2.2.2.2.2.2.2.2.2.2.2.2.2.1.choose_spec
  have hkill : (l ^ n : Padic.coefficientExtensionRing l E n) = 0 := by
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    change (l : Padic.coefficientExtensionIntegers l E) ^ n ∈
      Ideal.span ({Padic.coefficientExtensionUniformizer l E} :
        Set (Padic.coefficientExtensionIntegers l E)) ^ n
    rw [hgen]
    exact Ideal.pow_mem_pow hm n
  refine ⟨l ^ n, pow_pos (Fact.out : l.Prime).pos n, ?_, ?_⟩
  · apply ULift.ext
    change ((l ^ n : ℕ) : Padic.coefficientExtensionRing l E n) = 0
    simpa only [Nat.cast_pow] using hkill
  · have hu := (hl.pow n).map (Scheme.ΓSpecIso (.of K₀)).inv.hom
    simpa only [map_pow, map_natCast, Nat.cast_pow] using hu

private noncomputable def fixedCompactSupport_etaleOrigin
    (A : Type) [CommRing A] [Finite A] [TopologicalSpace A]
    [DiscreteTopology A] [IsTopologicalRing A]
    {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}}
    {f : X ⟶ Spec (.of k)} [QuasiCompact f] [HasCompactification f]
    (c : Compactification f)
    (G : Etale.DerivedCategoryModule (ULift.{u + 1} A) X)
    (hG : DerivedCategory.TStructure.t.bounded G) :
    (ProEtale.rightDerivedGlobalSections (ModuleCat.{u + 1} (ULift.{u + 1} A))
      (Spec (.of k))).obj
      ((ProEtale.rightDerivedLowerShriekOfCompactification
        (ModuleCat.{u + 1} (ULift.{u + 1} A)) c).obj
        ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1} A))
          X).mapDerivedCategory.obj G)) ≅
    (Etale.rightDerivedGlobalSections (ModuleCat.{u + 1} (ULift.{u + 1} A))
      (Spec (.of k))).obj
      ((Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} (ULift.{u + 1} A)) f).obj G) := by
  let C := ModuleCat.{u + 1} (ULift.{u + 1} A)
  let Y := Spec (.of k)
  let CP := ProEtale.comparisonUpperStar C Y
  let GP : DerivedCategory.Plus (Sheaf X.smallEtaleTopology C) := ⟨G, hG.1⟩
  let ec := (ProEtale.rightDerivedLowerShriekOfCompactificationComparisonIso C c).app GP
  let ei := (Etale.rightDerivedLowerShriekOfCompactificationPlusιIso
    (ULift.{u + 1} A) c (HasCompactification.compactification f)).app GP
  let H := (Etale.rightDerivedLowerShriek C f).obj G
  have hH : DerivedCategory.TStructure.t.plus H := by
    obtain ⟨a, ha⟩ := hG.1
    have : G.IsGE a := ha
    exact ⟨a, Etale.isGE_rightDerivedLowerShriek_obj
      (ULift.{u + 1} A) f G hG a⟩
  have := ProEtale.isIso_derivedComparisonAdjunction_unit_app C Y H hH
  exact (ProEtale.rightDerivedGlobalSections C Y).mapIso
      (ec ≪≫ CP.mapDerivedCategory.mapIso ei) ≪≫
    ((ProEtale.comparisonLowerStarCompRightDerivedGlobalSectionsIso C Y).app _).symm ≪≫
    (Etale.rightDerivedGlobalSections C Y).mapIso
      (asIso ((ProEtale.derivedComparisonAdjunction C Y).unit.app H)).symm

private theorem condensedFinite_compactSupport_perfect
    (A : Type) [CommRing A] [Finite A] [TopologicalSpace A]
    [DiscreteTopology A] [IsTopologicalRing A]
    {k : Type u} [Field k] [IsAlgClosed k]
    (X : Over (Spec (.of k)))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [HasInvertibleExponent (ULift.{u + 1} A) (Spec (.of k))]
    (c : Compactification X.hom)
    (K : (ProEtale.CondensedRing.condensedConstructibleFiniteTor
      (Profinite.continuousMapRingObj.{u} A) X.left).FullSubcategory) :
    DerivedCategory.IsPerfectRingComplex
      ((ProEtale.CondensedGeometricPoint.fiber (Profinite.continuousMapRingObj A) k).obj
        ((ProEtale.CondensedRing.rightDerivedLowerShriekOfCompactification
          (Profinite.continuousMapRingObj A) c).obj K.obj)) ∧
    ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (xbar : Spec (.of Ω) ⟶ X.left),
      DerivedCategory.IsPerfectRingComplex
        ((ProEtale.derivedGeometricStalk (ModuleCat.{u + 1} (ULift.{u + 1} A)) xbar).obj
          ((ProEtale.finiteCoefficientDerivedEquivalence X.left A).functor.obj K.obj)) := by
  classical
  constructor
  · let Λ := Profinite.continuousMapRingObj.{u} A
    let B := ULift.{u + 1} A
    let C := ModuleCat.{u + 1} B
    let Y := Spec (.of k)
    let F := ProEtale.CondensedRing.rightDerivedLowerShriekOfCompactification Λ c
    let H := F.obj K.obj
    let := c.hasCompactification
    let : HasInvertibleExponent B X.left := HasInvertibleExponent.of_hom X.hom
    obtain ⟨hbc, a, b, ht⟩ := fixedCtf A X.left K
    obtain ⟨G, hG, ⟨eG⟩⟩ :=
      (ProEtale.DerivedCategory.boundedConstructible_iff C X.left _).1 hbc
    have hEt := ProEtale.DerivedCategory.torAmplitudeIn_of_mapDerivedCategory B
      ((ProEtale.DerivedCategory.torAmplitudeIn C X.left a b).prop_of_iso eG.symm ht)
    have hp := etale_compactSupport_perfect B X.hom G ⟨hG, a, b, hEt⟩
    let ec := (fixedDerivedSectionsComparison A Y).app H ≪≫
      (ProEtale.rightDerivedGlobalSections C Y).mapIso
        ((fixedSupportComparison A c).app K.obj ≪≫
          (ProEtale.rightDerivedLowerShriekOfCompactification C c).mapIso eG.symm) ≪≫
      fixedCompactSupport_etaleOrigin A c G hG.1
    have hS := ProEtale.CondensedRing.perfect_of_iso ec.symm hp
    have hΓ := (ProEtale.CondensedRing.perfect_restrictScalars_iff
      (finiteScalarEquiv A) _).2 hS
    have hFib := ProEtale.CondensedRing.perfect_of_iso
      ((ProEtale.CondensedRing.actualSectionsDerivedIso Λ k).app H) hΓ
    exact (ProEtale.CondensedRing.perfect_restrictScalars_iff
      (ProEtale.CondensedRing.scalarSectionEquiv Λ) _).2 hFib
  · intro Ω _ _ xbar
    exact fixedStalkPerfect _ xbar _ (fixedCtf _ X.left K)

/-- Compact-support cohomology and every geometric stalk are perfect ordinary coefficient
complexes for the current condensed finite-Tor model.

Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/
sec-poincare-duality/sec-perfect-complexes-on-the-point-and-two-exchange-formulas/
sk-lem-finite/sk-prop-sf-trace-perfectness/prop-trf-compact-support-perfectness.md,
with proof route in prop-trf-compact-support-perfectness.proof.md
(blueprint: prop-trf-compact-support-perfectness).

Proof: the canonical finite-coefficient equivalence transports constructibility and the
actual Tor interval to fixed-scalar sheaves. Descend to the etale presentation. Compact
support has bounded constructible cohomology. Its derived scalar extension to the residue
ring is bounded: tensor constructibility handles the input, and the canonical proper/open
coefficient comparison identifies its compact support with scalar extension of the output.
The residue Tor criterion and finite cohomology give a finite-projective model after exact
sections on the point. Construct the comparisons of compactification lower shriek and
terminal sections, then use the actual point-fiber comparison and scalar ring isomorphisms
to transport this model to the specified condensed fiber. For each geometric point, exact
inverse image, the bounded-below comparison unit and Leray identify the specified pro-etale
stalk with the etale stalk. Its finite-Tor perfectness supplies the second model. No
finite-type hypothesis on the point field is used.
-/
theorem compactSupport_perfect
    (D : FiniteFieldDatum.{u}) (ell : ℕ) [Fact ell.Prime] (_hell : ell ≠ D.p)
    (E : PadicAlgCl.FiniteIntermediateField ell) (n : ℕ) (hn : 1 ≤ n)
    (X : Over (Spec (.of D.k)))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    (c : Compactification X.hom) :
    let A := Padic.coefficientExtensionRing ell E n
    letI : Finite A := Padic.finite_coefficientExtensionRing ell E n hn
    letI : TopologicalSpace A := ⊥
    letI : DiscreteTopology A := discreteTopology_bot A
    letI : IsTopologicalRing A := DiscreteTopology.topologicalRing
    let Λ := Profinite.continuousMapRingObj.{u} A
    ∀ K : (ProEtale.CondensedRing.condensedConstructibleFiniteTor Λ X.left).FullSubcategory,
      DerivedCategory.IsPerfectRingComplex
        ((ProEtale.CondensedGeometricPoint.fiber Λ D.k).obj
          ((ProEtale.CondensedRing.rightDerivedLowerShriekOfCompactification Λ c).obj K.obj)) ∧
      ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
        (xbar : Spec (.of Ω) ⟶ X.left),
        DerivedCategory.IsPerfectRingComplex
          ((ProEtale.derivedGeometricStalk
              (ModuleCat.{u + 1} (ULift.{u + 1} A)) xbar).obj
            ((ProEtale.finiteCoefficientDerivedEquivalence X.left A).functor.obj K.obj)) := by
  classical
  dsimp only
  let A := Padic.coefficientExtensionRing ell E n
  let : Finite A := Padic.finite_coefficientExtensionRing ell E n hn
  let : TopologicalSpace A := ⊥
  let : DiscreteTopology A := discreteTopology_bot A
  let : IsTopologicalRing A := DiscreteTopology.topologicalRing
  let : HasInvertibleExponent (ULift.{u + 1} A) (Spec (.of D.k)) :=
    coefficient_has_invertible_exponent ell E D.k (coefficientPrimeUnit D ell _hell) n hn
  exact fun K => condensedFinite_compactSupport_perfect A X c K

end WeilConjectures
