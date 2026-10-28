module

public import Sheaf.SixFunctors.IntegralDualizingRoosModel
import all Sheaf.Paper.PointFibreEquivalence
import all Sheaf.Paper.PointSectionsScalarExtension
import Sheaf.Paper.ConstantCoefficientObjectsConstructible
import Sheaf.Paper.CompactSupportRepresentativeIndependence
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory
import WeilConjectures.CategoryTheory.DerivedCategory.HomSingleProjective

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096
set_option linter.style.longLine false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

attribute [-instance] pointScalarModuleDerived pointCompletedSheafDerived
  pointScalarAbSheafify pointScalarAbLocallyBijective
  coefficientComplexModuleDerived

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (E : Type u) [Field E] [Algebra (Padic l) E]
  [FiniteDimensional (Padic l) E]
  (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
  [QuasiCompact (X ↘ Spec (.of D.k))] [IsSeparated (X ↘ Spec (.of D.k))]

/-- Zeroth cohomology of the coefficient dual represents maps into the unit.
Source: Stacks Project, Tags 08J7 and 08JA; coefficient-point tensor--Hom
adjunction in degree zero.
(blueprint: lem-coef-integral-dualizing-mapping-limit-hom-at-degree-zero)

The coefficient derived dual is the internal Hom into the regular coefficient
unit. The unit tensor--Hom adjunction, followed by the normalized degree-zero
Hom computation, identifies its zeroth cohomology with maps from the compact
sections object to the unit. -/
theorem integralDualizing_coefficient_homology_at_zero
    (K : sfIntegralConstructibleCategory l E X) :
    Nonempty (((DerivedCategory.homologyFunctor
      (ModuleCat.{u + 1} (integralDualizingCoefficients l E)) 0).obj
      ((coefficientDerivedDual (integralDualizingCoefficients l E)).obj
        (Opposite.op ((integralDualizingCompactSections l E D hl X).obj K)))) ≃
      (((integralDualizingLimit l E (Spec (.of D.k))).obj
        ((integralDualizingCompactTower l E D hl X).obj K.obj) ⟶
          (DerivedCategory.singleFunctor
            (scalarReductionSource l E (Spec (.of D.k))) 0).obj
            (SheafOfModules.unit
              (completedIntegralCoefficientSheafUnrestricted l E
                (Spec (.of D.k))))))) := by
  let : HasSheafify (ProEt.topology (Spec (.of D.k))) AddCommGrpCat.{u + 1} :=
    integralCoefficientAbSheafify.{u, u} (Spec (.of D.k))
  let : (ProEt.topology (Spec (.of D.k))).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
    integralCoefficientAbLocallyBijective.{u, u} (Spec (.of D.k))
  let : (pointIntegralFibre D l hl E).IsEquivalence :=
    pointIntegralFibre_equivalence D l hl E
  let : HasDerivedCategory.{u + 1}
      (ModuleCat.{u + 1} (integralDualizingCoefficients l E)) :=
    HasDerivedCategory.ofIsGrothendieckAbelian _
  let : IsGrothendieckAbelian.{u + 1}
      (scalarReductionSource l E (Spec (.of D.k))) :=
    (SheafOfModules.grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses.{u + 1, u, u}
      (ProEt.topology (Spec (.of D.k)))
      (completedIntegralCommRingSheafUnrestricted l E (Spec (.of D.k)))).1
  let : Abelian.HasKInjectiveResolutions (scalarReductionSource l E (Spec (.of D.k))) :=
    @Abelian.hasKInjectiveResolutions_of_isGrothendieckAbelian
      (scalarReductionSource l E (Spec (.of D.k))) inferInstance inferInstance
      (inferInstance : IsGrothendieckAbelian.{u + 1}
        (scalarReductionSource l E (Spec (.of D.k))))
  let r := pointIntegralSectionMap l E D.k
  let q : ModuleCat.of (integralDualizingCoefficients l E)
      (integralDualizingCoefficients l E) ⟶
      (pointIntegralSections l E D.k).obj (SheafOfModules.unit
        (completedIntegralCoefficientSheafUnrestricted l E (Spec (.of D.k)))) :=
    ModuleCat.ofHom
      (Y := (pointIntegralSections l E D.k).obj (SheafOfModules.unit
        (completedIntegralCoefficientSheafUnrestricted l E (Spec (.of D.k)))))
      { toFun := r
        map_add' := map_add r
        map_smul' := fun a b ↦ by
          change r (a * b) = r a * r b
          exact map_mul r a b }
  have hq : IsIso q := by
    apply (ConcreteCategory.isIso_iff_bijective q).2
    change Function.Bijective (pointIntegralSectionMap l E D.k)
    exact (pointCompletedConstant_bijective D.k l E).comp
      (ULift.ringEquiv : integralDualizingCoefficients l E ≃+*
        Padic.coefficientExtensionIntegers l E).bijective
  let hu : (pointFibreIntegralAmbient D l E).obj
      (integralConstantCoefficientObject l E (Spec (.of D.k))) ≅
      (DerivedCategory.singleFunctor
        (ModuleCat.{u + 1} (integralDualizingCoefficients l E)) 0).obj
        (ModuleCat.of (integralDualizingCoefficients l E) (integralDualizingCoefficients l E)) :=
    ((pointIntegralSections l E D.k).mapDerivedCategorySingleFunctor 0).app
      (SheafOfModules.unit
        (completedIntegralCoefficientSheafUnrestricted l E (Spec (.of D.k)))) ≪≫
    (DerivedCategory.singleFunctor _ 0).mapIso (@asIso _ _ _ _ q hq).symm
  have hc := integralConstantCoefficient_constructible l E (Spec (.of D.k)) D hl
  let := integralOperationsDerivedCountableProducts l E (Spec (.of D.k))
  let : (Spec (.of D.k)).Over (Spec (.of D.k)) := ⟨𝟙 _⟩
  let : (X ↘ Spec (.of D.k)).IsOver (Spec (.of D.k)) := ⟨Category.comp_id _⟩
  have h := exists_compactSupportRepresentativeComparison l E D.k
    (finiteFieldDatumPrimeUnit D l hl) X (Spec (.of D.k))
      (X ↘ Spec (.of D.k)) (integralDualizingCompactification D X)
  have hT := h.choose_spec.choose_spec
  have hR := hT.2.2.choose_spec.choose_spec
  have hF := hR.2.2.choose_spec.2
  let F := hF.choose
  let γ := hF.choose_spec.2.2.2.1.choose
  let ε : hT.2.2.choose ≅ integralDualizingLimit l E (Spec (.of D.k)) := eqToIso hR.1
  let δ := γ.app K ≪≫ ε.app (h.choose.obj K.obj) ≪≫
    (integralDualizingLimit l E (Spec (.of D.k))).mapIso
      (eqToIso (Functor.congr_obj hT.1 K.obj))
  have hp : sfIntegralConstructible l E (Spec (.of D.k))
      ((integralDualizingLimit l E (Spec (.of D.k))).obj
        ((integralDualizingCompactTower l E D hl X).obj K.obj)) :=
    ObjectProperty.prop_of_iso (sfIntegralConstructible l E (Spec (.of D.k))) δ
      (F.obj K).property
  let P : sfIntegralConstructibleCategory l E (Spec (.of D.k)) := ⟨_, hp⟩
  let U : sfIntegralConstructibleCategory l E (Spec (.of D.k)) := ⟨_, hc.2.1⟩
  let G := pointIntegralFibre D l hl E ⋙
    (DerivedCategory.pointFgComplete (integralDualizingCoefficients l E)
      (Ideal.span {ULift.up (Padic.coefficientExtensionUniformizer l E)})).ι
  have hG : G.Full := inferInstance
  have hG' : G.Faithful := inferInstance
  have hsec : integralDualizingDerivedSections l E (Spec (.of D.k)) ≅
      pointFibreIntegralAmbient D l E :=
    (pointIntegralSections l E D.k).rightDerivedFunctorIsoMapDerivedCategory
  let A := (integralDualizingCompactSections l E D hl X).obj K
  let B := (coefficientDerivedDual (integralDualizingCoefficients l E)).obj (op A)
  let R := integralDualizingCoefficients l E
  let H := (DerivedCategory.homologyFunctor (ModuleCat.{u + 1} R) 0).obj B
  let e0 : H ≃ (ModuleCat.of R R ⟶ H) :=
    ((ModuleCat.homEquiv).trans (LinearMap.ringLmapEquivSelf R R H).toEquiv).symm
  let : Projective (ModuleCat.of R R) :=
    ModuleCat.projective_of_free (Module.Basis.singleton Unit R)
  let e1 : ((ModuleCat.of R R ⟶ H)) ≃
      ((DerivedCategory.singleFunctor (ModuleCat.{u + 1} R) 0).obj
        (ModuleCat.of R R) ⟶ B) :=
    (DerivedCategory.homSingleEquivOfProjective (ModuleCat.of R R) 0 B).symm
  let e2 := (Iso.homCongr (DerivedCategory.singleFunctorObjUnitIso (ModuleCat.{u + 1} R))
    (Iso.refl B))
  let e3 := ((ihom.adjunction A).homEquiv
    (𝟙_ (DerivedCategory (ModuleCat.{u + 1} R)))
    (𝟙_ (DerivedCategory (ModuleCat.{u + 1} R)))).symm
  let e4 : (A ⊗ 𝟙_ (DerivedCategory (ModuleCat.{u + 1} R)) ⟶
      𝟙_ (DerivedCategory (ModuleCat.{u + 1} R))) ≃
      (A ⟶ 𝟙_ (DerivedCategory (ModuleCat.{u + 1} R))) :=
    Iso.homCongr (MonoidalCategory.rightUnitor A) (Iso.refl _)
  let e5 := Iso.homCongr (hsec.app P.obj) (hu ≪≫
    DerivedCategory.singleFunctorObjUnitIso (ModuleCat.{u + 1} R)).symm
  let e6 := ((Functor.FullyFaithful.ofFullyFaithful G).homEquiv (X := P) (Y := U)).symm
  let e7 := (sfIntegralConstructible l E (Spec (.of D.k))).fullyFaithfulι.homEquiv
    (X := P) (Y := U)
  exact ⟨e0.trans (e1.trans (e2.trans (e3.trans (e4.trans (e5.trans (e6.trans e7))))))⟩

end WeilConjectures
