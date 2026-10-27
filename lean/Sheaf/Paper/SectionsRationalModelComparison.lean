/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF groups X2 and H6
-/
module

public import Sheaf.Paper.CommonStageCompactWeilCohomology
public import Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients
public import Sheaf.Paper.SfIntegralConstructible
public import Sheaf.Paper.FiniteFieldFiber
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Sheaf.Paper.SfRationalizationKaroubi
public import Sheaf.Paper.PointFdQbarCategory
public import Sheaf.Paper.CoefficientCohomologyModules
public import Sheaf.Paper.FiniteTorAmplitudeSites
public import Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses
public import WeilConjectures.Algebra.Homology.ModuleHomComplex
public import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategory
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.AB
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
public import WeilConjectures.CategoryTheory.Abelian.Flat.ModuleCat
import Sheaf.Algebra.Homology.FieldComplexCohomologySplitting
import Mathlib.LinearAlgebra.TensorProduct.Tower
import all Sheaf.Paper.SfCompleteDirectImageReduction
import all Sheaf.Paper.SfDerivedCompleteLegacyComparison
import Sheaf.Paper.SfStrictDirectImageIntegralModels
import Sheaf.CategoryTheory.SemilinearScalarLocalization

/-! # Rational section models from an integral presentation

Source: blueprint thm-pod-point-perfectness.proof.md, Step 3, rational point complexes.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 4096
attribute [-instance] WeilConjectures.CompletedCoefficientPushforward.hasDerived
attribute [-instance] WeilConjectures.CompletedCoefficientPushforward.modAbelian
attribute [local instance 10000] HasDerivedCategory.ofIsGrothendieckAbelian
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped TensorProduct ChangeOfRings
namespace WeilConjectures

attribute [local irreducible] integralImage integralOrdinarySections integralCompactSections
  rationalImage rationalOrdinarySections rationalCompactSections
  pointIntegralFibre pointRationalFibre sfIntegralCompactSupportValue
  sfRationalCompactSupportValue

private noncomputable abbrev integralLift (R : Type u) [CommRing R] :
    ModuleCat.{u} R ⥤ ModuleCat.{u + 1} (ULift.{u + 1, u} R) :=
  ModuleCat.uliftFunctor.{u + 1, u} R ⋙
    ModuleCat.restrictScalars.{u + 1, u + 1, u}
      (ULift.ringEquiv : ULift.{u + 1, u} R ≃+* R).toRingHom

private noncomputable def tensorLiftIso (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] :
    integralLift (Padic.coefficientExtensionIntegers l E) ⋙
        ModuleCat.extendScalars.{u + 1, u + 1, u + 1} (pointIntegralToField l E) ⋙
          pointFibreCoefficientDown E ≅
      ModuleCat.extendScalars.{u, u, u}
        (algebraMap (Padic.coefficientExtensionIntegers l E) E) ⋙
          ModuleCat.uliftFunctor.{u + 1, u} E := by
  let e (M : ModuleCat.{u} (Padic.coefficientExtensionIntegers l E)) :
      ((integralLift (Padic.coefficientExtensionIntegers l E) ⋙
        ModuleCat.extendScalars.{u + 1, u + 1, u + 1} (pointIntegralToField l E) ⋙
          pointFibreCoefficientDown E).obj M) ≅
        ((ModuleCat.extendScalars.{u, u, u}
          (algebraMap (Padic.coefficientExtensionIntegers l E) E) ⋙
            ModuleCat.uliftFunctor.{u + 1, u} E).obj M) :=
    (TensorProduct.AlgebraTensorModule.uliftEquiv
      (Padic.coefficientExtensionIntegers l E) E E M).symm.toModuleIso
  refine NatIso.ofComponents e ?_
  intro M N f
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  let g := ((integralLift (Padic.coefficientExtensionIntegers l E) ⋙
    ModuleCat.extendScalars.{u + 1, u + 1, u + 1} (pointIntegralToField l E) ⋙
      pointFibreCoefficientDown E).map f ≫ (e N).hom).hom
  let h := ((e M).hom ≫ (ModuleCat.extendScalars.{u, u, u}
    (algebraMap (Padic.coefficientExtensionIntegers l E) E) ⋙
      ModuleCat.uliftFunctor.{u + 1, u} E).map f).hom
  intro x
  change g x = h x
  induction x using TensorProduct.induction_on with
  | zero => rfl
  | tmul a x => rfl
  | add x y hx hy =>
    exact (g.map_add x y).trans ((congrArg₂ (fun x y ↦ x + y) hx hy).trans
      (h.map_add x y).symm)

private noncomputable def tensorModelIso (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (P : CochainComplex (ModuleCat.{u} (Padic.coefficientExtensionIntegers l E)) ℤ) :
    (pointFibreCoefficientDown E).mapDerivedCategory.obj
        ((ModuleCat.extendScalars.{u + 1, u + 1, u + 1}
          (pointIntegralToField l E)).mapDerivedCategory.obj
            (DerivedCategory.Q.{u + 1}.obj
              (((integralLift (Padic.coefficientExtensionIntegers l E)).mapHomologicalComplex
                (.up ℤ)).obj P))) ≅
      (ModuleCat.uliftFunctor.{u + 1, u} E).mapDerivedCategory.obj
        (DerivedCategory.Q.{u}.obj
          (((ModuleCat.extendScalars.{u, u, u}
            (algebraMap (Padic.coefficientExtensionIntegers l E) E)).mapHomologicalComplex
              (.up ℤ)).obj P)) := by
  let A := integralLift (Padic.coefficientExtensionIntegers l E)
  let T := ModuleCat.extendScalars.{u + 1, u + 1, u + 1} (pointIntegralToField l E)
  let B := pointFibreCoefficientDown E
  let S := ModuleCat.extendScalars.{u, u, u}
    (algebraMap (Padic.coefficientExtensionIntegers l E) E)
  let U := ModuleCat.uliftFunctor.{u + 1, u} E
  let L := (A.mapHomologicalComplex (.up ℤ)).obj P
  let M := (T.mapHomologicalComplex (.up ℤ)).obj L
  let N := (S.mapHomologicalComplex (.up ℤ)).obj P
  let ec : (B.mapHomologicalComplex (.up ℤ)).obj M ≅
      (U.mapHomologicalComplex (.up ℤ)).obj N :=
    HomologicalComplex.Hom.isoOfComponents
      (fun i ↦ (tensorLiftIso l E).app (P.X i)) (by
        intro i j _
        exact ((tensorLiftIso l E).hom.naturality (P.d i j)).symm)
  exact B.mapDerivedCategory.mapIso (T.mapDerivedCategoryFactors.app L) ≪≫
    B.mapDerivedCategoryFactors.app M ≪≫ DerivedCategory.Q.mapIso ec ≪≫
      (U.mapDerivedCategoryFactors.app N).symm

private theorem reflectLiftIso (E : Type u) [Field E]
    (X Y : DerivedCategory.{u} (ModuleCat.{u} E))
    (e : (ModuleCat.uliftFunctor.{u + 1, u} E).mapDerivedCategory.obj X ≅
      (ModuleCat.uliftFunctor.{u + 1, u} E).mapDerivedCategory.obj Y) : Nonempty (X ≅ Y) := by
  let U := ModuleCat.uliftFunctor.{u + 1, u} E
  let eh (i : ℤ) := (U.mapDerivedCategoryHomologyFunctorIso i).app X ≪≫
    (DerivedCategory.homologyFunctor (ModuleCat.{u + 1} E) i).mapIso e ≪≫
      ((U.mapDerivedCategoryHomologyFunctorIso i).app Y).symm
  let ei (i : ℤ) := U.preimageIso (eh i)
  obtain ⟨f, hf⟩ := ((DerivedCategory.field_complex_cohomology_splitting E).2.2.1 X Y).surjective
    (fun i ↦ (ei i).hom)
  have : IsIso f := (DerivedCategory.isIso_iff (ModuleCat.{u} E) f).mpr (fun i ↦ by
    have hi : (DerivedCategory.homologyFunctor (ModuleCat.{u} E) i).map f =
        (ei i).hom := congrFun hf i
    rw [hi]
    infer_instance)
  exact ⟨asIso f⟩

private theorem pointModel (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (K : sfIntegralConstructibleCategory l E (Spec (.of D.k)))
    (P : CochainComplex (ModuleCat.{u} (Padic.coefficientExtensionIntegers l E)) ℤ)
    (e : ((pointIntegralFibre D l hl E).obj K).obj ≅ DerivedCategory.Q.{u + 1}.obj
      (((integralLift (Padic.coefficientExtensionIntegers l E)).mapHomologicalComplex
        (.up ℤ)).obj P)) :
    Nonempty (((pointRationalFibre D l hl E).obj
        ((sfRationalConstructibleLocalization l E (Spec (.of D.k))).obj K)).obj ≅
      DerivedCategory.Q.{u}.obj (((ModuleCat.extendScalars.{u, u, u}
        (algebraMap (Padic.coefficientExtensionIntegers l E) E)).mapHomologicalComplex
          (.up ℤ)).obj P)) := by
  unfold pointIntegralFibre at e
  change (pointFibreIntegralAmbient D l E).obj K.obj ≅ _ at e
  let T := ModuleCat.extendScalars.{u + 1, u + 1, u + 1} (pointIntegralToField l E)
  let B := pointFibreCoefficientDown E
  let er := pointRationalNormalization D l hl E
    ((sfRationalConstructibleLocalization l E (Spec (.of D.k))).obj K) ≪≫
      (pointFibreRationalDownIso D l E).symm.app K.obj
  apply reflectLiftIso E
  exact er ≪≫ B.mapDerivedCategory.mapIso (T.mapDerivedCategory.mapIso e) ≪≫
    tensorModelIso l E P

private theorem modelPushTowerIso (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (A : DerivedCategory (scalarReductionSource.{u, u} l E X))
    (hA : IsSfDerivedComplete l E X A)
    [HasProduct (sfDirectImageTerm l E f A)] (B : SfIntegralDirectImage l E f A) :
    Nonempty ((sfCompletedDerivedDirectImage l E f).obj A ≅ B.obj) := by
  let := completed_derived_products l E f
  let F := sfCompletedDerivedDirectImage l E f
  let a (n : ℕ) := (sfDerivedRestrictionComparison l E f n).app
    ((scalarReductionDerivedExtension.{u, u} l E X n).obj A)
  obtain ⟨hprod, δ, hδ⟩ := hA
  let := hprod
  let : HasProduct (fun n ↦ F.obj ((sfDerivedReductionRestricted l E X n).obj A)) :=
    hasProduct_of_equiv_of_iso (sfDirectImageTerm l E f A) _ (Equiv.refl ℕ) a
  obtain ⟨ε, hε⟩ := map_roos F
    (fun n ↦ (sfDerivedReductionTransition l E X n).app A) A
    (Pi.lift (fun n ↦ (sfDerivedReductionUnit l E X n).app A)) δ hδ
  let p (n : ℕ) := F.map ((sfDerivedReductionUnit l E X n).app A) ≫ (a n).hom
  have hR : ∃ hp : HasProduct (sfDirectImageTerm l E f A), let := hp
      ∃ ε, IsDerivedLimitTriangle (sfDirectImageTransition l E f A)
        (F.obj A) (Pi.lift p) ε := by
    apply roos_transport
      (X := fun n ↦ F.obj ((sfDerivedReductionRestricted l E X n).obj A))
      (Y := sfDirectImageTerm l E f A)
      (fun n ↦ F.map ((sfDerivedReductionTransition l E X n).app A))
      (sfDirectImageTransition l E f A) (Iso.refl (F.obj A)) a
      (fun n ↦ F.map ((sfDerivedReductionUnit l E X n).app A)) p
    · intro n
      dsimp only [sfDirectImageTransition, a, Iso.app_hom, Iso.app_inv]
      simp only [Iso.hom_inv_id_app_assoc]
      rfl
    · intro n
      simp only [p, Iso.refl_hom, Category.id_comp]
    · refine ⟨inferInstance, ε, ?_⟩
      simpa only [Pi.lift_π] using hε
  obtain ⟨hp, ε', hε'⟩ := hR
  have hR' : ∃ ε, IsDerivedLimitTriangle (sfDirectImageTransition l E f A)
      (F.obj A) (Pi.lift p) ε := by
    simpa only using (show ∃ ε, IsDerivedLimitTriangle (sfDirectImageTransition l E f A)
      (F.obj A) (Pi.lift p) ε from ⟨ε', hε'⟩)
  obtain ⟨ε'', hε''⟩ := hR'
  obtain ⟨e, _⟩ := roos_unique (sfDirectImageTransition l E f A)
    B.projection (Pi.lift p) B.boundary ε'' B.roos hε''
  exact ⟨e.symm⟩

/-- The rational ordinary image respects isomorphisms of integral representatives.
Source: blueprint thm-pod-point-perfectness.proof.md, Step 3, scalar-six compatibility.

Proof: the integral direct image is computed by the completed right-derived direct
image. Compare each chosen Roos vertex with that image by applying direct image to
its derived-completion triangle; the direct-image/restriction comparison identifies
all terms and transition maps. The uniqueness of the Roos vertex supplies the
comparison isomorphism. The ambient right-derived functor is additive and integral
linear, so its restriction to integral constructible objects is integral linear.
Tensor its Hom maps with the localization of the coefficient ring. Balancing and
integral linearity give a functor on the raw rational category; the identity and
composition laws hold on pure tensors and then by additivity. Map the supplied
isomorphism with this functor, and conjugate by the localized Roos comparisons at
both ends. The object values are precisely rationalImage. This works for torsion
objects and zero objects as well, and makes no finiteness assertion about a chosen
complex representative. -/
private theorem rational_ordinary_image_respects_iso
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
    [QuasiCompact (X ↘ Spec (.of D.k))] [IsSeparated (X ↘ Spec (.of D.k))]
    (K L : sfRationalConstructibleCategory l E X) (h : Nonempty (K ≅ L)) :
    Nonempty (rationalImage D l hl E X K ≅ rationalImage D l hl E X L) := by
  classical
  let : (Spec (.of D.k)).Over (Spec (.of D.k)) := ⟨𝟙 _⟩
  let : (X ↘ Spec (.of D.k)).IsOver (Spec (.of D.k)) := inferInstance
  obtain ⟨M⟩ := SfStrictDirectImageScalar.strictDirectImageIntegralModel l E D.k
    (finiteFieldDatumPrimeUnit D l hl) (X ↘ Spec (.of D.k))
  have compare (J : sfIntegralConstructibleCategory l E X) :
      Nonempty (M.image.obj J ≅ integralImage D l hl E X J) := by
    let w := sfIntegralDirectImage_constructible D.k l (finiteFieldDatumPrimeUnit D l hl)
      E (X ↘ Spec (.of D.k)) J.obj J.property
    let := w.1.choose
    let B : SfIntegralDirectImage l E (X ↘ Spec (.of D.k)) J.obj :=
      w.1.choose_spec.some
    obtain ⟨e⟩ := modelPushTowerIso l E (X ↘ Spec (.of D.k)) J.obj J.property.1 B
    have e' : (M.image.obj J).obj ≅ (integralImage D l hl E X J).obj := by
      unfold integralImage
      exact (M.reconstruction.app J).symm ≪≫ e
    exact ⟨ObjectProperty.isoMk _ e'⟩
  let R := Padic.coefficientExtensionIntegers l E
  let t := Padic.coefficientExtensionUniformizer l E
  have hs : ScalarLocalization.IsSemilinear (RingHom.id R) M.image := by
    intro A B a f
    exact M.image.map_smul a f
  let F := ScalarLocalization.extension t t (RingHom.id R)
    (IsLocalization.Away.algebraMap_isUnit t) M.image hs
  obtain ⟨a⟩ := compare K.obj
  obtain ⟨b⟩ := compare L.obj
  obtain ⟨e⟩ := h
  unfold rationalImage
  exact ⟨(sfRationalConstructibleLocalization l E (Spec (.of D.k))).mapIso a.symm ≪≫
    F.mapIso e ≪≫
      (sfRationalConstructibleLocalization l E (Spec (.of D.k))).mapIso b⟩

/-- Rationalization takes either integral section model to the corresponding field model.
Source: blueprint thm-pod-point-perfectness.proof.md, Step 3, rational point complexes.
(blueprint: lem-sf-sections-rational-model-comparison).

Proof: the ordinary rational direct image is the localization of the integral direct
image; the compact construction has the identical rationalization convention. Apply
these functors to the given representative isomorphism in the rational constructible
category. The defining comparison of the rational point fibre identifies the result
with integral sections tensored with E and descended in carrier size. Since E is the
localization of its integer ring at the uniformizer, this tensor functor is exact and
preserves the quasi-isomorphism presenting the integral section object. On the lifted
small complex P, the canonical tensor/carrier interchange sends a tensor up(x) to
up(a tensor x); its inverse is the reverse formula. The coefficient ULift equivalence
cancels, and the size-descent counit gives the displayed small E-complex. This proves
each implication for every model, including zero and shifted complexes, and for any
integral representative; it does not assert perfectness or construct a model. -/
theorem sections_rational_model_comparison
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
    [QuasiCompact (X ↘ Spec (.of D.k))] [IsSeparated (X ↘ Spec (.of D.k))]
    (c : Compactification (X ↘ Spec (.of D.k)))
    (K_E : sfRationalConstructibleCategory l E X)
    (K_R : sfIntegralConstructibleCategory l E X)
    (hrep : Nonempty ((sfRationalConstructibleLocalization l E X).obj K_R ≅ K_E))
    (P : CochainComplex (ModuleCat.{u} (Padic.coefficientExtensionIntegers l E)) ℤ) :
    let I := DerivedCategory.Q.{u + 1}.obj
      (((ModuleCat.uliftFunctor.{u + 1, u} (Padic.coefficientExtensionIntegers l E) ⋙
        ModuleCat.restrictScalars.{u + 1, u + 1, u}
          (ULift.ringEquiv : ULift.{u + 1, u} (Padic.coefficientExtensionIntegers l E) ≃+*
            Padic.coefficientExtensionIntegers l E).toRingHom
        ).mapHomologicalComplex (.up ℤ)).obj P)
    let V := DerivedCategory.Q.{u}.obj
      (((ModuleCat.extendScalars.{u, u, u}
        (algebraMap (Padic.coefficientExtensionIntegers l E) E)).mapHomologicalComplex
        (.up ℤ)).obj P)
    (Nonempty ((integralOrdinarySections D l hl E X K_R).obj ≅ I) →
      Nonempty ((rationalOrdinarySections D l hl E X K_E).obj ≅ V)) ∧
    (Nonempty ((integralCompactSections D l hl E X c K_R).obj ≅ I) →
      Nonempty ((rationalCompactSections D l hl E X c K_E).obj ≅ V)) := by
  classical
  dsimp only
  constructor
  · rintro ⟨e⟩
    unfold integralOrdinarySections at e
    change ((pointIntegralFibre D l hl E).obj
      (integralImage D l hl E X K_R)).obj ≅ _ at e
    obtain ⟨m⟩ := pointModel D l hl E (integralImage D l hl E X K_R) P e
    obtain ⟨r⟩ := rational_ordinary_image_respects_iso D l hl E X
      ((sfRationalConstructibleLocalization l E X).obj K_R) K_E hrep
    let er := (DerivedCategory.pointFiniteDimensional E).ι.mapIso
      ((pointRationalFibre D l hl E).mapIso r)
    unfold rationalImage at er
    unfold rationalOrdinarySections
    unfold rationalImage
    exact ⟨er.symm ≪≫ m⟩
  · rintro ⟨e⟩
    let : (Spec (.of D.k)).Over (Spec (.of D.k)) := ⟨𝟙 _⟩
    let : (X ↘ Spec (.of D.k)).IsOver (Spec (.of D.k)) := inferInstance
    unfold integralCompactSections at e
    let K := sfIntegralCompactSupportValue l E D.k (finiteFieldDatumPrimeUnit D l hl) c K_R
    obtain ⟨m⟩ := pointModel D l hl E K P e
    let F := sfCompactSupportFiniteFunctor l D.k (finiteFieldDatumPrimeUnit D l hl) c E
    have ev (J : sfRationalConstructibleCategory l E X) :
        F.obj J = sfRationalCompactSupportValue l E D.k
          (finiteFieldDatumPrimeUnit D l hl) c J.obj := by
      change (⟨(sfCompactSupportFiniteIntegralFunctor l D.k
        (finiteFieldDatumPrimeUnit D l hl) c E).obj J.obj⟩ :
          sfRationalConstructibleCategory l E (Spec (.of D.k))) = _
      unfold sfRationalCompactSupportValue
      rw [sfCompactSupportFiniteIntegralFunctor_obj]
      rfl
    obtain ⟨h⟩ := hrep
    let r := eqToIso (ev ((sfRationalConstructibleLocalization l E X).obj K_R)).symm ≪≫
      F.mapIso h ≪≫ eqToIso (ev K_E)
    let er := (DerivedCategory.pointFiniteDimensional E).ι.mapIso
      ((pointRationalFibre D l hl E).mapIso r)
    unfold rationalCompactSections
    unfold sfRationalCompactSupportValue at er
    unfold sfRationalCompactSupportValue
    exact ⟨er.symm ≪≫ m⟩

end WeilConjectures
