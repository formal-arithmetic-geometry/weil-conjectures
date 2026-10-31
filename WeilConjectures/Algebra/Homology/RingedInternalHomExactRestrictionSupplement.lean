/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.DerivedInternalHom
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.Algebra.Homology.KFlatSupplement
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.CategoryTheory.Triangulated.Opposite.Pretriangulated
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import WeilConjectures.Algebra.Homology.RingedInternalHomCovariantExact
import WeilConjectures.Algebra.Homology.DerivedInternalHom
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.CategoryTheory.Triangulated.Opposite.Pretriangulated
import WeilConjectures.Algebra.Homology.RingedDerivedTensorHomAdjunction
import WeilConjectures.Algebra.Homology.RingedDerivedTensorNativeSupplement
import WeilConjectures.Algebra.Homology.KInjectiveHomComplexOfUniverses
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import WeilConjectures.Algebra.Homology.HomComplex
import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import WeilConjectures.Algebra.Homology.HomTensorDegreewiseIso
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.RingTheory.Flat.CategoryTheory
import WeilConjectures.SecSmoothPurity.CochainTensoratorExistence
import WeilConjectures.CategoryTheory.AlgebraicInverseImage
import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.CategoryTheory.Sites.Whiskering
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.SiteTensorFunctorialitySupplement
import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainInverseComparison
import Mathlib.CategoryTheory.Adjunction.Limits
import WeilConjectures.CategoryTheory.AdjunctionRingOperations
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib.CategoryTheory.Adjunction.Basic
import WeilConjectures.CategoryTheory.GeometricModuleConstruction
import WeilConjectures.CategoryTheory.RingedToposRingData
import WeilConjectures.CategoryTheory.RingedToposMorphismSupplement
import Mathlib.CategoryTheory.Sites.CartesianMonoidal
import Mathlib.CategoryTheory.Monoidal.CommGrp_
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
import WeilConjectures.CategoryTheory.GeometricModuleTransport
import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import WeilConjectures.Algebra.Homology.InternalHom
import WeilConjectures.Algebra.Homology.HomComplexComponents
import WeilConjectures.CategoryTheory.Monoidal.Instances.CochainComplex
import WeilConjectures.Algebra.Homology.HomotopyCategory.InternalHom
import WeilConjectures.SecSmoothPurity.ModuleTensorGenerators
import WeilConjectures.SecSmoothPurity.CochainCoefficientArrowsSupplement
import Mathlib.CategoryTheory.Triangulated.Adjunction
import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify
import WeilConjectures.Algebra.Homology.RingedInternalHomContravariantExact
import WeilConjectures.CategoryTheory.DerivedCategory.BifunctorHomHomotopyExactSupplement
import WeilConjectures.Algebra.Homology.HomComplexInternalHomComparison
import Mathlib.CategoryTheory.Triangulated.Opposite.Functor
import Mathlib.Algebra.Homology.DerivedCategory.Fractions
import WeilConjectures.CategoryTheory.Monoidal.Closed.IhomComparison
import WeilConjectures.Algebra.Homology.RingedHomRestrictionOrdinary
import WeilConjectures.Algebra.Homology.RingedHomRestrictionComparison
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMap
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import WeilConjectures.Algebra.Homology.RingedHomRestrictionComposition
import WeilConjectures.Algebra.Homology.KInjectiveRestrictLocalized
import WeilConjectures.CategoryTheory.SiteRelocalizationKInjective
import WeilConjectures.Algebra.Homology.SitePerfectModelRestrictionSupplement
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
import WeilConjectures.CategoryTheory.SiteRestrictionKInjective
import WeilConjectures.CategoryTheory.SiteModuleExtensionByZeroExact
import WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import Mathlib.CategoryTheory.Adjunction.Additive
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.FullyFaithful
import WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
import WeilConjectures.Algebra.Homology.KInjectiveHomComplexSupplement
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.Algebra.Homology.HomTensorTotal
import WeilConjectures.Algebra.Homology.HomotopyCategory.Braided
import Mathlib.CategoryTheory.Localization.DerivabilityStructure.OfFunctorialResolutions
public import WeilConjectures.Algebra.Homology.RingedInternalHomExactRestriction

/-!
# Internal derived Hom calculus on small ringed sites

Source: Stacks Project, Cohomology on Sites, Tags 08J9, 08JB and 08JC
(blueprint: lem-weil-pbc-ringed-internal-hom-exact-restriction).

The tensor functor is specified by its natural total-tensor comparison on K-flat
representatives. Restriction uses Mathlib's slice functors and their induced functors
on unbounded derived categories. The opposite triangulated structure reverses shifts.
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false

universe u w

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.Pretriangulated.Opposite

namespace CategoryTheory

private theorem ringedSite_pushforward_limits
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {G : C ⥤ D} [Functor.IsContinuous G J K]
    {S : Sheaf J RingCat.{u}} {R : Sheaf K RingCat.{u}}
    (φ : S ⟶ (G.sheafPushforwardContinuous RingCat.{u} J K).obj R) :
    PreservesFiniteLimits (SheafOfModules.pushforward.{u} φ) := by
  let T := SheafOfModules.forget.{u} S ⋙ PresheafOfModules.toPresheaf S.obj
  have : PreservesFiniteLimits (SheafOfModules.pushforward.{u} φ ⋙ T) := by
    change PreservesFiniteLimits
      ((SheafOfModules.forget.{u} R ⋙ PresheafOfModules.toPresheaf R.obj) ⋙
        (Functor.whiskeringLeft _ _ _).obj G.op)
    infer_instance
  exact preservesFiniteLimits_of_reflects_of_preserves _ T

private theorem ringedSite_pushforward_colimits
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {G : C ⥤ D} [Functor.IsContinuous G J K] [G.IsCocontinuous J K]
    {S : Sheaf J RingCat.{u}} {R : Sheaf K RingCat.{u}}
    (φ : S ⟶ (G.sheafPushforwardContinuous RingCat.{u} J K).obj R) :
    PreservesFiniteColimits (SheafOfModules.pushforward.{u} φ) := by
  let H := G.sheafPushforwardContinuous AddCommGrpCat.{u} J K
  have : PreservesColimitsOfSize.{u, u} H :=
    (G.sheafAdjunctionCocontinuous AddCommGrpCat.{u} J K).leftAdjoint_preservesColimits
  let T := SheafOfModules.toSheaf.{u} S
  have : PreservesFiniteColimits (SheafOfModules.pushforward.{u} φ ⋙ T) := by
    change PreservesFiniteColimits (SheafOfModules.toSheaf.{u} R ⋙ H)
    infer_instance
  have : ReflectsFiniteColimits T :=
    { reflects := fun _ _ _ ↦ reflectsColimitsOfShape_of_reflectsIsomorphisms }
  exact preservesFiniteColimits_of_reflects_of_preserves _ T

set_option maxHeartbeats 400000 in
-- Descending the trifunctor comparison requires several large tensor instances.
set_option backward.isDefEq.respectTransparency true in
/-- The tensor--Hom currying isomorphism is natural in all three derived objects.
The parameters P, hP, T and r specify the derived tensor in the node: total
tensor on K-flat representatives. They impose no condition on K, L or M.

Source: Stacks Project, Tag 08J9 (lemma-internal-hom).
(blueprint: lem-weil-pbc-ringed-internal-hom-exact-restriction).

Proof: Use the concrete functorial flat resolution (lem-pc-kflat-resolution) to localize the
    full subcategory P at quasi-isomorphisms, and replace M functorially by a K-injective I
    (prop-pur-kinjective-resolutions-exist). Currying identifies Hom(A, Hom(B,I)) with Hom(Tot(A
    tensor B),I): Hom out of a direct sum is a product. Expanding the differential gives d_I
    f(a,b) - (-1)^n f(d_A a,b) - (-1)^(n+p) f(a,d_B b) on both sides. The inverse is uncurrying.
    Hom(B,I) is K-injective by lem-pur-hom-kflat-into-kinjective; K-flatness computes derived
    tensor. The representative comparisons of def-pur-derived-internal-hom and
    lem-pur-rhom-well-defined descend the chain isomorphism to the localization. Its formula
    commutes with precomposition in A,B and postcomposition in I, giving the displayed naturality
    equation. -/
theorem ringedInternalHom_tensor_adjunction
    {C : Type u} [SmallCategory C] (J : GrothendieckTopology C) (R : Sheaf J CommRingCat.{u})
    [HasDerivedCategory.{w} (ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat.{u}
    RingCat.{u})).obj R))]
    (P : ObjectProperty (CochainComplex (ringedSiteModules.{u} ((sheafCompose J (forget₂
    CommRingCat.{u} RingCat.{u})).obj R)) ℤ))
    (hP : ∀ X, P X ↔ X.IsAcyclicTensorKFlat)
    (T : (DerivedCategory (ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat.{u}
    RingCat.{u})).obj R))) × (DerivedCategory (ringedSiteModules.{u} ((sheafCompose J (forget₂
    CommRingCat.{u} RingCat.{u})).obj R))) ⥤ (DerivedCategory (ringedSiteModules.{u}
    ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R))))
    (r : (P.ι.prod P.ι) ⋙ Functor.uncurry.obj
    ((@CategoryTheory.MonoidalCategory.curriedTensor (ringedSiteModules.{u} ((sheafCompose J
    (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) _
    (SheafOfModules.monoidalCategory R)).map₂HomologicalComplex
    (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ)) ⋙ DerivedCategory.Q ≅
    ((P.ι ⋙ DerivedCategory.Q).prod (P.ι ⋙ DerivedCategory.Q)) ⋙ T) :
    ∃ e : ∀ K L M : (DerivedCategory (ringedSiteModules.{u} ((sheafCompose J (forget₂
    CommRingCat.{u} RingCat.{u})).obj R))),
    (derivedInternalHom.{u, w} J R).obj (op K, (derivedInternalHom.{u, w} J R).obj (op L, M)) ≅
    (derivedInternalHom.{u, w} J R).obj (op (T.obj (K, L)), M),
    ∀ (K L M K' L' M' : (DerivedCategory (ringedSiteModules.{u} ((sheafCompose J (forget₂
    CommRingCat.{u} RingCat.{u})).obj R)))) (a : K' ⟶ K) (b : L' ⟶ L) (c : M ⟶ M'),
    (e K L M).hom ≫ (derivedInternalHom.{u, w} J R).map ((T.map (a, b)).op, c) =
    (derivedInternalHom.{u, w} J R).map (a.op, (derivedInternalHom.{u, w} J R).map (b.op, c)) ≫ (e
    K' L' M').hom := by
  classical
  let A := ringedSiteModules.{u}
    ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)
  let := SheafOfModules.monoidalCategory R
  let := SheafOfModules.symmetricCategory R
  let := SheafOfModules.monoidalClosed_kfi (R := R)
  let := SheafOfModules.monoidalPreadditive_kfi R
  let : IsGrothendieckAbelian.{u} A := SheafOfModules.isGrothendieckAbelian _
  have := SheafOfModules.hasExactColimits_int_kfi R
  let := SheafOfModules.hasFunctorialFlatResolution_kfi R
  have (X : A) : PreservesColimitsOfShape ℤ ((MonoidalCategory.curriedTensor A).flip.obj X) :=
    preservesColimitsOfShape_of_natIso (F := MonoidalCategory.tensorLeft X)
      (NatIso.ofComponents (fun Y ↦ (β_ X Y)) (by intros; simp))
  let W := HomologicalComplex.quasiIso A (.up ℤ)
  let Q : CochainComplex A ℤ ⥤ DerivedCategory A := DerivedCategory.Q
  let Λ := (inferInstance : Abelian.HasFunctorialFlatResolution A).some.reduced
  have flat (K : CochainComplex A ℤ) (hK : W.kFlat K) : P K := by
    apply (hP K).mpr
    rw [← HomotopyCategory.kFlat_quotient_obj_iff,
      HomotopyCategory.kFlat_iff_preserves_acyclic] at hK
    intro Z hZ
    exact (HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic
      (CochainComplex.mapBifunctor Z K (MonoidalCategory.curriedTensor A))).mp
        (hK _ ((HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic Z).mpr hZ)).2
  let B := ObjectProperty.lift P Λ.resolutionFunctor
    (fun K ↦ flat _ (Λ.kFlat_resolutionFunctor_obj ObjectProperty.flat.essImage_ι_le K))
  let Φ : LocalizerMorphism (W.inverseImage P.ι) W :=
    { functor := P.ι
      map := fun _ _ _ h ↦ h }
  have : Φ.IsInduced := ⟨rfl⟩
  have : Φ.IsLocalizedEquivalence :=
    Φ.isLocalizedEquivalence_of_functorial_left_resolutions (ρ := B) Λ.resolutionNatTrans
      (fun K ↦ by
        dsimp only [W]
        rw [HomologicalComplex.mem_quasiIso_iff]
        infer_instance) rfl
  have : (P.ι ⋙ Q).IsLocalization (W.inverseImage P.ι) :=
    LocalizerMorphism.IsLocalizedEquivalence.isLocalization Φ Q
  let D := DerivedCategory A
  let K := CochainComplex A ℤ
  let S := P.FullSubcategoryᵒᵖ × (P.FullSubcategoryᵒᵖ × K)
  let I := CochainComplex.kInjectiveResolutionFunctor.{u} A
  let η := CochainComplex.toKInjectiveResolution.{u} A
  let H := Functor.uncurry.obj (homComplexFunctor (R := R))
  let F := derivedInternalHom.{u, w} J R
  obtain ⟨e₀⟩ := derivedInternalHom_comparison J R I η (fun M ↦
    ⟨(CochainComplex.monoQuasiIso_toKInjectiveResolution_app.{u} A M).2,
      CochainComplex.isKInjective_kInjectiveResolutionFunctor_obj.{u} A M⟩)
  have rep (G : S ⥤ Kᵒᵖ × K) (hG : ∀ X, (G.obj X).2.IsKInjective) :
      Nonempty (G ⋙ (Q.op.prod Q) ⋙ F ≅ G ⋙ H ⋙ Q) := by
    let α := Functor.whiskerLeft G
      (Functor.whiskerRight (NatTrans.prod (𝟙 (𝟭 Kᵒᵖ)) η) (H ⋙ Q))
    have : IsIso α := by
      rw [NatTrans.isIso_iff_isIso_app]
      intro X
      have : ((G.obj X).2).IsKInjective := hG X
      have : (I.obj (G.obj X).2).IsKInjective :=
        CochainComplex.isKInjective_kInjectiveResolutionFunctor_obj.{u} A _
      have : QuasiIso (η.app (G.obj X).2) :=
        (CochainComplex.monoQuasiIso_toKInjectiveResolution_app.{u} A _).2
      apply (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).mpr
      exact quasiIso_homComplex_map (I' := (G.obj X).2)
        (I := I.obj (G.obj X).2) (η.app (G.obj X).2) (𝟙 (G.obj X).1.unop)
    exact ⟨Functor.isoWhiskerLeft G e₀ ≪≫ (asIso α).symm⟩
  let a := CategoryTheory.Prod.fst P.FullSubcategoryᵒᵖ (P.FullSubcategoryᵒᵖ × K) ⋙ P.ι.op
  let b := CategoryTheory.Prod.snd P.FullSubcategoryᵒᵖ (P.FullSubcategoryᵒᵖ × K) ⋙
    CategoryTheory.Prod.fst P.FullSubcategoryᵒᵖ K ⋙ P.ι.op
  let c := CategoryTheory.Prod.snd P.FullSubcategoryᵒᵖ (P.FullSubcategoryᵒᵖ × K) ⋙
    CategoryTheory.Prod.snd P.FullSubcategoryᵒᵖ K
  let inner := (b.prod' (c ⋙ I)) ⋙ H
  have hinner (X : S) : (inner.obj X).IsKInjective :=
    CochainComplex.isKInjective_homComplex_of_isKFlat (P.ι.obj X.2.1.unop)
      (I.obj X.2.2) ((hP _).mp X.2.1.unop.property)
  let eInner : (b.prod' c) ⋙ (Q.op.prod Q) ⋙ F ≅ inner ⋙ Q :=
    Functor.isoWhiskerLeft (b.prod' c) e₀
  let eLeft₁ := Functor.isoWhiskerRight
    (Functor.isoWhiskerLeft (Functor.diag S)
      (NatIso.prod (Iso.refl (a ⋙ Q.op)) eInner)) F
  obtain ⟨eLeft₂⟩ := rep (a.prod' inner) hinner
  let eLeft : (a ⋙ Q.op).prod' ((b.prod' c) ⋙ (Q.op.prod Q) ⋙ F) ⋙ F ≅
      (a.prod' inner) ⋙ H ⋙ Q := eLeft₁ ≪≫ eLeft₂
  let tensor := (a.prod' b) ⋙ (prodOpEquiv K (D := K)).inverse ⋙
    (Functor.uncurry.obj ((MonoidalCategory.curriedTensor A).map₂HomologicalComplex
      (.up ℤ) (.up ℤ) (.up ℤ))).op
  let eRight : (tensor ⋙ Q.op).prod' (c ⋙ Q) ⋙ F ≅
      (tensor.prod' (c ⋙ I)) ⋙ H ⋙ Q :=
    Functor.isoWhiskerLeft (tensor.prod' c) e₀
  have tensor_map (K₁ K₂ L₁ L₂ : K) (f : K₁ ⟶ L₁) (g : K₂ ⟶ L₂) :
      (Functor.uncurry.obj ((MonoidalCategory.curriedTensor A).map₂HomologicalComplex
        (.up ℤ) (.up ℤ) (.up ℤ))).map (X := (K₁, K₂)) (Y := (L₁, L₂)) (f, g) =
      HomologicalComplex.mapBifunctorMap f g (MonoidalCategory.curriedTensor A) (.up ℤ) := by
    change HomologicalComplex.mapBifunctorMap f (𝟙 K₂)
      (MonoidalCategory.curriedTensor A) (.up ℤ) ≫
      HomologicalComplex.mapBifunctorMap (𝟙 L₁) g
        (MonoidalCategory.curriedTensor A) (.up ℤ) = _
    simp only [HomologicalComplex.mapBifunctorMap, Functor.map_id, NatTrans.id_app,
      Category.id_comp, Category.comp_id, ← HomologicalComplex₂.total.map_comp]
  obtain ⟨eC, heC⟩ := homComplex_tensorTotal_iso R
  let eChain : (a.prod' inner) ⋙ H ≅ (tensor.prod' (c ⋙ I)) ⋙ H :=
    NatIso.ofComponents (fun X ↦ eC X.1.unop.obj X.2.1.unop.obj (I.obj X.2.2))
      (fun {X Y} f ↦ by
        change
          ((((homComplexFunctor (R := R)).map f.1.unop.hom.op).app
            (homComplex (R := R) X.2.1.unop.obj (I.obj X.2.2))) ≫
              ((homComplexFunctor (R := R)).obj (op Y.1.unop.obj)).map
                ((((homComplexFunctor (R := R)).map f.2.1.unop.hom.op).app
                  (I.obj X.2.2)) ≫
                    ((homComplexFunctor (R := R)).obj (op Y.2.1.unop.obj)).map
                      (I.map f.2.2))) ≫
            (eC Y.1.unop.obj Y.2.1.unop.obj (I.obj Y.2.2)).hom =
          (eC X.1.unop.obj X.2.1.unop.obj (I.obj X.2.2)).hom ≫
            ((((homComplexFunctor (R := R)).map
              ((Functor.uncurry.obj ((MonoidalCategory.curriedTensor A).map₂HomologicalComplex
                (.up ℤ) (.up ℤ) (.up ℤ))).map
                  (X := (Y.1.unop.obj, Y.2.1.unop.obj))
                  (Y := (X.1.unop.obj, X.2.1.unop.obj))
                  (f.1.unop.hom, f.2.1.unop.hom)).op).app (I.obj X.2.2)) ≫
                ((homComplexFunctor (R := R)).obj
                  (op (HomologicalComplex.mapBifunctor Y.1.unop.obj Y.2.1.unop.obj
                    (MonoidalCategory.curriedTensor A) (.up ℤ)))).map (I.map f.2.2))
        rw [tensor_map]
        exact (Category.assoc _ _ _).trans
          (heC X.1.unop.obj Y.1.unop.obj X.2.1.unop.obj Y.2.1.unop.obj
          (I.obj X.2.2) (I.obj Y.2.2) f.1.unop.hom f.2.1.unop.hom (I.map f.2.2)))
  let E := Dᵒᵖ × (Dᵒᵖ × D)
  let ad := CategoryTheory.Prod.fst Dᵒᵖ (Dᵒᵖ × D)
  let bd := CategoryTheory.Prod.snd Dᵒᵖ (Dᵒᵖ × D) ⋙ CategoryTheory.Prod.fst Dᵒᵖ D
  let cd := CategoryTheory.Prod.snd Dᵒᵖ (Dᵒᵖ × D) ⋙ CategoryTheory.Prod.snd Dᵒᵖ D
  let td := (ad.prod' bd) ⋙ (prodOpEquiv D (D := D)).inverse ⋙ T.op
  let FL : E ⥤ D := ad.prod' ((bd.prod' cd) ⋙ F) ⋙ F
  let FR : E ⥤ D := td.prod' cd ⋙ F
  let L := (P.ι ⋙ Q).op.prod ((P.ι ⋙ Q).op.prod Q)
  let p12 := ((CategoryTheory.Prod.fst P.FullSubcategoryᵒᵖ
    (P.FullSubcategoryᵒᵖ × K)).prod'
      (CategoryTheory.Prod.snd P.FullSubcategoryᵒᵖ (P.FullSubcategoryᵒᵖ × K) ⋙
        CategoryTheory.Prod.fst P.FullSubcategoryᵒᵖ K)) ⋙
          (prodOpEquiv P.FullSubcategory (D := P.FullSubcategory)).inverse
  let er : tensor ⋙ Q.op ≅ L ⋙ td :=
    Functor.isoWhiskerLeft p12 (NatIso.op r).symm
  let eRight₂ : (tensor ⋙ Q.op).prod' (c ⋙ Q) ⋙ F ≅ L ⋙ FR :=
    Functor.isoWhiskerRight
      (Functor.isoWhiskerLeft (Functor.diag S) (NatIso.prod er (Iso.refl (c ⋙ Q)))) F
  let ePre : L ⋙ FL ≅ L ⋙ FR :=
    eLeft ≪≫ Functor.isoWhiskerRight eChain Q ≪≫ eRight.symm ≪≫ eRight₂
  let WL := (W.inverseImage P.ι).op.prod ((W.inverseImage P.ι).op.prod W)
  let e : FL ≅ FR := (Localization.fullyFaithfulWhiskeringLeft L WL D).preimageIso ePre
  refine ⟨fun K L M ↦ e.app (op K, op L, M), ?_⟩
  intro K L M K' L' M' a b c
  exact (e.hom.naturality (show (op K, op L, M) ⟶ (op K', op L', M') from
    (a.op, b.op, c))).symm

attribute [local irreducible] derivedInternalHom homComplexFunctor

set_option linter.style.haveILetI false in
end CategoryTheory
