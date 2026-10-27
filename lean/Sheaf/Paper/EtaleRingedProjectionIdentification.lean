module

public import WeilConjectures.SixFunctors.Etale.Derived.Tensor
public import Mathlib.AlgebraicGeometry.Scheme
public import Sheaf.Paper.RingedProjectionCoherenceData
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Sheaf.CategoryTheory.ConstantScalarRestrictionTensor
import all Sheaf.CategoryTheory.ConstantScalarRestrictionTensor
public import Sheaf.Paper.ProjectionMateExact
public import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
public import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact

public import Sheaf.Paper.EtaleRingedDerivedIdentificationData
public import Sheaf.CategoryTheory.ConstantModuleDerivedComparisonData
public import Sheaf.Paper.RingedProjectionTensorAssociativity
public import WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjection
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Comparison
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat
public import Mathlib.CategoryTheory.Category.ULift
public import Mathlib.CategoryTheory.Sites.Equivalence
import Sheaf.Paper.EtaleRingedGeometricRealization
import Sheaf.Paper.EtaleRingedNormalizedConstraints
import Sheaf.Paper.EtaleRingedNativeTensorRealization
import Sheaf.Paper.EtaleRingedNativeDerivedComparison

/-! # Étale and ringed-site projection identifications

Source: Stacks Project, Cohomology on Sites, Tags 07A4, 07A6 and 0B56
(blueprint: lem-pur-etale-ringed-projection-identification).
-/

@[expose] public noncomputable section

set_option autoImplicit false
attribute [-instance] WeilConjectures.SemilinearSections.hasDerived
set_option genSizeOf false
set_option genInjectivity false
set_option genSizeOfSpec false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u w a h dU dV dW

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.Functor
open CategoryTheory.ConstantScalarRestriction CategoryTheory.ConstantModuleDerivedProjection

namespace AlgebraicGeometry.Etale.RingedProjectionIdentification

set_option Elab.async false
private theorem localizationTensor_isIso
    {D : Type dU} [Category.{dV} D] [Abelian D] [IsGrothendieckAbelian.{dV} D]
    [MonoidalCategory D] [SymmetricCategory D] [MonoidalClosed D]
    [MonoidalPreadditive D] [Abelian.HasFunctorialFlatResolution D]
    [HasDerivedCategory.{dW} D] (P Q : CochainComplex D ℤ)
    (hQ : Q.IsKFlatForTotalTensor) :
    IsIso (Functor.LaxMonoidal.μ DerivedCategory.Q P Q) := by
  exact CategoryTheory.ConstantScalarRestriction.nativeTensorIso P Q hQ

private theorem inverseTensor_naturality
    {C D : Type*} [Category C] [Category D]
    [MonoidalCategory C] [MonoidalCategory D]
    (F : C ⥤ D) [F.LaxMonoidal] {P Q P' Q' : C} (f : P ⟶ P') (g : Q ⟶ Q')
    [IsIso (Functor.LaxMonoidal.μ F P Q)] [IsIso (Functor.LaxMonoidal.μ F P' Q')] :
    F.map (f ⊗ₘ g) ≫ CategoryTheory.inv (Functor.LaxMonoidal.μ F P' Q') =
      CategoryTheory.inv (Functor.LaxMonoidal.μ F P Q) ≫ (F.map f ⊗ₘ F.map g) := by
  apply (cancel_epi (Functor.LaxMonoidal.μ F P Q)).1
  apply (cancel_mono (Functor.LaxMonoidal.μ F P' Q')).1
  simpa only [Category.assoc, IsIso.inv_hom_id, Category.comp_id,
    IsIso.hom_inv_id_assoc] using (Functor.LaxMonoidal.μ_natural F f g).symm

attribute [local irreducible] SheafOfModules.monoidalCategory

private theorem normalizedRepresentative_exists
    {D : Type dU} [Category.{dV} D] [Abelian D] [IsGrothendieckAbelian.{dV} D]
    [MonoidalCategory D] [SymmetricCategory D] [MonoidalClosed D]
    [MonoidalPreadditive D] [Abelian.HasFunctorialFlatResolution D]
    [HasDerivedCategory.{dW} D] (p : ObjectProperty (CochainComplex D ℤ))
    (h : ∀ P Q : p.FullSubcategory,
      IsIso (Functor.LaxMonoidal.μ DerivedCategory.Q P.obj Q.obj)) :
    ∃ z : p.ι.prod p.ι ⋙
        uncurry.obj ((curriedTensor D).map₂HomologicalComplex (.up ℤ) (.up ℤ) (.up ℤ)) ⋙
          DerivedCategory.Q ≅
      (p.ι ⋙ DerivedCategory.Q).prod (p.ι ⋙ DerivedCategory.Q) ⋙
        uncurry.obj (curriedTensor (DerivedCategory D)),
      ∀ P Q : p.FullSubcategory,
        Functor.LaxMonoidal.μ DerivedCategory.Q P.obj Q.obj ≫ z.hom.app (P, Q) = 𝟙 _ := by
  let μiso (P Q : p.FullSubcategory) :=
    @asIso _ _ _ _ (Functor.LaxMonoidal.μ DerivedCategory.Q P.obj Q.obj) (h P Q)
  refine ⟨NatIso.ofComponents (fun Z ↦ (μiso Z.1 Z.2).symm) ?_,
    fun P Q ↦ (μiso P Q).hom_inv_id⟩
  intro Z Z' g
  let := h Z.1 Z.2
  let := h Z'.1 Z'.2
  have hi := inverseTensor_naturality DerivedCategory.Q g.1.hom g.2.hom
  have hg : HomologicalComplex.mapBifunctorMap g.1.hom (𝟙 Z.2.obj)
      (curriedTensor D) (.up ℤ) ≫
      HomologicalComplex.mapBifunctorMap (𝟙 Z'.1.obj) g.2.hom
        (curriedTensor D) (.up ℤ) = g.1.hom ⊗ₘ g.2.hom := by
    change _ = HomologicalComplex.mapBifunctorMap _ _ _ _
    simp [HomologicalComplex.mapBifunctorMap, ← HomologicalComplex₂.total.map_comp]
  change DerivedCategory.Q.map
      (HomologicalComplex.mapBifunctorMap g.1.hom (𝟙 Z.2.obj) (curriedTensor D) (.up ℤ) ≫
        HomologicalComplex.mapBifunctorMap (𝟙 Z'.1.obj) g.2.hom
          (curriedTensor D) (.up ℤ)) ≫ (μiso Z'.1 Z'.2).inv =
    (μiso Z.1 Z.2).inv ≫
      (DerivedCategory.Q.map g.1.hom ▷ _ ≫ _ ◁ DerivedCategory.Q.map g.2.hom)
  rw [hg, ← tensorHom_def]
  exact hi

private theorem normalizedModel_exists (T : Scheme.{u})
    (Λ : Type (u + 1)) [CommRing Λ]
    [HasDerivedCategory.{u + 1} (Modules (topology T) Λ)] :
    ∃ a : SheafOfModules.RingedTensorModel (corner T Λ), ModelNormalized T Λ a := by
  let : IsGrothendieckAbelian.{u + 1} (corner T Λ).mateModules :=
    ringGrothendieck (topology T) Λ
  let : MonoidalClosed (corner T Λ).mateModules := ringClosed (topology T) Λ
  let : Abelian.HasFunctorialFlatResolution (corner T Λ).mateModules :=
    ringFlatResolutions (topology T) Λ
  obtain ⟨z, hz⟩ := normalizedRepresentative_exists (D := Modules (topology T) Λ)
    (corner T Λ).mateFlat (fun P Q ↦ localizationTensor_isIso P.obj Q.obj
      ((kflat_iff (topology T) Λ Q.obj).2.1.mp
        ((CochainComplex.isKFlatIndependentCoefficients_iff_isKFlat _).2 Q.property.1)))
  exact ⟨⟨z⟩, fun P Q hP hQ ↦ hz ⟨P, hP⟩ ⟨Q, hQ⟩⟩

attribute [local semireducible] SheafOfModules.monoidalCategory

private theorem nativeTensorData_exists (T : Scheme.{u})
    (Λ : Type (u + 1)) [CommRing Λ]
    [HasDerivedCategory.{u + 1} (Modules (topology T) Λ)]
    (m : NativeOrdinaryTensorData T Λ) : Nonempty (NativeTensorData T Λ m.braided) := by
  let := m.braided
  let : TensorPreservesCountableCoproducts (Modules (topology T) Λ) :=
    ⟨fun _ _ _ ↦ inferInstance, fun _ _ _ ↦ inferInstance⟩
  let : TensorPreservesCountableCoproducts
      (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :=
    ⟨fun _ _ _ ↦ inferInstance, fun _ _ _ ↦ inferInstance⟩
  apply CategoryTheory.ConstantScalarRestriction.abstract_derived_comparison (toNative T Λ)
    (fun P ↦ P.IsKFlatIndependentCoefficients)
  intro P hP
  have h := CategoryTheory.ConstantScalarRestriction.abstract_kflat_comparison (toNative T Λ) P
  exact h.2.2.mp (h.2.1.mpr hP)

set_option maxHeartbeats 800000 in
-- The dependent geometric and tensor witnesses require additional elaboration heartbeats.
/-- Arbitrary constant coefficients identify the specified etale and ringed projection
maps, with the canonical unbounded tensor, representative and adjunction normalizations.
Source: Stacks 03CY, 03EL, 06YU, 07A4, 07A6 and 0B56
(blueprint: lem-pur-etale-ringed-projection-identification).
Proof: scalar restriction is an exact symmetric monoidal equivalence. Transport it
along the displayed equivalence of site presentations. The constant-section ring
isomorphism identifies module scalar extension with exact etale inverse image; its
ordinary adjunction has the underlying geometric unit and counit. Localizing the
ordinary comparison gives the displayed left normalization. Compute direct image
on K-injective resolutions; the exact equivalence preserves K-injectives, giving the
right normalization. The Hom bijection is localization, the ordinary Hom adjunction,
and localization back on those representatives; hence its unit and counit agree.
On flat-term K-flat pairs both tensor comparisons insert the same scalar one on
pure tensors in every bidegree. Their signed total maps therefore coincide; resolving
descent extends equality to all unbounded inputs. The localization tensorator fixes
the corner models, and ordinary reassociation and the signed swap give the specified
constraints. Finally both projection maps are transposes of this tensor comparison
followed by counit tensor identity, so their published projection square commutes. -/
theorem etale_ringed_projection_identification {X Y : Scheme.{u}} (f : X ⟶ Y)
    (Λ : Type (u + 1)) [CommRing Λ]
    [HasDerivedCategory.{u + 1} (Modules (topology Y) Λ)]
    [HasDerivedCategory.{u + 1} (Modules (topology X) Λ)] :
    ∃ d : GeometricData (topology Y) (topology X) Λ,
      d.inverse = (presentationEquivalence Y (Type (u + 1))).inverse ⋙
        Scheme.etaleSetPullback f ⋙ (presentationEquivalence X (Type (u + 1))).functor ∧
      d.direct = transportedDirect f (Type (u + 1)) ∧
      HEq d.geometric
        ((presentationEquivalence Y (Type (u + 1))).symm.toAdjunction.comp
          ((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
            (MorphismProperty.Over.pullback @Etale ⊤ f) (Type (u + 1))
            (Y.smallGrothendieckTopology @Etale)
            (X.smallGrothendieckTopology @Etale)).comp
              (presentationEquivalence X (Type (u + 1))).toAdjunction)) ∧
      ∃ (hL : d.pullA = transportedInverse f (ModuleCat.{u + 1} Λ))
        (hR : d.pushA = transportedDirect f (ModuleCat.{u + 1} Λ)),
        HEq d.fixedAdj
          ((nativeEquivalence Y Λ).symm.toAdjunction.comp
            ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f).comp
              (nativeEquivalence X Λ).toAdjunction)) ∧
        ∃ (x : ExactData d) (o : OrdinaryIdentification d)
          (mY : NativeOrdinaryTensorData Y Λ) (mX : NativeOrdinaryTensorData X Λ)
          (cY : NativeTensorData Y Λ mY.braided) (cX : NativeTensorData X Λ mX.braided)
          (e : NativeIdentification f Λ d x o hL hR mY mX cY cX)
          (a : SheafOfModules.RingedTensorModel (corner Y Λ))
          (b : SheafOfModules.RingedTensorModel (corner X Λ)),
          ModelNormalized Y Λ a ∧ ModelNormalized X Λ b ∧
          (∃ tY : SheafOfModules.ProjectionCoherence.TensorConstraints (corner Y Λ) a,
            (∀ E F G : DerivedCategory (Modules (topology Y) Λ),
              tY.associator E F G = α_ E F G) ∧
            (∀ E F : DerivedCategory (Modules (topology Y) Λ),
              tY.symmetry E F = DerivedMonoidal.braiding'
                (DerivedCategory.Qh (C := Modules (topology Y) Λ))
                (HomotopyCategory.quasiIso (Modules (topology Y) Λ) (.up ℤ)) E F)) ∧
          (∃ tX : SheafOfModules.ProjectionCoherence.TensorConstraints (corner X Λ) b,
            (∀ E F G : DerivedCategory (Modules (topology X) Λ),
              tX.associator E F G = α_ E F G) ∧
            (∀ E F : DerivedCategory (Modules (topology X) Λ),
              tX.symmetry E F = DerivedMonoidal.braiding'
                (DerivedCategory.Qh (C := Modules (topology X) Λ))
                (HomotopyCategory.quasiIso (Modules (topology X) Λ) (.up ℤ)) E F)) ∧
          (∀ M N : DerivedCategory (Modules (topology Y) Λ),
            @Functor.OplaxMonoidal.δ _ _ _ _ _ _ d.pullR.mapDerivedCategory
              e.tensor.val.1.toOplaxMonoidal M N =
              ((edge Λ d x).tensorComparison a b).hom.app (M, N)) ∧
          PublishedProjectionSquare f Λ d x o hL hR mY mX cY cX e a b := by
  classical
  obtain ⟨d, hinverse, hdirect, hgeom, hL, hR, hAdj, x, ⟨o⟩⟩ :=
    etale_ringed_geometric_realization f Λ
  refine ⟨d, hinverse, hdirect, hgeom, hL, hR, hAdj, x, o, ?_⟩
  obtain ⟨mY⟩ := etale_ringed_native_tensor_realization Y Λ
  obtain ⟨mX⟩ := etale_ringed_native_tensor_realization X Λ
  refine ⟨mY, mX, ?_⟩
  obtain ⟨cY⟩ := nativeTensorData_exists Y Λ mY
  obtain ⟨cX⟩ := nativeTensorData_exists X Λ mX
  refine ⟨cY, cX, ?_⟩
  obtain ⟨a, ha⟩ := normalizedModel_exists Y Λ
  obtain ⟨b, hb⟩ := normalizedModel_exists X Λ
  obtain ⟨e, hδ, hprojection⟩ := etale_ringed_native_derived_comparison
    f Λ d x o hL hR mY mX cY cX hAdj a b ha hb
  refine ⟨e, a, b, ha, hb, ?_, ?_, hδ, hprojection⟩
  · exact etale_ringed_normalized_constraints Y Λ a ha
  · exact etale_ringed_normalized_constraints X Λ b hb

end AlgebraicGeometry.Etale.RingedProjectionIdentification
