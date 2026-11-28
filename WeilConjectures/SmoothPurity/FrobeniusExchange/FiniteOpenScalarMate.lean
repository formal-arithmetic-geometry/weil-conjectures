/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.FrobeniusExchange.DerivedSquareMate
public import WeilConjectures.CategoryTheory.Adjunction.NormalizedExactDerivedUnit
public import WeilConjectures.SmoothPurity.Compact.CompactSupportOpenScalarRestriction
import all WeilConjectures.AlgebraicGeometry.Open.OpenScalarRestrictionUnit
import all WeilConjectures.SixFunctors.FrobeniusExchange.SystemScalarPullbackGeneralMate
import all WeilConjectures.SixFunctors.FrobeniusExchange.SystemOpenScalarPullbackMate
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategorySquareIsoSymm
import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Mates

/-! # Localized mates of the finite open scalar square

The finite mate of the open scalar restriction square along `j_! ⊣ j^*` is inverse to the
inverse-image mate of the direct-image coefficient comparison, and both are localizations of
ordinary squares. This gives the commuting cube of right-adjoint comparisons used for the open
scalar evaluation formula.

## Implementation details

The instances in `MixedCoordinates` restate exactness of the finite-level functors with one
side read in normalized coefficient modules and the other in constant-ring modules, the form
in which instance search meets them when localizing the cube.

The commuting cube of right-adjoint comparisons is proved face by face: every face is the
localization of an ordinary square, and the ordinary cube is the left mate of the
identity-on-sections direct-image cube.

## References

* Stacks Project, Tags 015F, 03DI and 07A6
-/

@[expose] public noncomputable section
set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Adjunction

variable {C D : Type*} [Category C] [Category D] {F : C ⥤ D} {G : D ⥤ C}

/-- If `F ⊣ G`, an endotransformation `θ` of `G ⋙ H` which fixes the image under `H` of every
unit component is the identity. -/
private theorem natTrans_eq_id_of_unit (adj : F ⊣ G) {E : Type*} [Category E] (H : C ⥤ E)
    (θ : G ⋙ H ⟶ G ⋙ H)
    (h : ∀ X, H.map (adj.unit.app X) ≫ θ.app (F.obj X) = H.map (adj.unit.app X)) :
    θ = 𝟙 _ := by
  ext Y
  have hn := θ.naturality (adj.counit.app Y)
  simp only [Functor.comp_map, Functor.comp_obj, Functor.id_obj] at hn
  calc θ.app Y = H.map (adj.unit.app (G.obj Y) ≫ G.map (adj.counit.app Y)) ≫ θ.app Y := by
        simp
    _ = 𝟙 _ := by
        rw [H.map_comp, Category.assoc, hn, reassoc_of% (h (G.obj Y)), ← H.map_comp,
          adj.right_triangle_components, H.map_id]
        rfl

end CategoryTheory.Adjunction

open WeilConjectures (compactSupportDirectModel compactSupportScalarDirectImage
  compactSupportScalarPullback compactSupportScalarPullback_isIso)

namespace AlgebraicGeometry.Scheme

universe u

variable {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]

/-- The unit-normalized change of pullback coordinates carries the tensor-pullback unit, read
in intrinsic direct-image coordinates, to the intrinsic pullback unit. -/
theorem openSquarePullbackModel_unit {X Y : Scheme.{u}} (f : X ⟶ Y)
    (N : proEtaleRingModules Y (proEtaleConstantRing Y A)) :
    (proEtaleConstantRingAdjunction A f).unit.app N ≫
        (compactSupportDirectModel f A).hom.app ((proEtaleConstantRingPullback A f).obj N) ≫
        (proEtaleConstantModuleDirectImage f A).map ((openSquarePullbackModel A f).hom.app N) =
      (sfIntrinsicConstantModuleAdjunction f A).unit.app N := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro V
  ext s
  exact (openSquarePullbackModel_existsUnique A f).exists.choose_spec N V.unop s

/-- The intrinsic inverse-image mate of the direct-image coefficient comparison is the
tensor inverse-image mate, conjugated by the unit-normalized pullback coordinate changes. -/
theorem sfIntrinsicPullback_restrictScalars_mate_app {X Y : Scheme.{u}} (f : X ⟶ Y)
    (φ : A →+* B) (M : proEtaleRingModules Y (proEtaleConstantRing Y B)) :
    ((mateEquiv (sfIntrinsicConstantModuleAdjunction f B)
        (sfIntrinsicConstantModuleAdjunction f A)).symm
        (TwoSquare.mk _ _ _ _ (proEtaleCoefficientDirectImageComparison f φ).hom)).app M =
      (openSquarePullbackModel A f).inv.app ((proEtaleCoefficientRestrictScalars Y φ).obj M) ≫
        (compactSupportScalarPullback f φ).app M ≫
        (proEtaleCoefficientRestrictScalars X φ).map ((openSquarePullbackModel B f).hom.app M) := by
  have h1 := unit_mateEquiv_symm (sfIntrinsicConstantModuleAdjunction f B)
    (sfIntrinsicConstantModuleAdjunction f A)
    (TwoSquare.mk _ _ _ _ (proEtaleCoefficientDirectImageComparison f φ).hom) M
  have hc := unit_mateEquiv_symm (proEtaleConstantRingAdjunction B f)
    (proEtaleConstantRingAdjunction A f)
    (TwoSquare.mk _ _ _ _ (Functor.whiskerRight (compactSupportDirectModel f B).hom
        (proEtaleCoefficientRestrictScalars Y φ) ≫
      (proEtaleCoefficientDirectImageComparison f φ).hom ≫
      Functor.whiskerLeft (proEtaleCoefficientRestrictScalars X φ)
        (compactSupportDirectModel f A).inv)) M
  have nd : (proEtaleConstantRingPushforward A f).map ((compactSupportScalarPullback f φ).app M) ≫
        (compactSupportDirectModel f A).hom.app
          ((proEtaleCoefficientRestrictScalars X φ).obj
            ((proEtaleConstantRingPullback B f).obj M)) =
      (compactSupportDirectModel f A).hom.app
          ((proEtaleConstantRingPullback A f).obj
            ((proEtaleCoefficientRestrictScalars Y φ).obj M)) ≫
        (proEtaleConstantModuleDirectImage f A).map ((compactSupportScalarPullback f φ).app M) :=
    (compactSupportDirectModel f A).hom.naturality _
  have nc := (proEtaleCoefficientDirectImageComparison f φ).hom.naturality
    ((openSquarePullbackModel B f).hom.app M)
  have e : compactSupportScalarPullback f φ =
      (mateEquiv (proEtaleConstantRingAdjunction B f) (proEtaleConstantRingAdjunction A f)).symm
        (TwoSquare.mk _ _ _ _ (Functor.whiskerRight (compactSupportDirectModel f B).hom
            (proEtaleCoefficientRestrictScalars Y φ) ≫
          (proEtaleCoefficientDirectImageComparison f φ).hom ≫
          Functor.whiskerLeft (proEtaleCoefficientRestrictScalars X φ)
            (compactSupportDirectModel f A).inv)) := rfl
  rw [e] at nd ⊢
  simp only [Functor.comp_map, Functor.id_obj, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, TwoSquare.mk] at h1 hc nd nc ⊢
  apply ((sfIntrinsicConstantModuleAdjunction f A).homEquiv _ _).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, ← h1,
    ← openSquarePullbackModel_unit f ((proEtaleCoefficientRestrictScalars Y φ).obj M),
    ← openSquarePullbackModel_unit f M]
  simp only [Functor.map_comp, Category.assoc]
  rw [nc, ← (proEtaleConstantModuleDirectImage f A).map_comp_assoc, Iso.hom_inv_id_app,
    CategoryTheory.Functor.map_id, Category.id_comp,
    ← reassoc_of% nd, ← reassoc_of% hc, Iso.inv_hom_id_app_assoc]

/-- The intrinsic inverse-image mate of the direct-image coefficient comparison is
invertible. -/
theorem sfIntrinsicPullback_restrictScalars_mate_isIso {X Y : Scheme.{u}} (f : X ⟶ Y)
    (φ : A →+* B) :
    IsIso ((mateEquiv (sfIntrinsicConstantModuleAdjunction f B)
        (sfIntrinsicConstantModuleAdjunction f A)).symm
        (TwoSquare.mk _ _ _ _ (proEtaleCoefficientDirectImageComparison f φ).hom)) := by
  have := compactSupportScalarPullback_isIso f φ
  have h : ((mateEquiv (sfIntrinsicConstantModuleAdjunction f B)
        (sfIntrinsicConstantModuleAdjunction f A)).symm
        (TwoSquare.mk _ _ _ _ (proEtaleCoefficientDirectImageComparison f φ).hom)) =
      Functor.whiskerLeft (proEtaleCoefficientRestrictScalars Y φ)
          (openSquarePullbackModel A f).inv ≫ compactSupportScalarPullback f φ ≫
        Functor.whiskerRight (openSquarePullbackModel B f).hom
          (proEtaleCoefficientRestrictScalars X φ) := by
    ext M : 2
    exact sfIntrinsicPullback_restrictScalars_mate_app f φ M
  rw [h]
  infer_instance


/-- The open-adjunction mate of the extension-by-zero coefficient square is a left inverse of
the inverse-image mate of the direct-image coefficient comparison. -/
theorem sfIntrinsicOpenMate_comp_pullbackMate {X Z : Scheme.{u}} (j : X ⟶ Z)
    [IsOpenImmersion j] (φ : A →+* B) :
    mateEquiv (sfIntrinsicOpenAdjunction B j) (sfIntrinsicOpenAdjunction A j)
        (TwoSquare.mk _ _ _ _ (sfOpenRestriction j φ).hom) ≫
      (mateEquiv (sfIntrinsicConstantModuleAdjunction j B)
        (sfIntrinsicConstantModuleAdjunction j A)).symm
        (TwoSquare.mk _ _ _ _ (proEtaleCoefficientDirectImageComparison j φ).hom) = 𝟙 _ := by
  apply (sfIntrinsicOpenAdjunction B j).natTrans_eq_id_of_unit
  intro M
  have hu := unit_mateEquiv (sfIntrinsicOpenAdjunction B j) (sfIntrinsicOpenAdjunction A j)
    (TwoSquare.mk _ _ _ _ (sfOpenRestriction j φ).hom) M
  have ho₀ := ProEtale.ordinaryUnit φ j M
  have ne := (openSquarePullbackModel A j).inv.naturality ((sfOpenRestriction j φ).hom.app M)
  simp only [Adjunction.ofNatIsoRight_unit, NatTrans.comp_app, Functor.whiskerLeft_app,
    Iso.symm_hom, Category.assoc, Functor.comp_obj, Functor.id_obj, TwoSquare.mk] at hu ho₀ ne
  have ho : (sfIntrinsicOpenAdjunction A j).unit.app
        ((proEtaleCoefficientRestrictScalars X φ).obj M) ≫
      (openSquarePullbackModel A j).inv.app ((sfIntrinsicExtensionByZero j A).obj
        ((proEtaleCoefficientRestrictScalars X φ).obj M)) ≫
      (proEtaleConstantRingPullback A j).map ((sfOpenRestriction j φ).hom.app M) ≫
      (compactSupportScalarPullback j φ).app ((sfIntrinsicExtensionByZero j B).obj M) =
      (proEtaleCoefficientRestrictScalars X φ).map ((sfIntrinsicOpenAdjunction B j).unit.app M ≫
        (openSquarePullbackModel B j).inv.app ((sfIntrinsicExtensionByZero j B).obj M)) :=
    ho₀
  rw [NatTrans.comp_app, reassoc_of% hu, sfIntrinsicPullback_restrictScalars_mate_app,
    reassoc_of% ne, reassoc_of% ho, ← Functor.map_comp, Category.assoc, Iso.inv_hom_id_app,
    Category.comp_id]

/-- The open-adjunction mate of the extension-by-zero coefficient square is a right inverse
of the inverse-image mate of the direct-image coefficient comparison. -/
theorem pullbackMate_comp_sfIntrinsicOpenMate {X Z : Scheme.{u}} (j : X ⟶ Z)
    [IsOpenImmersion j] (φ : A →+* B) :
    (mateEquiv (sfIntrinsicConstantModuleAdjunction j B)
        (sfIntrinsicConstantModuleAdjunction j A)).symm
        (TwoSquare.mk _ _ _ _ (proEtaleCoefficientDirectImageComparison j φ).hom) ≫
      mateEquiv (sfIntrinsicOpenAdjunction B j) (sfIntrinsicOpenAdjunction A j)
        (TwoSquare.mk _ _ _ _ (sfOpenRestriction j φ).hom) = 𝟙 _ := by
  have := sfIntrinsicPullback_restrictScalars_mate_isIso j φ
  rw [← IsIso.inv_eq_of_inv_hom_id (sfIntrinsicOpenMate_comp_pullbackMate j φ),
    IsIso.hom_inv_id]

end AlgebraicGeometry.Scheme

namespace WeilConjectures.FrobeniusExchange

set_option synthInstance.maxSize 4096

attribute [local implicit_reducible] integralCoefficientSheaf

open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.FiniteCompactScalar

universe u

section MixedCoordinates

variable (l : ℕ) [Fact l.Prime] (E L : Type u) [Field E] [Field L]
  [Algebra (Padic l) E] [Algebra (Padic l) L]
  [FiniteDimensional (Padic l) E] [FiniteDimensional (Padic l) L]
  (ι : E →ₐ[Padic l] L)

/-- Finite-level intrinsic pullback is additive from normalized coefficient modules. -/
instance normalizedSfIntrinsicPullback_additive {X Z : Scheme.{u}} (j : X ⟶ Z) (n : ℕ)
    [Finite (Padic.coefficientExtensionRing l E (n + 1))] :
    @Functor.Additive (normalizedDVRModules l E Z n)
      (X.proEtaleRingModules (X.proEtaleConstantRing (Padic.coefficientExtensionRing l E (n + 1))))
      _ _ _ _ (sfIntrinsicPullback (Padic.coefficientExtensionRing l E (n + 1)) j) :=
  sfIntrinsicPullback_additive _ _

/-- Finite-level intrinsic pullback is left exact from normalized coefficient modules. -/
instance normalizedSfIntrinsicPullback_preservesFiniteLimits {X Z : Scheme.{u}} (j : X ⟶ Z)
    (n : ℕ) [Finite (Padic.coefficientExtensionRing l E (n + 1))] :
    @PreservesFiniteLimits (normalizedDVRModules l E Z n) _
      (X.proEtaleRingModules (X.proEtaleConstantRing (Padic.coefficientExtensionRing l E (n + 1))))
      _ (sfIntrinsicPullback (Padic.coefficientExtensionRing l E (n + 1)) j) :=
  sfIntrinsicPullback_preservesFiniteLimits _ _

/-- Finite-level intrinsic pullback is right exact from normalized coefficient modules. -/
instance normalizedSfIntrinsicPullback_preservesFiniteColimits {X Z : Scheme.{u}} (j : X ⟶ Z)
    (n : ℕ) [Finite (Padic.coefficientExtensionRing l E (n + 1))] :
    @PreservesFiniteColimits (normalizedDVRModules l E Z n) _
      (X.proEtaleRingModules (X.proEtaleConstantRing (Padic.coefficientExtensionRing l E (n + 1))))
      _ (sfIntrinsicPullback (Padic.coefficientExtensionRing l E (n + 1)) j) :=
  sfIntrinsicPullback_preservesFiniteColimits _ _

/-- Finite-level scalar restriction is additive from normalized coefficient modules. -/
instance normalizedRestrictScalars_additive_constantRing (W : Scheme.{u}) (n : ℕ) :
    @Functor.Additive (normalizedDVRModules l L W n)
      (W.proEtaleRingModules (W.proEtaleConstantRing (Padic.coefficientExtensionRing l E (n + 1))))
      _ _ _ _ (proEtaleCoefficientRestrictScalars W (integralScalarQuotientMap l E L ι n)) :=
  inferInstanceAs
    (proEtaleCoefficientRestrictScalars W (integralScalarQuotientMap l E L ι n)).Additive

/-- Finite-level scalar restriction is left exact from normalized coefficient modules. -/
instance normalizedRestrictScalars_preservesFiniteLimits_constantRing (W : Scheme.{u})
    (n : ℕ) :
    @PreservesFiniteLimits (normalizedDVRModules l L W n) _
      (W.proEtaleRingModules (W.proEtaleConstantRing (Padic.coefficientExtensionRing l E (n + 1))))
      _ (proEtaleCoefficientRestrictScalars W (integralScalarQuotientMap l E L ι n)) :=
  proEtaleCoefficientRestrictScalars_preservesFiniteLimits _ _

/-- Finite-level scalar restriction is right exact from normalized coefficient modules. -/
instance normalizedRestrictScalars_preservesFiniteColimits_constantRing (W : Scheme.{u})
    (n : ℕ) :
    @PreservesFiniteColimits (normalizedDVRModules l L W n) _
      (W.proEtaleRingModules (W.proEtaleConstantRing (Padic.coefficientExtensionRing l E (n + 1))))
      _ (proEtaleCoefficientRestrictScalars W (integralScalarQuotientMap l E L ι n)) :=
  proEtaleCoefficientRestrictScalars_preservesFiniteColimits _ _

/-- Coefficient evaluation is additive into constant-ring module coordinates. -/
instance coefficientSequenceEvaluation_additive_constantRing (W : Scheme.{u}) (n : ℕ) :
    @Functor.Additive (coefficientSequenceModules l E W)
      (W.proEtaleRingModules (W.proEtaleConstantRing (Padic.coefficientExtensionRing l E (n + 1))))
      _ _ _ _ (coefficientSequenceEvaluation l E W n) :=
  coefficientSequenceEvaluation_additiveInstance l E W n

/-- Coefficient evaluation is left exact into constant-ring module coordinates. -/
instance coefficientSequenceEvaluation_limits_constantRing (W : Scheme.{u}) (n : ℕ) :
    @PreservesFiniteLimits (coefficientSequenceModules l E W) _
      (W.proEtaleRingModules (W.proEtaleConstantRing (Padic.coefficientExtensionRing l E (n + 1))))
      _ (coefficientSequenceEvaluation l E W n) :=
  coefficientSequenceEvaluation_limits l E W n

/-- Coefficient evaluation is right exact into constant-ring module coordinates. -/
instance coefficientSequenceEvaluation_colimits_constantRing (W : Scheme.{u}) (n : ℕ) :
    @PreservesFiniteColimits (coefficientSequenceModules l E W) _
      (W.proEtaleRingModules (W.proEtaleConstantRing (Padic.coefficientExtensionRing l E (n + 1))))
      _ (coefficientSequenceEvaluation l E W n) :=
  coefficientSequenceEvaluation_colimits l E W n

/-- The left adjoint of the system direct image is additive. -/
instance integralComparisonSequenceDirectImage_leftAdjoint_additive {X Y : Scheme.{u}}
    (f : X ⟶ Y) : (integralComparisonSequenceDirectImage l E f).leftAdjoint.Additive :=
  integralComparisonSequencePullbackAdditive l E f

/-- The left adjoint of the system direct image is left exact. -/
instance integralComparisonSequenceDirectImage_leftAdjoint_limits {X Y : Scheme.{u}}
    (f : X ⟶ Y) : PreservesFiniteLimits (integralComparisonSequenceDirectImage l E f).leftAdjoint :=
  integralComparisonSequencePullbackLimits l E f

/-- The left adjoint of the system direct image is right exact. -/
instance integralComparisonSequenceDirectImage_leftAdjoint_colimits {X Y : Scheme.{u}}
    (f : X ⟶ Y) :
    PreservesFiniteColimits (integralComparisonSequenceDirectImage l E f).leftAdjoint :=
  integralComparisonSequencePullbackColimits l E f

/-- Finite-level intrinsic pullback is additive on normalized coefficient modules. -/
instance normalizedSfIntrinsicPullback_additive_normalized {X Z : Scheme.{u}} (j : X ⟶ Z)
    (n : ℕ)
    [Finite (Padic.coefficientExtensionRing l E (n + 1))] :
    @Functor.Additive (normalizedDVRModules l E Z n) (normalizedDVRModules l E X n)
      _ _ _ _ (sfIntrinsicPullback (Padic.coefficientExtensionRing l E (n + 1)) j) :=
  sfIntrinsicPullback_additive _ _

/-- Finite-level intrinsic pullback is left exact on normalized coefficient modules. -/
instance normalizedSfIntrinsicPullback_preservesFiniteLimits_normalized {X Z : Scheme.{u}}
    (j : X ⟶ Z) (n : ℕ) [Finite (Padic.coefficientExtensionRing l E (n + 1))] :
    @PreservesFiniteLimits (normalizedDVRModules l E Z n) _ (normalizedDVRModules l E X n) _
      (sfIntrinsicPullback (Padic.coefficientExtensionRing l E (n + 1)) j) :=
  sfIntrinsicPullback_preservesFiniteLimits _ _

/-- Finite-level intrinsic pullback is right exact on normalized coefficient modules. -/
instance normalizedSfIntrinsicPullback_preservesFiniteColimits_normalized {X Z : Scheme.{u}}
    (j : X ⟶ Z) (n : ℕ) [Finite (Padic.coefficientExtensionRing l E (n + 1))] :
    @PreservesFiniteColimits (normalizedDVRModules l E Z n) _ (normalizedDVRModules l E X n) _
      (sfIntrinsicPullback (Padic.coefficientExtensionRing l E (n + 1)) j) :=
  sfIntrinsicPullback_preservesFiniteColimits _ _

end MixedCoordinates

/-- The commuting cube of right-adjoint comparisons for the open scalar evaluation: the
restriction/pullback square, the restriction-evaluation squares, the pullback evaluations and
the finite open restriction mate commute. -/
private theorem systemOpenScalar_rightCube (l : ℕ) [Fact l.Prime]
    (E L : Type u) [Field E] [Field L]
    [Algebra (Padic l) E] [Algebra (Padic l) L]
    [FiniteDimensional (Padic l) E] [FiniteDimensional (Padic l) L]
    (ι : E →ₐ[Padic l] L) {X Z : Scheme.{u}} (j : X ⟶ Z)
    [IsOpenImmersion j] (n : ℕ)
    [Finite (Padic.coefficientExtensionRing l E (n + 1))]
    [Finite (Padic.coefficientExtensionRing l L (n + 1))] :
    ∀ (ρX : TwoSquare
        (SemilinearSections.resD (integralComparisonSequenceScalarMap l E L ι X))
        (coefficientSequenceDerivedEvaluation l L X n)
        (coefficientSequenceDerivedEvaluation l E X n)
        (pbcDerivedRestrict (scalarRingMap (integralScalarQuotientMap l E L ι n) X)))
      (ρZ : TwoSquare
        (SemilinearSections.resD (integralComparisonSequenceScalarMap l E L ι Z))
        (coefficientSequenceDerivedEvaluation l L Z n)
        (coefficientSequenceDerivedEvaluation l E Z n)
        (pbcDerivedRestrict (scalarRingMap (integralScalarQuotientMap l E L ι n) Z))),
      HEq ρX (SemilinearSections.restrictionEvaluation (ProEt.topology X)
        (integralCoefficientCommRingSheaf l E X) (coefficientSequenceCommRingTransition l E X)
        (integralCoefficientCommRingSheaf l L X) (coefficientSequenceCommRingTransition l L X)
        (integralScalarQuotientSheafMap l E L ι X)
        (scalarQuotient_compatible l E L ι X) n).hom →
      HEq ρZ (SemilinearSections.restrictionEvaluation (ProEt.topology Z)
        (integralCoefficientCommRingSheaf l E Z) (coefficientSequenceCommRingTransition l E Z)
        (integralCoefficientCommRingSheaf l L Z) (coefficientSequenceCommRingTransition l L Z)
        (integralScalarQuotientSheafMap l E L ι Z)
        (scalarQuotient_compatible l E L ι Z) n).hom →
      ∀ M, (coefficientSequenceDerivedEvaluation l E X n).map
          ((Functor.mapDerivedCategorySquareIso
            (@asIso _ _ _ _ (sequenceRestrictionPullbackInv l E L ι j)
              (sequenceRestrictionPullbackInv_isIso l E L ι j)).symm).inv.app M) ≫
        ρX.app ((integralComparisonDerivedSequencePullback l L j).obj M) ≫
        (pbcDerivedRestrict (scalarRingMap (integralScalarQuotientMap l E L ι n) X)).map
          ((systemPullEvaluation l L j n).inv.app M) ≫
        ((mateEquiv (SheafOfModules.OpenTensorNormalization.exactDerivedAdjunction
            (sfIntrinsicOpenAdjunction (Padic.coefficientExtensionRing l L (n + 1)) j))
          (SheafOfModules.OpenTensorNormalization.exactDerivedAdjunction
            (sfIntrinsicOpenAdjunction (Padic.coefficientExtensionRing l E (n + 1)) j)))
          (TwoSquare.mk _ _ _ _ (Functor.mapDerivedCategorySquareIso
            (sfOpenRestriction j (integralScalarQuotientMap l E L ι n))).hom)).app
          ((coefficientSequenceDerivedEvaluation l L Z n).obj M) =
        (systemPullEvaluation l E j n).inv.app
          ((SemilinearSections.resD (integralComparisonSequenceScalarMap l E L ι Z)).obj M) ≫
        (sfIntrinsicPullback (Padic.coefficientExtensionRing l E (n + 1)) j).mapDerivedCategory.map
          (ρZ.app M) := by
  intro ρX ρZ hρX hρZ M
  obtain ⟨ρX₀, hX₀, hΔX⟩ := systemRestrictionEvaluation_isDerivedSquareOf l E L ι X n ρX hρX
  obtain ⟨ρZ₀, hZ₀, hΔZ⟩ := systemRestrictionEvaluation_isDerivedSquareOf l E L ι Z n ρZ hρZ
  have pdE : ∀ (N : coefficientSequenceModules l E X) (U : Z.ProEtᵒᵖ)
      (y : ((integralComparisonSequenceDirectImage l E j ⋙
        coefficientSequenceEvaluation l E Z n).obj N).val.obj U),
      HEq ((((eqToIso (systemDirectEvaluationOrdinary_eq l E j n)).hom.app N).val.app U).hom y)
        y := by
    intro N U y
    exact eqToIso_hom_app_val_app_heq l E (systemDirectEvaluationOrdinary_eq l E j n) N U y
  have pdL : ∀ (N : coefficientSequenceModules l L X) (U : Z.ProEtᵒᵖ)
      (y : ((integralComparisonSequenceDirectImage l L j ⋙
        coefficientSequenceEvaluation l L Z n).obj N).val.obj U),
      HEq ((((eqToIso (systemDirectEvaluationOrdinary_eq l L j n)).hom.app N).val.app U).hom y)
        y := by
    intro N U y
    exact eqToIso_hom_app_val_app_heq l L (systemDirectEvaluationOrdinary_eq l L j n) N U y
  have hright (N : coefficientSequenceModules l L X) :
      (coefficientSequenceEvaluation l E Z n).map
          ((sequenceScalarPullbackRight l E L ι j).inv.app N) ≫
        (eqToIso (systemDirectEvaluationOrdinary_eq l E j n)).hom.app
          ((sequenceRestriction l E L ι X).obj N) ≫
        (proEtaleConstantModuleDirectImage j (Padic.coefficientExtensionRing l E (n + 1))).map
          (ρX₀.app N) =
      ρZ₀.app ((integralComparisonSequenceDirectImage l L j).obj N) ≫
        (proEtaleCoefficientRestrictScalars Z (integralScalarQuotientMap l E L ι n)).map
          ((eqToIso (systemDirectEvaluationOrdinary_eq l L j n)).hom.app N) ≫
        (proEtaleCoefficientDirectImageComparison j
          (integralScalarQuotientMap l E L ι n)).hom.app
          ((coefficientSequenceEvaluation l L X n).obj N) := by
    generalize (eqToIso (systemDirectEvaluationOrdinary_eq l E j n)).hom = dE at pdE ⊢
    generalize (eqToIso (systemDirectEvaluationOrdinary_eq l L j n)).hom = dL at pdL ⊢
    exact ordinaryDirectRestrictionEvaluation_cube l E L ι j n dE pdE dL pdL ρZ₀ hZ₀ ρX₀ hX₀ N
  generalize hdE : (eqToIso (systemDirectEvaluationOrdinary_eq l E j n)).hom = dE at hright
  generalize hdL : (eqToIso (systemDirectEvaluationOrdinary_eq l L j n)).hom = dL at hright
  have hleft := leftMate_cube_of_rightCube
    (Adjunction.ofIsRightAdjoint (integralComparisonSequenceDirectImage l E j))
    (Adjunction.ofIsRightAdjoint (integralComparisonSequenceDirectImage l L j))
    (sfIntrinsicConstantModuleAdjunction j (Padic.coefficientExtensionRing l E (n + 1)))
    (sfIntrinsicConstantModuleAdjunction j (Padic.coefficientExtensionRing l L (n + 1)))
    _ _ _ _ ρZ₀ ρX₀ hright
  subst hdE hdL
  have := systemPullEvaluationOrdinaryInv_isIso l E j n
  have := systemPullEvaluationOrdinaryInv_isIso l L j n
  have := sequenceRestrictionPullbackInv_isIso l E L ι j
  obtain ⟨Δq, hΔq⟩ := Functor.exists_isDerivedSquareOf
    ((mateEquiv (sfIntrinsicConstantModuleAdjunction j (Padic.coefficientExtensionRing l L (n + 1)))
      (sfIntrinsicConstantModuleAdjunction j (Padic.coefficientExtensionRing l E (n + 1)))).symm
      (TwoSquare.mk _ _ _ _
        (proEtaleCoefficientDirectImageComparison j (integralScalarQuotientMap l E L ι n)).hom))
  have hcube := @Functor.derivedCube_of_isDerivedSquareOf
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    _ _ _ _ _ _
    hleft _
    (@Functor.isDerivedSquareOf_mapDerivedCategorySquareIso
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
      (asIso (systemPullEvaluationOrdinaryInv l E j n))) _
    (@Functor.isDerivedSquareOf_mapDerivedCategorySquareIso
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
      (asIso (systemPullEvaluationOrdinaryInv l L j n))) _
    (@Functor.isDerivedSquareOf_mapDerivedCategorySquareIso
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
      (asIso (sequenceRestrictionPullbackInv l E L ι j))) _ hΔq _ hΔZ _ hΔX M
  have hψ := Functor.isDerivedSquareOf_mateEquiv
    (sfIntrinsicOpenAdjunction (Padic.coefficientExtensionRing l L (n + 1)) j)
    (sfIntrinsicOpenAdjunction (Padic.coefficientExtensionRing l E (n + 1)) j)
    (sfOpenRestriction j (integralScalarQuotientMap l E L ι n)).hom
    (Functor.isDerivedSquareOf_mapDerivedCategorySquareIso
      (sfOpenRestriction j (integralScalarQuotientMap l E L ι n)))
  have hinv := Functor.isDerivedSquareOf_comp_eq_id
    (pullbackMate_comp_sfIntrinsicOpenMate j (integralScalarQuotientMap l E L ι n)) hΔq hψ
  have hK := congr_app hinv ((coefficientSequenceDerivedEvaluation l L Z n).obj M)
  rw [NatTrans.comp_app, NatTrans.id_app] at hK
  rw [Functor.mapDerivedCategorySquareIso_symm, Iso.symm_inv]
  refine (Iso.eq_inv_comp ((systemPullEvaluation l E j n).app _)).mpr ?_
  have h4 : Δq.app ((coefficientSequenceDerivedEvaluation l L Z n).obj M) ≫
      (X.proEtaleCoefficientRestrictScalars
        (integralScalarQuotientMap l E L ι n)).mapDerivedCategory.map
        ((systemPullEvaluation l L j n).hom.app M) ≫
      (X.proEtaleCoefficientRestrictScalars
        (integralScalarQuotientMap l E L ι n)).mapDerivedCategory.map
        ((systemPullEvaluation l L j n).inv.app M) ≫
      (mateEquiv
        (sfIntrinsicOpenAdjunction (Padic.coefficientExtensionRing l L (n + 1))
          j).mapExactDerivedCategory
        (sfIntrinsicOpenAdjunction (Padic.coefficientExtensionRing l E (n + 1))
          j).mapExactDerivedCategory
        (TwoSquare.mk _ _ _ _ (Functor.mapDerivedCategorySquareIso
          (sfOpenRestriction j (integralScalarQuotientMap l E L ι n))).hom)).app
        ((coefficientSequenceDerivedEvaluation l L Z n).obj M) = 𝟙 _ := by
    rw [← Functor.map_comp_assoc, Iso.hom_inv_id_app]
    erw [CategoryTheory.Functor.map_id, Category.id_comp]
    exact hK
  have hc2 : (systemPullEvaluation l E j n).hom.app
        ((SemilinearSections.resD (integralComparisonSequenceScalarMap l E L ι Z)).obj M) ≫
      (coefficientSequenceDerivedEvaluation l E X n).map
        ((Functor.mapDerivedCategorySquareIso
          (asIso (sequenceRestrictionPullbackInv l E L ι j))).hom.app M) ≫
      ρX.app ((integralComparisonDerivedSequencePullback l L j).obj M) =
      (sfIntrinsicPullback (Padic.coefficientExtensionRing l E (n + 1)) j).mapDerivedCategory.map
          (ρZ.app M) ≫
        Δq.app ((coefficientSequenceDerivedEvaluation l L Z n).obj M) ≫
        (pbcDerivedRestrict (scalarRingMap (integralScalarQuotientMap l E L ι n) X)).map
          ((systemPullEvaluation l L j n).hom.app M) :=
    hcube
  have h4' : Δq.app ((coefficientSequenceDerivedEvaluation l L Z n).obj M) ≫
      (pbcDerivedRestrict (scalarRingMap (integralScalarQuotientMap l E L ι n) X)).map
        ((systemPullEvaluation l L j n).hom.app M) ≫
      (pbcDerivedRestrict (scalarRingMap (integralScalarQuotientMap l E L ι n) X)).map
        ((systemPullEvaluation l L j n).inv.app M) ≫
      ((mateEquiv (SheafOfModules.OpenTensorNormalization.exactDerivedAdjunction
          (sfIntrinsicOpenAdjunction (Padic.coefficientExtensionRing l L (n + 1)) j))
        (SheafOfModules.OpenTensorNormalization.exactDerivedAdjunction
          (sfIntrinsicOpenAdjunction (Padic.coefficientExtensionRing l E (n + 1)) j)))
        (TwoSquare.mk _ _ _ _ (Functor.mapDerivedCategorySquareIso
          (sfOpenRestriction j (integralScalarQuotientMap l E L ι n))).hom)).app
        ((coefficientSequenceDerivedEvaluation l L Z n).obj M) = 𝟙 _ :=
    h4
  have hfin : (systemPullEvaluation l E j n).hom.app
        ((SemilinearSections.resD (integralComparisonSequenceScalarMap l E L ι Z)).obj M) ≫
      (coefficientSequenceDerivedEvaluation l E X n).map
        ((Functor.mapDerivedCategorySquareIso
          (asIso (sequenceRestrictionPullbackInv l E L ι j))).hom.app M) ≫
      ρX.app ((integralComparisonDerivedSequencePullback l L j).obj M) ≫
      (pbcDerivedRestrict (scalarRingMap (integralScalarQuotientMap l E L ι n) X)).map
        ((systemPullEvaluation l L j n).inv.app M) ≫
      ((mateEquiv (SheafOfModules.OpenTensorNormalization.exactDerivedAdjunction
          (sfIntrinsicOpenAdjunction (Padic.coefficientExtensionRing l L (n + 1)) j))
        (SheafOfModules.OpenTensorNormalization.exactDerivedAdjunction
          (sfIntrinsicOpenAdjunction (Padic.coefficientExtensionRing l E (n + 1)) j)))
        (TwoSquare.mk _ _ _ _ (Functor.mapDerivedCategorySquareIso
          (sfOpenRestriction j (integralScalarQuotientMap l E L ι n))).hom)).app
        ((coefficientSequenceDerivedEvaluation l L Z n).obj M) =
      (sfIntrinsicPullback (Padic.coefficientExtensionRing l E (n + 1)) j).mapDerivedCategory.map
          (ρZ.app M) := by
    refine (congrArg (fun g ↦ _ ≫ g) (Category.assoc _ _ _)).symm.trans
      ((Category.assoc _ _ _).symm.trans ?_)
    refine (congrArg (fun g ↦ g ≫ _) hc2).trans ((Category.assoc _ _ _).trans ?_)
    refine (congrArg (fun g ↦ _ ≫ g) (Category.assoc _ _ _)).trans ?_
    exact (congrArg (fun g ↦ _ ≫ g) h4').trans (Category.comp_id _)
  exact hfin

end WeilConjectures.FrobeniusExchange
