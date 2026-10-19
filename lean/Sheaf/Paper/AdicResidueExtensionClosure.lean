/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P5
-/
module

public import Sheaf.Paper.AdicStratifiedPerfectData
import Mathlib.CategoryTheory.Triangulated.Subcategory
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat
import WeilConjectures.CategoryTheory.Abelian.Flat.ModuleCat
import Mathlib.CategoryTheory.Sites.Adjunction
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.CategoryTheory.DerivedCategory.Constructible
import Sheaf.AlgebraicGeometry.BoundedBelowProEtaleComparison
import all Sheaf.AlgebraicGeometry.DiscreteNoetherianConstructibleSerre

/-!
# Extension closure of bounded constructible etale residue origin

Source: Bhatt--Scholze, Definition 6.5.1, Remark 6.3.2 and Proposition 6.6.11.
(blueprint: lem-sfb-adic-residue-extension-closure).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite
namespace AlgebraicGeometry.Scheme

section FieldExtensions
variable {Λ : Type (u + 1)} [Field Λ] {X Y : Scheme.{u}}

private theorem field_constructible_of_shortExact
    {S : ShortComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))} (hS : S.ShortExact)
    [IsConstructibleSheaf (FA := fun M N : ModuleCat.{u + 1} Λ ↦ M →ₗ[Λ] N)
      (CA := fun M : ModuleCat.{u + 1} Λ ↦ M) S.X₁]
    [IsConstructibleSheaf (FA := fun M N : ModuleCat.{u + 1} Λ ↦ M →ₗ[Λ] N)
      (CA := fun M : ModuleCat.{u + 1} Λ ↦ M) S.X₃] :
    IsConstructibleSheaf (FA := fun M N : ModuleCat.{u + 1} Λ ↦ M →ₗ[Λ] N)
      (CA := fun M : ModuleCat.{u + 1} Λ ↦ M) S.X₂ := by
  obtain ⟨T₁, hT₁⟩ := IsConstructibleSheaf.exists_stratification
    (FA := fun M N : ModuleCat.{u + 1} Λ ↦ M →ₗ[Λ] N) (CA := fun M : ModuleCat.{u + 1} Λ ↦ M)
    (F := S.X₁)
  obtain ⟨T₃, hT₃⟩ := IsConstructibleSheaf.exists_stratification
    (FA := fun M N : ModuleCat.{u + 1} Λ ↦ M →ₗ[Λ] N) (CA := fun M : ModuleCat.{u + 1} Λ ↦ M)
    (F := S.X₃)
  refine ⟨T₁.inter T₃, fun k ↦ ?_⟩
  have h₁ := (T₁.inter_refines_left T₃).isFiniteLocallyConstantSheaf_upperStar S.X₁ hT₁ k
  have h₃ := (T₁.inter_refines_right T₃).isFiniteLocallyConstantSheaf_upperStar S.X₃ hT₃ k
  let F := Etale.upperStar (ModuleCat.{u + 1} Λ) ((T₁.inter T₃).immersion k)
  have : PreservesFiniteLimits F := inferInstance
  have : PreservesFiniteColimits F := inferInstance
  have hS' : (S.map F).ShortExact := hS.map_of_exact F
  have : IsFiniteLocallyConstantSheaf (FA := fun M N : ModuleCat.{u + 1} Λ ↦ M →ₗ[Λ] N)
      (CA := fun M : ModuleCat.{u + 1} Λ ↦ M) (S.map F).X₁ := h₁
  have : IsFiniteLocallyConstantSheaf (FA := fun M N : ModuleCat.{u + 1} Λ ↦ M →ₗ[Λ] N)
      (CA := fun M : ModuleCat.{u + 1} Λ ↦ M) (S.map F).X₃ := h₃
  exact noetherian_flc_of_shortExact hS'

private noncomputable instance (X : Scheme.{u}) (k : Type (u + 1)) [Field k] :
    ObjectProperty.IsClosedUnderExtensions
      (AlgebraicGeometry.Etale.constructibleSheaf (ModuleCat.{u + 1} k) X) where
  prop_X₂_of_shortExact {S} hS h₁ h₃ := by
    have := (AlgebraicGeometry.Etale.constructibleSheaf_iff _ _ _).mp h₁
    have := (AlgebraicGeometry.Etale.constructibleSheaf_iff _ _ _).mp h₃
    exact (AlgebraicGeometry.Etale.constructibleSheaf_iff _ _ _).mpr
      (field_constructible_of_shortExact hS)
end FieldExtensions

private theorem field_tensor_vanish
    (X : Scheme.{u}) (k : Type (u + 1)) [Field k]
    (C : CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} k)) ℤ)
    (N : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} k)) (q : ℤ)
    (h : IsZero (C.homology q)) :
    IsZero ((sfbEtaleTensorDegreeZero X k C N).homology q) := by
  let := Sheaf.monoidalCategory X.smallEtaleTopology (ModuleCat.{u + 1} k)
  have hf : ObjectProperty.flat N :=
    (AlgebraicGeometry.Etale.flat_iff_forall_flat_sheafFiber_obj N).2 (by
      intro Ω _ _ s
      exact (ModuleCat.flat_iff_flat _).2 inferInstance)
  have : PreservesFiniteLimits (MonoidalCategory.tensorRight N) := hf.2.1
  exact ((MonoidalCategory.tensorRight N).map_isZero h).of_iso
    ((C.sc q).mapHomologyIso (MonoidalCategory.tensorRight N))


private noncomputable def etaleBoundedToPlus (X : Scheme.{u})
    (k : Type (u + 1)) [CommRing k] :=
  DerivedCategory.TStructure.t.plus.lift
    (AlgebraicGeometry.Etale.DerivedCategory.boundedConstructible
      (ModuleCat.{u + 1} k) X).ι
    (fun K ↦ K.property.1.1)

private noncomputable instance (X : Scheme.{u}) (k : Type (u + 1)) [CommRing k] :
    (etaleBoundedToPlus X k).Full := by
  dsimp only [etaleBoundedToPlus]
  infer_instance

private noncomputable instance (X : Scheme.{u}) (k : Type (u + 1)) [CommRing k]
    [IsNoetherianRing k]
    [ObjectProperty.IsClosedUnderExtensions
      (AlgebraicGeometry.Etale.constructibleSheaf (ModuleCat.{u + 1} k) X)] :
    (etaleBoundedToPlus X k).CommShift ℤ := by
  dsimp only [etaleBoundedToPlus]
  infer_instance

private noncomputable instance (X : Scheme.{u}) (k : Type (u + 1)) [CommRing k]
    [IsNoetherianRing k]
    [ObjectProperty.IsClosedUnderExtensions
      (AlgebraicGeometry.Etale.constructibleSheaf (ModuleCat.{u + 1} k) X)] :
    (etaleBoundedToPlus X k).IsTriangulated := by
  dsimp only [etaleBoundedToPlus]
  infer_instance

private noncomputable instance (X : Scheme.{u}) (k : Type (u + 1)) [CommRing k] :
    PreservesFiniteLimits (sfbFixedScalarRestriction X k) := by
  let U := sheafCompose (ProEt.topology X) (forget₂ (ModuleCat.{u + 1} k) AddCommGrpCat.{u + 1})
  obtain ⟨e⟩ := sfbFixedScalarRestriction_forget_iso X k
  have : PreservesFiniteLimits (sfbFixedScalarRestriction X k ⋙ U) :=
    preservesFiniteLimits_of_natIso e.symm
  have : U.ReflectsIsomorphisms := by dsimp [U]; infer_instance
  have : PreservesFiniteLimits (U ⋙ sheafToPresheaf _ _) :=
    inferInstanceAs (PreservesFiniteLimits (sheafToPresheaf _ _ ⋙
      (Functor.whiskeringRight _ _ _).obj (forget₂ (ModuleCat.{u + 1} k) AddCommGrpCat.{u + 1})))
  have : PreservesFiniteLimits U :=
    preservesFiniteLimits_of_reflects_of_preserves _ (sheafToPresheaf _ _)
  have : ReflectsFiniteLimits U := reflectsFiniteLimits_of_reflectsIsomorphisms U
  exact preservesFiniteLimits_of_reflects_of_preserves _ U

private noncomputable instance (X : Scheme.{u}) (k : Type (u + 1)) [CommRing k] :
    PreservesFiniteColimits (sfbFixedScalarRestriction X k) := by
  let U := sheafCompose (ProEt.topology X) (forget₂ (ModuleCat.{u + 1} k) AddCommGrpCat.{u + 1})
  obtain ⟨e⟩ := sfbFixedScalarRestriction_forget_iso X k
  have : PreservesFiniteColimits (sfbFixedScalarRestriction X k ⋙ U) :=
    preservesFiniteColimits_of_natIso e.symm
  have : U.ReflectsIsomorphisms := by dsimp [U]; infer_instance
  let r : ℤ →+* k := Int.castRingHom k
  let V := ModuleCat.restrictScalars.{u + 1} r
  have : V.IsLeftAdjoint :=
    (ModuleCat.restrictCoextendScalarsAdj.{0, 0, u + 1} r).isLeftAdjoint
  have : (V ⋙ forget₂ (ModuleCat.{u + 1} ℤ) AddCommGrpCat.{u + 1}).IsLeftAdjoint := inferInstance
  have : (forget₂ (ModuleCat.{u + 1} k) AddCommGrpCat.{u + 1}).IsLeftAdjoint :=
    inferInstanceAs (V ⋙ forget₂ (ModuleCat.{u + 1} ℤ) AddCommGrpCat.{u + 1}).IsLeftAdjoint
  let J := ProEt.topology X
  let G := forget₂ (ModuleCat.{u + 1} k) AddCommGrpCat.{u + 1}
  let e : Sheaf.composeAndSheafify J G ≅ sheafCompose J G :=
    Functor.isoWhiskerLeft (sheafCompose J G)
      (sheafificationNatIso J AddCommGrpCat.{u + 1}).symm ≪≫
      Functor.rightUnitor (sheafCompose J G)
  have : (Sheaf.composeAndSheafify J G).IsLeftAdjoint := inferInstance
  have : (sheafCompose J G).IsLeftAdjoint := Functor.isLeftAdjoint_of_iso e
  have : PreservesFiniteColimits U := inferInstanceAs
    (PreservesFiniteColimits (sheafCompose J G))
  have : ReflectsFiniteColimits U := reflectsFiniteColimitsOfReflectsIsomorphisms U
  exact preservesFiniteColimits_of_reflects_of_preserves _ U

private noncomputable instance residue_change_shift (X : Scheme.{u})
    {A : Type (u + 1)} [CommRing A] (I : Ideal A) :
    (completedAdicDerivedChange.{u} X (limit.π (adicLisseRingSystem X I) (op 0))).CommShift ℤ :=
  (completedAdicChangeData.{u} X (limit.π (adicLisseRingSystem X I) (op 0))).choose_spec
    |>.choose_spec.choose_spec.choose_spec.2.2.choose_spec.choose_spec.2.1.choose

private noncomputable instance residue_change_triangle (X : Scheme.{u})
    {A : Type (u + 1)} [CommRing A] (I : Ideal A) :
    (completedAdicDerivedChange.{u} X (limit.π (adicLisseRingSystem X I) (op 0))).IsTriangulated :=
  (completedAdicChangeData.{u} X (limit.π (adicLisseRingSystem X I) (op 0))).choose_spec
    |>.choose_spec.choose_spec.choose_spec.2.2.choose_spec.choose_spec.2.1.choose_spec

attribute [local irreducible] completedAdicDerivedChange

private noncomputable def residueFunctor (X : Scheme.{u})
    {A : Type (u + 1)} [CommRing A] (I : Ideal A) :=
  completedAdicDerivedChange.{u} X (limit.π (adicLisseRingSystem X I) (op 0)) ⋙
    (sfbFixedScalarRestriction X (A ⧸ I ^ (0 + 1))).mapDerivedCategory

private noncomputable instance (X : Scheme.{u})
    {A : Type (u + 1)} [CommRing A] (I : Ideal A) :
    (residueFunctor X I).Additive := by
  dsimp only [residueFunctor]
  infer_instance

private noncomputable instance (X : Scheme.{u})
    {A : Type (u + 1)} [CommRing A] (I : Ideal A) :
    (residueFunctor X I).CommShift ℤ := by
  dsimp only [residueFunctor]
  infer_instance

private noncomputable def residueFunctorIso (X : Scheme.{u})
    {A : Type (u + 1)} [CommRing A] (I : Ideal A)
    (K : DerivedCategory (proEtaleRingModules X (adicLisseCompletedRing X I))) :
    (residueFunctor X I).obj K ≅ DerivedCategory.Q.obj (sfbResidueComplex X I K) :=
  let D := (sfbFixedScalarRestriction X (A ⧸ I ^ (0 + 1))).mapDerivedCategory
  (D.mapIso (DerivedCategory.Q.objObjPreimageIso
    ((completedAdicDerivedChange.{u} X (limit.π (adicLisseRingSystem X I) (op 0))).obj K))).symm ≪≫
    (sfbFixedScalarRestriction X (A ⧸ I ^ (0 + 1))).mapDerivedCategoryFactors.app _

private noncomputable def etaleImageFunctor (X : Scheme.{u})
    (k : Type (u + 1)) [CommRing k] :=
  etaleBoundedToPlus X k ⋙
    (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} k) X).mapDerivedCategoryPlus ⋙
      DerivedCategory.Plus.ι

private noncomputable instance (X : Scheme.{u}) (k : Type (u + 1)) [CommRing k] :
    (etaleImageFunctor X k).Full := by
  obtain ⟨hf⟩ := (ProEtale.boundedBelowComparison X k).2.1
  have := hf.full
  dsimp only [etaleImageFunctor]
  infer_instance

private noncomputable def etaleImageIso (X : Scheme.{u})
    (k : Type (u + 1)) [CommRing k]
    (C : (AlgebraicGeometry.Etale.DerivedCategory.boundedConstructible
      (ModuleCat.{u + 1} k) X).FullSubcategory) :
    (etaleImageFunctor X k).obj C ≅
      (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} k) X).mapDerivedCategory.obj C.obj :=
  ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} k) X).mapDerivedCategoryPlusCompatibility).app
    ((etaleBoundedToPlus X k).obj C)

private theorem residue_mem_image (X : Scheme.{u}) {A : Type (u + 1)} [CommRing A]
    (I : Ideal A)
    (K : DerivedCategory (proEtaleRingModules X (adicLisseCompletedRing X I)))
    (hK : IsSfbResidueConstructible X I K) :
    (etaleImageFunctor X (A ⧸ I ^ (0 + 1))).essImage ((residueFunctor X I).obj K) := by
  let k := A ⧸ I ^ (0 + 1)
  obtain ⟨C, ⟨a, b, hab, hb⟩, hc, ⟨he⟩, ht⟩ := hK
  have hbc : AlgebraicGeometry.Etale.DerivedCategory.boundedConstructible
      (ModuleCat.{u + 1} k) X (DerivedCategory.Q.obj C) := by
    refine ⟨?_, fun q ↦ ?_⟩
    · refine ⟨⟨a, (DerivedCategory.isGE_iff _ a).2 (fun q hq ↦ ?_)⟩,
        ⟨b, (DerivedCategory.isLE_iff _ b).2 (fun q hq ↦ ?_)⟩⟩
      · exact (hb q (Or.inl hq)).of_iso
          ((DerivedCategory.homologyFunctorFactors _ q).app C)
      · exact (hb q (Or.inr hq)).of_iso
          ((DerivedCategory.homologyFunctorFactors _ q).app C)
    · exact (AlgebraicGeometry.Etale.constructibleSheaf (ModuleCat.{u + 1} k) X).prop_of_iso
        ((DerivedCategory.homologyFunctorFactors _ q).app C).symm (hc q)
  refine ⟨⟨DerivedCategory.Q.obj C, hbc⟩, ⟨?_⟩⟩
  exact (etaleImageIso X k _) ≪≫
    (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} k) X).mapDerivedCategoryFactors.app C ≪≫
    he.symm ≪≫ (residueFunctorIso X I K).symm

private theorem residue_of_mem_image (X : Scheme.{u})
    {A : Type (u + 1)} [CommRing A] (I : Ideal A) (hI : I.IsMaximal)
    (K : DerivedCategory (proEtaleRingModules X (adicLisseCompletedRing X I)))
    (hK : (etaleImageFunctor X (A ⧸ I ^ (0 + 1))).essImage
      ((residueFunctor X I).obj K)) : IsSfbResidueConstructible X I K := by
  let k := A ⧸ I ^ (0 + 1)
  have : (I ^ (0 + 1)).IsMaximal := by simpa using hI
  let : Field k := Ideal.Quotient.field (I ^ (0 + 1))
  obtain ⟨E, ⟨he⟩⟩ := hK
  let C := DerivedCategory.Q.objPreimage E.obj
  let e := DerivedCategory.Q.objObjPreimageIso E.obj
  have hbc := (AlgebraicGeometry.Etale.DerivedCategory.boundedConstructible
    (ModuleCat.{u + 1} k) X).prop_of_iso e.symm E.property
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := hbc.1
  have hbound (q : ℤ) (hq : q < min a b ∨ max a b < q) : IsZero (C.homology q) := by
    apply IsZero.of_iso _ ((DerivedCategory.homologyFunctorFactors _ q).app C).symm
    rcases hq with hq | hq
    · exact (DerivedCategory.isGE_iff _ a).1 ha q (lt_of_lt_of_le hq (min_le_left _ _))
    · exact (DerivedCategory.isLE_iff _ b).1 hb q (lt_of_le_of_lt (le_max_right _ _) hq)
  refine ⟨C, ⟨min a b, max a b, le_trans (min_le_left _ _) (le_max_left _ _), hbound⟩,
    ?_, ⟨?_⟩, ?_⟩
  · intro q
    exact (AlgebraicGeometry.Etale.constructibleSheaf (ModuleCat.{u + 1} k) X).prop_of_iso
      ((DerivedCategory.homologyFunctorFactors _ q).app C) (hbc.2 q)
  · exact (residueFunctorIso X I K).symm ≪≫ he.symm ≪≫ etaleImageIso X k E ≪≫
      (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} k) X).mapDerivedCategory.mapIso e.symm ≪≫
      (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} k) X).mapDerivedCategoryFactors.app C
  · refine ⟨min a b, max a b, le_trans (min_le_left _ _) (le_max_left _ _), ?_⟩
    intro N q hq
    exact field_tensor_vanish X k C N q (hbound q hq)

/-- The residue condition is closed under extensions in the ambient derived category.
No completeness condition on the three objects is needed.
Source: Bhatt--Scholze, Definition 6.5.1 and Remark 6.3.2; Stacks Tag 09AL.
(blueprint: lem-sfb-adic-residue-extension-closure).

Proof: Compose derived reduction with exact restriction to fixed scalars. The
localization computation identifies its value with Q(sfbResidueComplex). Over the
residue field, refine the two endpoint stratifications to a common stratification.
On each stratum apply the Noetherian finite-presentation extension lemma: local
lifts of finitely many generators and finitely many relations produce a constant
middle sheaf, whose fibers are finite by exact geometric stalks. This gives
constructible extension closure over arbitrary residue fields.
Together with the existing kernel/cokernel closure this makes bounded constructible
etale complexes a triangulated category. Their bounded-below comparison is fully
faithful, so its essential image in the unbounded pro-etale derived category is
triangulated. The input residue witnesses belong to this image, hence so does the
middle vertex. Choose a representative of its etale antecedent; the derived homology
computation supplies constructibility and bounds. Finally every residue-field module
sheaf is flat by the geometric-stalk criterion. Exact tensor commutes with homology,
so the same finite interval supplies the uniform Tor bound. This argument works over
infinite residue fields and imposes no completeness condition on the three objects -/
theorem sfb_adic_residue_extension_closed
    (X : Scheme.{u}) [IsNoetherian X]
    (A : Type (u + 1)) [CommRing A] [IsNoetherianRing A]
    (I : Ideal A) (hI : I.IsMaximal ∧ ∀ J : Ideal A, J.IsMaximal → J = I)
    [IsAdicComplete I A]
    (T : Triangle (DerivedCategory (proEtaleRingModules X (adicLisseCompletedRing X I))))
    (hT : T ∈ distTriang _)
    (h₁ : IsSfbResidueConstructible X I T.obj₁)
    (h₃ : IsSfbResidueConstructible X I T.obj₃) :
    IsSfbResidueConstructible X I T.obj₂  := by
  let k := A ⧸ I ^ (0 + 1)
  have : (I ^ (0 + 1)).IsMaximal := by simpa using hI.1
  let : Field k := Ideal.Quotient.field (I ^ (0 + 1))
  have : (residueFunctor X I).IsTriangulated := by
    dsimp only [residueFunctor]
    infer_instance
  let : (etaleImageFunctor X k).CommShift ℤ := by
    dsimp only [etaleImageFunctor]
    infer_instance
  have : (etaleImageFunctor X k).IsTriangulated := by
    have : (etaleBoundedToPlus X k).IsTriangulated := inferInstance
    have : ((ProEtale.comparisonUpperStar
        (ModuleCat.{u + 1} k) X).mapDerivedCategoryPlus).IsTriangulated :=
      inferInstance
    dsimp only [etaleImageFunctor]
    infer_instance
  apply residue_of_mem_image X I hI.1
  exact (etaleImageFunctor X k).essImage.ext_of_isTriangulatedClosed₂
    ((residueFunctor X I).mapTriangle.obj T)
    ((residueFunctor X I).map_distinguished T hT)
    (residue_mem_image X I T.obj₁ h₁) (residue_mem_image X I T.obj₃ h₃)


end AlgebraicGeometry.Scheme
