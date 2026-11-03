/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FieldRestrictionExteriorProduct
public import WeilConjectures.CategoryTheory.Monoidal.Instances.CochainComplex
public import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategory
public import WeilConjectures.FromJoel.Algebra.Homology.TotalComplexMap
public import WeilConjectures.FromJoel.CategoryTheory.Localization.DerivabilityStructure.DerivesTwo

/-!
# The lax tensor comparison for exact coefficient restriction

Source: Stacks Project, Tags 06YN, 06YP, 06YS and 0F1E. This is the tensor comparison used
in the coefficient-reduction paragraph of `lem-pur-ordinary-kunneth-finite-ring`
(blueprint: lem-pur-derived-scalar-restriction-tensor).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true

universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace AlgebraicGeometry.Etale

variable {C D : Type (u + 2)} [Category.{u + 1} C] [Category.{u + 1} D]
  [Abelian C] [Abelian D] [IsGrothendieckAbelian.{u + 1} C]
  [IsGrothendieckAbelian.{u + 1} D]
  [MonoidalCategory C] [MonoidalCategory D]
  [SymmetricCategory C] [SymmetricCategory D]
  [MonoidalClosed C] [MonoidalClosed D]
  [MonoidalPreadditive C] [MonoidalPreadditive D]
  (G : C ⥤ D) [G.Additive]
  [PreservesColimitsOfSize.{0, 0} G] (ordinary : G.LaxMonoidal)


/-- Apply the ordinary balancing map in every bidegree.
Source: Stacks 0F1E (blueprint: lem-pur-derived-scalar-restriction-tensor). -/
def scalarRestrictionTensorBicomplexMap (K L : CochainComplex C ℤ) :
    (((curriedTensor D).mapBifunctorHomologicalComplex (.up ℤ) (.up ℤ)).obj
      ((G.mapHomologicalComplex (.up ℤ)).obj K)).obj
        ((G.mapHomologicalComplex (.up ℤ)).obj L) ⟶
      (G.mapHomologicalComplex₂ (.up ℤ) (.up ℤ)).obj
        ((((curriedTensor C).mapBifunctorHomologicalComplex (.up ℤ) (.up ℤ)).obj K).obj L) :=
  by
    letI := ordinary
    exact HomologicalComplex₂.homMk (fun ⟨p, q⟩ ↦ ordinary.μ (K.X p) (L.X q))
      (fun _ _ _ _ ↦ (Functor.LaxMonoidal.μ_natural_left G _ _).symm)
      (fun _ _ _ _ ↦ (Functor.LaxMonoidal.μ_natural_right G _ _).symm)

/-- The signed total-complex tensorator of an additive lax monoidal restriction functor.
Source: Stacks 06YS and 0F1E (blueprint: lem-pur-derived-scalar-restriction-tensor).
The bicomplex map applies the ordinary tensorator in each bidegree; preservation of
countable coproducts identifies the total of the mapped bicomplex with the mapped total. -/
def scalarRestrictionChainTensor (K L : CochainComplex C ℤ) :
    (G.mapHomologicalComplex (.up ℤ)).obj K ⊗
      (G.mapHomologicalComplex (.up ℤ)).obj L ⟶
        (G.mapHomologicalComplex (.up ℤ)).obj (K ⊗ L) :=
  HomologicalComplex₂.total.map (scalarRestrictionTensorBicomplexMap G ordinary K L) (.up ℤ) ≫
    (HomologicalComplex₂.mapTotalIso G
      ((((curriedTensor C).mapBifunctorHomologicalComplex (.up ℤ) (.up ℤ)).obj K).obj L)
      (.up ℤ)).hom

/-- The total-complex comparison is the ordinary scalar balancing map on every summand.
Source: Stacks 0F1E (blueprint: lem-pur-derived-scalar-restriction-tensor).
Proof: the inclusion formula for total maps followed by the inclusion formula for
`mapTotalIso` identifies the composite with the ordinary tensorator followed by the
image of the original summand inclusion. -/
@[reassoc]
theorem scalarRestrictionChainTensor_summand (K L : CochainComplex C ℤ)
    (p q n : ℤ) (h : p + q = n) :
    HomologicalComplex.ιTensorObj ((G.mapHomologicalComplex (.up ℤ)).obj K)
        ((G.mapHomologicalComplex (.up ℤ)).obj L) p q n h ≫
        (scalarRestrictionChainTensor G ordinary K L).f n =
      ordinary.μ (K.X p) (L.X q) ≫
        G.map (HomologicalComplex.ιTensorObj K L p q n h) := by
  simp only [scalarRestrictionChainTensor, HomologicalComplex.comp_f]
  erw [HomologicalComplex₂.ιTotal_map_assoc,
    HomologicalComplex₂.ι_mapTotalXIso_hom]
  rfl

/-- Naturality of scalar balancing on total tensor complexes.
Source: Stacks 0F1E (blueprint: lem-pur-derived-scalar-restriction-tensor).
Proof: test on every tensor summand. Naturality of the ordinary tensorator gives
both sides, since the tensor map sends a summand to the corresponding summand. -/
theorem scalarRestrictionChainTensor_naturality
    {K K' L L' : CochainComplex C ℤ} (a : K ⟶ K') (b : L ⟶ L') :
    ((G.mapHomologicalComplex (.up ℤ)).map a ⊗ₘ
      (G.mapHomologicalComplex (.up ℤ)).map b) ≫
        scalarRestrictionChainTensor G ordinary K' L' =
      scalarRestrictionChainTensor G ordinary K L ≫
        (G.mapHomologicalComplex (.up ℤ)).map (a ⊗ₘ b) := by
  let := ordinary
  apply HomologicalComplex.Hom.ext
  funext n
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro p q h
  simp only [HomologicalComplex.comp_f]
  erw [CochainComplex.ιTensorObj_tensorHom_f_assoc,
    scalarRestrictionChainTensor_summand, scalarRestrictionChainTensor_summand_assoc]
  simp only [Functor.mapHomologicalComplex_map_f]
  erw [← G.map_comp, CochainComplex.ιTensorObj_tensorHom_f, G.map_comp,
    ← Functor.LaxMonoidal.μ_natural_assoc]

variable [Abelian.HasFunctorialFlatResolution C] [Abelian.HasFunctorialFlatResolution D]
  [HasDerivedCategory.{u + 1} C] [HasDerivedCategory.{u + 1} D]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]

/-- The tensor counit after exact restriction, with the exact localization factor.
Source: Stacks 06YS (blueprint: lem-pur-derived-scalar-restriction-tensor). -/
def scalarRestrictionDerivedTensorCounit :
    (((Functor.whiskeringLeft₂ _).obj (DerivedCategory.Q (C := C))).obj
      DerivedCategory.Q).obj
        ((Functor.postcompose₂.obj G.mapDerivedCategory).obj (curriedTensor _)) ⟶
      (Functor.postcompose₂.obj
        (G.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)).obj
          (curriedTensor (CochainComplex C ℤ)) :=
  (Functor.postcompose₂.obj G.mapDerivedCategory).map
      (Functor.LaxMonoidal.μNatTrans DerivedCategory.Q) ≫
    (Functor.postcompose₂.map G.mapDerivedCategoryFactors.hom).app
      (curriedTensor (CochainComplex C ℤ))

omit [IsGrothendieckAbelian.{u + 1} D] [MonoidalCategory D]
  [SymmetricCategory D] [MonoidalClosed D] [MonoidalPreadditive D]
  [PreservesColimitsOfSize.{0, 0} G] [Abelian.HasFunctorialFlatResolution D] in
/-- Applying exact restriction to derived tensor still gives the total left derived
bifunctor. Restriction need not preserve K-flat objects.
Source: Stacks 06YS (blueprint: lem-pur-derived-scalar-restriction-tensor).
Proof: use K-flat resolutions in the source coefficient category in both variables.
The source tensor counit is invertible there. Restriction carries this isomorphism
to an isomorphism, as does the exact localization factor. The resolving-class
criterion gives the universal property. -/
theorem scalarRestrictionDerivedTensor_isLeftDerived :
    ((Functor.postcompose₂.obj G.mapDerivedCategory).obj
      (curriedTensor _)).IsLeftDerivedFunctor₂ (scalarRestrictionDerivedTensorCounit G)
        (HomologicalComplex.quasiIso C (.up ℤ))
        (HomologicalComplex.quasiIso C (.up ℤ)) := by
  refine LocalizerMorphism.isLeftDerivedFunctor₂_of_isLeftDerivabilityStructure
    (HomologicalComplex.quasiIso C (.up ℤ)).localizerMorphismKFlat
    (HomologicalComplex.quasiIso C (.up ℤ)).localizerMorphismKFlat _ (fun K L ↦ ?_)
  have : IsIso (Functor.LaxMonoidal.μ DerivedCategory.Q K.obj L.obj) := by
    have hμ : IsIso (Functor.LaxMonoidal.μ DerivedCategory.Qh
        ((HomotopyCategory.quotient C (.up ℤ)).obj K.obj)
        ((HomotopyCategory.quotient C (.up ℤ)).obj L.obj)) :=
      DerivedMonoidal.isIso_counit_app_app_of_kFlat_right DerivedCategory.Qh
      (HomotopyCategory.quasiIso C (.up ℤ))
      ((HomotopyCategory.quotient C (.up ℤ)).obj K.obj)
      ((HomotopyCategory.quotient C (.up ℤ)).obj L.obj)
      ((HomotopyCategory.kFlat_quotient_obj_iff L.obj).2 L.property)
    have : IsIso (Functor.LaxMonoidal.μ
        (HomotopyCategory.quotient C (.up ℤ)) K.obj L.obj) := by
      change IsIso (𝟙 _)
      infer_instance
    change IsIso ((_ ⊗ₘ _) ≫
      (Functor.LaxMonoidal.μ DerivedCategory.Qh _ _ ≫ DerivedCategory.Qh.map _) ≫ _)
    infer_instance
  change IsIso (G.mapDerivedCategory.map
    (Functor.LaxMonoidal.μ DerivedCategory.Q K.obj L.obj) ≫
    G.mapDerivedCategoryFactors.hom.app (K.obj ⊗ L.obj))
  infer_instance

/-- Package the total-complex balancing maps as a transformation of bifunctors.
Source: Stacks 0F1E (blueprint: lem-pur-derived-scalar-restriction-tensor). -/
def scalarRestrictionChainTensorNatTrans :
    (((Functor.whiskeringLeft₂ _).obj (G.mapHomologicalComplex (.up ℤ))).obj
      (G.mapHomologicalComplex (.up ℤ))).obj (curriedTensor (CochainComplex D ℤ)) ⟶
    (Functor.postcompose₂.obj (G.mapHomologicalComplex (.up ℤ))).obj
      (curriedTensor (CochainComplex C ℤ)) where
  app K :=
    { app L := scalarRestrictionChainTensor G ordinary K L
      naturality L L' b := by
        have h := scalarRestrictionChainTensor_naturality G ordinary (𝟙 K) b
        rw [(G.mapHomologicalComplex (.up ℤ)).map_id, id_tensorHom] at h
        exact h }
  naturality K K' a := by
    apply NatTrans.ext
    funext L
    have h := scalarRestrictionChainTensor_naturality G ordinary a (𝟙 L)
    rw [(G.mapHomologicalComplex (.up ℤ)).map_id, tensorHom_id] at h
    exact h

/-- The summand normalization determines the entire cochain tensorator.
Source: Stacks 06YS (blueprint: lem-pur-derived-scalar-restriction-tensor).
Proof: maps out of the signed total are equal if they agree on each summand. -/
theorem scalarRestrictionChainTensor_unique (r : RestrictionTensorData G ordinary)
    (K L : CochainComplex C ℤ) :
    r.chain K L = scalarRestrictionChainTensor G ordinary K L := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro p q h
  rw [r.chain_summand, scalarRestrictionChainTensor_summand]

/-- The normalized lax tensorator on derived restriction of scalars.
Source: Stacks 06YS and 0F1E (blueprint: lem-pur-derived-scalar-restriction-tensor).
The universal property is applied to the restricted source tensor, so no assumption
that restriction preserves K-flat objects is introduced. -/
def scalarRestrictionDerivedTensorData : RestrictionTensorData G ordinary := by
  let U := (((Functor.whiskeringLeft₂ _).obj G.mapDerivedCategory).obj
    G.mapDerivedCategory).obj (curriedTensor (DerivedCategory D))
  let V := (Functor.postcompose₂.obj G.mapDerivedCategory).obj
    (curriedTensor (DerivedCategory C))
  let α := scalarRestrictionDerivedTensorCounit G
  let : V.IsLeftDerivedFunctor₂ α (HomologicalComplex.quasiIso C (.up ℤ))
      (HomologicalComplex.quasiIso C (.up ℤ)) :=
    scalarRestrictionDerivedTensor_isLeftDerived G
  let β : (((Functor.whiskeringLeft₂ _).obj (DerivedCategory.Q (C := C))).obj
      DerivedCategory.Q).obj U ⟶
      (Functor.postcompose₂.obj
        (G.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)).obj
          (curriedTensor (CochainComplex C ℤ)) :=
    (((Functor.whiskeringLeft₂ _).map G.mapDerivedCategoryFactors.hom).app
      (DerivedCategory.Q ⋙ G.mapDerivedCategory)).app (curriedTensor _) ≫
    (((Functor.whiskeringLeft₂ _).obj
      (G.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)).map
        G.mapDerivedCategoryFactors.hom).app (curriedTensor _) ≫
    (((Functor.whiskeringLeft₂ _).obj (G.mapHomologicalComplex (.up ℤ))).obj
      (G.mapHomologicalComplex (.up ℤ))).map
        (Functor.LaxMonoidal.μNatTrans DerivedCategory.Q) ≫
    (Functor.postcompose₂.obj DerivedCategory.Q).map
      (scalarRestrictionChainTensorNatTrans G ordinary)
  let γ : U ⟶ V := V.leftDerived₂Lift α
    (HomologicalComplex.quasiIso C (.up ℤ))
    (HomologicalComplex.quasiIso C (.up ℤ)) U β
  refine {
    map := fun P Q ↦ (γ.app P).app Q
    naturality := ?_
    chain := scalarRestrictionChainTensor G ordinary
    chain_summand := scalarRestrictionChainTensor_summand G ordinary
    normalization := ?_ }
  · intro P P' Q Q' a b
    have ha := congr_app (γ.naturality a) Q
    have hb := (γ.app P').naturality b
    change (G.mapDerivedCategory.map a ▷ G.mapDerivedCategory.obj Q) ≫
      (γ.app P').app Q = (γ.app P).app Q ≫ G.mapDerivedCategory.map (a ▷ Q) at ha
    change (G.mapDerivedCategory.obj P' ◁ G.mapDerivedCategory.map b) ≫
      (γ.app P').app Q' = (γ.app P').app Q ≫ G.mapDerivedCategory.map (P' ◁ b) at hb
    rw [MonoidalCategory.tensorHom_def, Category.assoc, hb, ← Category.assoc, ha,
      Category.assoc, ← Functor.map_comp, ← MonoidalCategory.tensorHom_def]
  · intro K L
    have hα : (α.app K).app L = G.mapDerivedCategory.map
        (Functor.LaxMonoidal.μ DerivedCategory.Q K L) ≫
          G.mapDerivedCategoryFactors.hom.app (K ⊗ L) := rfl
    have hβ : (β.app K).app L =
        (G.mapDerivedCategoryFactors.hom.app K ⊗ₘ
          G.mapDerivedCategoryFactors.hom.app L) ≫
        Functor.LaxMonoidal.μ DerivedCategory.Q
          ((G.mapHomologicalComplex (.up ℤ)).obj K)
          ((G.mapHomologicalComplex (.up ℤ)).obj L) ≫
        DerivedCategory.Q.map (scalarRestrictionChainTensor G ordinary K L) := by
      simp only [β, NatTrans.comp_app, MonoidalCategory.tensorHom_def, Category.assoc]
      rfl
    have h := V.leftDerived₂_fac_app_app α
      (HomologicalComplex.quasiIso C (.up ℤ))
      (HomologicalComplex.quasiIso C (.up ℤ)) U β K L
    rw [hα, hβ] at h
    simpa only [Category.assoc] using h

end AlgebraicGeometry.Etale
