/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteExceptionalTensor.FiniteExceptionalCoefficientTensor
public import Mathlib.Lean.Meta.CongrTheorems
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ReductionExtendScalars
public import WeilConjectures.AlgebraicGeometry.CoefficientScalarRepresentatives.CoefficientScalarRepresentatives
public import WeilConjectures.AlgebraicGeometry.Compact.CompactSupportCoefficientChange
public import WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinary.FiniteCtfInternalEtaleRealization
public import WeilConjectures.AlgebraicGeometry.FiniteOrAlgebraicallyClosed.OrdinaryFiniteCompactSupportScalarProjectionNormalization
public import WeilConjectures.AlgebraicGeometry.FiniteOrAlgebraicallyClosed.OrdinaryFiniteScalarUnitSymmetry
public import WeilConjectures.CategoryTheory.Derived.DerivedTensorRightExact
public import WeilConjectures.CategoryTheory.DerivedCategory.Adjunction
public import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
public import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Unique
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ProjectionFormula

/-!
# Compact-support scalar projection coherence

Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/sec-smooth-purity/
sec-sp-grp-ladic-summary/sec-change-of-finite-coefficients/sk-lem-sp-reduction/
sk-lem-sp-reduction-compatibilities.proof.md, Proof (3), Tensor map
(blueprint: lem-sp-finite-or-algebraically-closed-compact-support-scalar-projection-coherence).

The statement uses the existing fixed-scalar presentation of the ordinary constant-ring
pro-etale derived categories and its recorded operations and canonical maps from
`AlgebraicGeometry.ProEtale.FiniteExceptionalTensor` (owner node
lem-pur-exceptional-coefficient-comparison): `D`, `ctf`, the scalar functor `scalar`
(the recorded `scalarExtensionFunctor` of det-sp-scalar-extension-functor transported along
the finite-coefficient equivalences), exact restriction `restrict`, compact support
`support` = Rp_* j_!, pullback `pull`, the Koszul `braiding`, the ordered projection map
`projection`, and the adjunction mates `scalarTensor`, `scalarUnit`, `scalarPull`
(= lambda_f⁻¹), `compactComparison` (= b) and `sigma`.  None of these is redefined here.
Those definitions involve no property of the base field, so they serve the finite or
algebraically closed base of this node.  The statement includes nonflat coefficient maps
and zero rings.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale.FiniteExceptionalTensor
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.FiniteOrAlgebraicallyClosed

end

section Ordinary
variable {C D : Type (u + 2)} [Category.{u + 1} C] [Category.{u + 1} D]
  [Abelian C] [Abelian D] [IsGrothendieckAbelian.{u + 1} C]
  [IsGrothendieckAbelian.{u + 1} D]
  [MonoidalCategory C] [MonoidalCategory D] [SymmetricCategory C] [SymmetricCategory D]
  [MonoidalClosed C] [MonoidalClosed D] [MonoidalPreadditive C] [MonoidalPreadditive D]
  (E : C ⥤ D) (U : D ⥤ C) [E.Additive] [U.Additive]
  [E.Monoidal] [U.LaxMonoidal] [PreservesColimitsOfSize.{0, 0} E]
  [PreservesColimitsOfSize.{0, 0} U] (adj : E ⊣ U) [adj.IsMonoidal]

set_option maxHeartbeats 800000 in
-- The normalization compares total tensors and several localization factors.
private theorem ordinary_tensor_unit
    (K L : CochainComplex C ℤ) :
    let a := adj.mapHomologicalComplex (.up ℤ)
    (a.unit.app K ⊗ₘ a.unit.app L) ≫
        scalarRestrictionChainTensor U inferInstance
          ((E.mapHomologicalComplex (.up ℤ)).obj K)
          ((E.mapHomologicalComplex (.up ℤ)).obj L) =
      a.unit.app (K ⊗ L) ≫ (U.mapHomologicalComplex (.up ℤ)).map
        (((Functor.OplaxMonoidal.mapHomologicalComplexδNatTrans (.up ℤ) E).app K).app L) := by
  intro a
  apply HomologicalComplex.Hom.ext
  funext n
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro p q h
  simp only [HomologicalComplex.comp_f]
  erw [CochainComplex.ιTensorObj_tensorHom_f_assoc,
    scalarRestrictionChainTensor_summand]
  simp only [Functor.mapHomologicalComplex_map_f]
  change (adj.unit.app (K.X p) ⊗ₘ adj.unit.app (L.X q)) ≫ _ ≫ _ =
    HomologicalComplex.ιTensorObj K L p q n h ≫ adj.unit.app _ ≫ U.map _
  have hn := adj.unit.naturality (HomologicalComplex.ιTensorObj K L p q n h)
  dsimp only [Functor.id_map, Functor.comp_map] at hn
  erw [reassoc_of% hn]
  erw [← adj.unit_app_tensor_comp_map_δ_assoc, ← U.map_comp, ← U.map_comp]
  congr 1
  apply congrArg U.map
  exact (HomologicalComplex.map_ιMapBifunctor_mapBifunctorComparisonX
    (Functor.OplaxMonoidal.δNatTrans E) (.up ℤ) K L p q n h).symm

variable [Abelian.HasFunctorialFlatResolution C] [Abelian.HasFunctorialFlatResolution D]
  [E.PreservesKFlatQuasiIso] [E.PreservesFlat] [E.IsLeftAdjoint]
  [PreservesFiniteLimits U] [PreservesFiniteColimits U]

omit [MonoidalCategory D] [SymmetricCategory D] [MonoidalClosed D]
  [MonoidalPreadditive D] [E.Monoidal] [U.LaxMonoidal]
  [PreservesColimitsOfSize.{0, 0} E] [PreservesColimitsOfSize.{0, 0} U]
  [adj.IsMonoidal] [Abelian.HasFunctorialFlatResolution D]
  [E.PreservesFlat] [E.IsLeftAdjoint] in
private theorem cochain_unit (P : CochainComplex C ℤ) :
    (adj.derivedAdjunction.ofNatIsoRight U.rightDerivedFunctorIsoMapDerivedCategory).unit.app
        (DerivedCategory.Q.obj P) ≫
      U.mapDerivedCategory.map (E.rightExact_cochainCounit P) ≫
        U.mapDerivedCategoryFactors.hom.app ((E.mapHomologicalComplex (.up ℤ)).obj P) =
      DerivedCategory.Q.map ((adj.mapHomologicalComplex (.up ℤ)).unit.app P) := by
  have h := scalarChangeCochainUnit E U adj P
  change _ ≫ U.mapDerivedCategory.map (E.rightExact_cochainCounit P) = _ at h
  rw [← Category.assoc, h, Category.assoc, Iso.inv_hom_id_app]
  exact Category.comp_id _

set_option maxHeartbeats 800000 in
-- The normalization compares total tensors and several localization factors.
private theorem derived_tensor_unit_model
    (r : RestrictionTensorData U inferInstance)
    (P Q : CochainComplex C ℤ)
    (hP : (HomologicalComplex.quasiIso C (.up ℤ)).kFlat P)
    (hQ : (HomologicalComplex.quasiIso C (.up ℤ)).kFlat Q)
    (_hEP : (HomologicalComplex.quasiIso D (.up ℤ)).kFlat
      ((E.mapHomologicalComplex (.up ℤ)).obj P))
    (hEQ : (HomologicalComplex.quasiIso D (.up ℤ)).kFlat
      ((E.mapHomologicalComplex (.up ℤ)).obj Q)) :
    let a := adj.derivedAdjunction.ofNatIsoRight U.rightDerivedFunctorIsoMapDerivedCategory
    (a.unit.app (DerivedCategory.Q.obj P) ⊗ₘ a.unit.app (DerivedCategory.Q.obj Q)) ≫
        r.map (E.leftDerivedFunctor.obj (DerivedCategory.Q.obj P))
          (E.leftDerivedFunctor.obj (DerivedCategory.Q.obj Q)) =
      a.unit.app (DerivedCategory.Q.obj P ⊗ DerivedCategory.Q.obj Q) ≫
        U.mapDerivedCategory.map
          ((E.rightExact_leftDerivedTensorComparison.app (DerivedCategory.Q.obj P)).app
            (DerivedCategory.Q.obj Q)) := by
  intro a
  let EP := (E.mapHomologicalComplex (.up ℤ)).obj P
  let EQ := (E.mapHomologicalComplex (.up ℤ)).obj Q
  let εP := E.rightExact_cochainCounit P
  let εQ := E.rightExact_cochainCounit Q
  have : IsIso εP := E.rightExact_cochainCounit_isIso P hP
  have : IsIso εQ := E.rightExact_cochainCounit_isIso Q hQ
  have : IsIso (Functor.LaxMonoidal.μ DerivedCategory.Q EP EQ) :=
    Functor.tensorator_Q_isIso EP EQ hEQ
  apply (cancel_mono (U.mapDerivedCategory.map
    ((εP ⊗ₘ εQ) ≫ Functor.LaxMonoidal.μ DerivedCategory.Q EP EQ) ≫
      U.mapDerivedCategoryFactors.hom.app (EP ⊗ EQ))).1
  simp only [Functor.map_comp, Category.assoc]
  rw [← (reassoc_of% (r.naturality εP εQ)), r.normalization]
  simp only [tensorHom_comp_tensorHom_assoc]
  rw [cochain_unit E U adj P, cochain_unit E U adj Q]
  erw [Functor.LaxMonoidal.μ_natural_assoc]
  rw [← DerivedCategory.Q.map_comp, scalarRestrictionChainTensor_unique]
  rw [ordinary_tensor_unit E U adj P Q, DerivedCategory.Q.map_comp]
  have hc := E.rightExact_comparison_cochain P Q
  have hn := a.unit.naturality (Functor.LaxMonoidal.μ DerivedCategory.Q P Q)
  dsimp only [Functor.id_map, Functor.comp_map] at hn
  have hf := U.mapDerivedCategoryFactors.hom.naturality
    (((Functor.OplaxMonoidal.mapHomologicalComplexδNatTrans (.up ℤ) E).app P).app Q)
  dsimp only [Functor.comp_map] at hf
  have hcR := congrArg U.mapDerivedCategory.map hc
  simp only [Functor.map_comp] at hcR
  erw [← reassoc_of% hcR, ← reassoc_of% hn]
  erw [hf, reassoc_of% (cochain_unit E U adj (P ⊗ Q))]
  rfl


set_option maxHeartbeats 800000 in
-- The normalization compares total tensors and several localization factors.
private theorem derived_tensor_unit
    (r : RestrictionTensorData U inferInstance) (K L : DerivedCategory C) :
    let a := adj.derivedAdjunction.ofNatIsoRight U.rightDerivedFunctorIsoMapDerivedCategory
    (a.unit.app K ⊗ₘ a.unit.app L) ≫
        r.map (E.leftDerivedFunctor.obj K) (E.leftDerivedFunctor.obj L) =
      a.unit.app (K ⊗ L) ≫ U.mapDerivedCategory.map
        ((E.rightExact_leftDerivedTensorComparison.app K).app L) := by
  intro a
  obtain ⟨P, hP, _, hEP, ⟨e⟩⟩ := E.good_representative K
  obtain ⟨Q, hQ, _, hEQ, ⟨d⟩⟩ := E.good_representative L
  have h := derived_tensor_unit_model E U adj r P Q hP hQ hEP hEQ
  have hn : (e.hom ⊗ₘ d.hom) ≫ (a.unit.app K ⊗ₘ a.unit.app L) =
      (a.unit.app (DerivedCategory.Q.obj P) ⊗ₘ
        a.unit.app (DerivedCategory.Q.obj Q)) ≫
      (U.mapDerivedCategory.map (E.leftDerivedFunctor.map e.hom) ⊗ₘ
        U.mapDerivedCategory.map (E.leftDerivedFunctor.map d.hom)) := by
    simp only [tensorHom_comp_tensorHom]
    congr 1
    · exact a.unit.naturality e.hom
    · exact a.unit.naturality d.hom
  apply (cancel_epi (e.hom ⊗ₘ d.hom)).1
  rw [← Category.assoc, hn, Category.assoc, r.naturality,
    ← Category.assoc, h, Category.assoc, ← U.mapDerivedCategory.map_comp,
    ← E.rightExact_comparison_naturality_tensorHom]
  have hu := a.unit.naturality (e.hom ⊗ₘ d.hom)
  dsimp only [Functor.id_map, Functor.comp_map] at hu
  rw [Functor.map_comp, ← Category.assoc]
  simpa only [Category.assoc] using congrArg (· ≫ U.mapDerivedCategory.map
    ((E.rightExact_leftDerivedTensorComparison.app K).app L)) hu.symm

-- Fix the map type before specializing the derived bifunctors to sheaf categories.
private def typed_tensorComparison (K L : DerivedCategory C) :
    E.leftDerivedFunctor.obj (K ⊗ L) ⟶
      E.leftDerivedFunctor.obj K ⊗ E.leftDerivedFunctor.obj L :=
  ((E.rightExact_leftDerivedTensorComparison.app K).app L)

omit [PreservesColimitsOfSize.{0, 0} E] in
private theorem typed_tensorComparison_isIso (K L : DerivedCategory C) :
    IsIso (typed_tensorComparison E K L) := by
  unfold typed_tensorComparison
  infer_instance

private theorem typed_tensor_unit (r : RestrictionTensorData U inferInstance)
    (K L : DerivedCategory C) :
    let a := adj.derivedAdjunction.ofNatIsoRight U.rightDerivedFunctorIsoMapDerivedCategory
    (a.unit.app K ⊗ₘ a.unit.app L) ≫
        r.map (E.leftDerivedFunctor.obj K) (E.leftDerivedFunctor.obj L) =
      a.unit.app (K ⊗ L) ≫ U.mapDerivedCategory.map (typed_tensorComparison E K L) :=
  derived_tensor_unit E U adj r K L

attribute [local irreducible] typed_tensorComparison

end Ordinary

end AlgebraicGeometry.Etale.FiniteScalarProjectionFoundations

namespace AlgebraicGeometry.ProEtale.FiniteOrAlgebraicallyClosed

attribute [local irreducible] scalar projection scalarTensor scalarPull compactComparison sigma
attribute [local irreducible] Functor.leftDerivedFunctorCounit
  Functor.rightExact_leftDerivedTensorComparison

/-- Compatibility of the derived unit with exact restriction, proved from the
upstream derived-adjunction factorization. -/
private theorem scalarChangeDerivedUnit (P : HomotopyCategory C (.up ℤ)) :
    (adj.derivedAdjunction.ofNatIsoRight U.rightDerivedFunctorIsoMapDerivedCategory).unit.app
        (DerivedCategory.Qh.obj P) ≫
      U.mapDerivedCategory.map (E.leftDerivedFunctorCounit.app P) =
    DerivedCategory.Qh.map ((adj.mapHomotopyCategory (.up ℤ)).unit.app P) ≫
      U.mapDerivedCategoryFactorsh.inv.app ((E.mapHomotopyCategory (.up ℤ)).obj P) := by
  have h := (adj.mapHomotopyCategory (.up ℤ)).derivedη_fac_app
    (HomotopyCategory.quasiIso C (.up ℤ))
    E.leftDerivedFunctorCounit U.rightDerivedFunctorUnit P
  have hf := NatTrans.congr_app U.rightDerivedFunctorIsoMapDerivedCategory_hom_fac
    ((E.mapHomotopyCategory (.up ℤ)).obj P)
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app] at hf
  simp only [Adjunction.derivedAdjunction, Adjunction.ofNatIsoRight_unit,
    NatTrans.comp_app, Functor.whiskerLeft_app, Adjunction.derived_unit]
  rw [Category.assoc,
    ← U.rightDerivedFunctorIsoMapDerivedCategory.hom.naturality,
    ← Category.assoc, h, Category.assoc]
  dsimp only [Functor.comp_obj]
  rw [hf]

private theorem scalarChangeCochainUnit (P : CochainComplex C ℤ) :
    (adj.derivedAdjunction.ofNatIsoRight U.rightDerivedFunctorIsoMapDerivedCategory).unit.app
        (DerivedCategory.Q.obj P) ≫
      U.mapDerivedCategory.map (E.rightExact_cochainCounit P) =
    DerivedCategory.Q.map ((adj.mapHomologicalComplex (.up ℤ)).unit.app P) ≫
      U.mapDerivedCategoryFactors.inv.app ((E.mapHomologicalComplex (.up ℤ)).obj P) := by
  let H := (E.mapHomologicalComplex (.up ℤ)).obj P
  have hf := U.mapDerivedCategoryFactorsh_hom_app H
  simp only [Functor.mapHomotopyCategoryFactors, Quotient.lift.isLift_inv] at hf
  have hi : U.mapDerivedCategoryFactorsh.inv.app
      ((HomotopyCategory.quotient D (.up ℤ)).obj H) ≫
        U.mapDerivedCategory.map ((DerivedCategory.quotientCompQhIso D).hom.app H) =
      (DerivedCategory.quotientCompQhIso C).hom.app
        ((U.mapHomologicalComplex (.up ℤ)).obj H) ≫
          U.mapDerivedCategoryFactors.inv.app H := by
    apply (cancel_epi (U.mapDerivedCategoryFactorsh.hom.app _)).mp
    simp only [Iso.hom_inv_id_app_assoc]
    rw [hf]
    simp
  have hu := scalarChangeDerivedUnit E U adj ((HomotopyCategory.quotient _ _).obj P)
  rw [Adjunction.mapHomotopyCategory_unit_app_quotient] at hu
  change _ = DerivedCategory.Qh.map
    ((HomotopyCategory.quotient C (.up ℤ)).map
      ((adj.mapHomologicalComplex (.up ℤ)).unit.app P)) ≫
      U.mapDerivedCategoryFactorsh.inv.app
        ((HomotopyCategory.quotient D (.up ℤ)).obj H) at hu
  have hnat := (adj.derivedAdjunction.ofNatIsoRight
    U.rightDerivedFunctorIsoMapDerivedCategory).unit.naturality
      ((DerivedCategory.quotientCompQhIso C).inv.app P)
  dsimp only [Functor.id_map, Functor.comp_map] at hnat
  dsimp only [Functor.rightExact_cochainCounit]
  rw [Functor.map_comp, Functor.map_comp, ← Category.assoc, ← hnat]
  dsimp only [Functor.comp_obj]
  rw [Category.assoc, reassoc_of% hu, hi,
    DerivedCategory.quotientCompQhIso_hom_naturality_assoc]
  simp
  rfl

private theorem ordinary_tensor_unit
    (K L : CochainComplex C ℤ) :
    let a := adj.mapHomologicalComplex (.up ℤ)
    (a.unit.app K ⊗ₘ a.unit.app L) ≫
        scalarRestrictionChainTensor U inferInstance
          ((E.mapHomologicalComplex (.up ℤ)).obj K)
          ((E.mapHomologicalComplex (.up ℤ)).obj L) =
      a.unit.app (K ⊗ L) ≫ (U.mapHomologicalComplex (.up ℤ)).map
        (((Functor.OplaxMonoidal.mapHomologicalComplexδNatTrans (.up ℤ) E).app K).app L) := by
  intro a
  apply HomologicalComplex.Hom.ext
  funext n
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro p q h
  simp only [HomologicalComplex.comp_f]
  erw [CochainComplex.ιTensorObj_tensorHom_f_assoc,
    scalarRestrictionChainTensor_summand]
  simp only [Functor.mapHomologicalComplex_map_f]
  change (adj.unit.app (K.X p) ⊗ₘ adj.unit.app (L.X q)) ≫ _ ≫ _ =
    HomologicalComplex.ιTensorObj K L p q n h ≫ adj.unit.app _ ≫ U.map _
  have hn := adj.unit.naturality (HomologicalComplex.ιTensorObj K L p q n h)
  dsimp only [Functor.id_map, Functor.comp_map] at hn
  erw [reassoc_of% hn]
  erw [← adj.unit_app_tensor_comp_map_δ_assoc, ← U.map_comp, ← U.map_comp]
  congr 1
  apply congrArg U.map
  exact (HomologicalComplex.map_ιMapBifunctor_mapBifunctorComparisonX
    (Functor.OplaxMonoidal.δNatTrans E) (.up ℤ) K L p q n h).symm

private theorem cochain_unit (P : CochainComplex C ℤ) :
    (adj.derivedAdjunction.ofNatIsoRight U.rightDerivedFunctorIsoMapDerivedCategory).unit.app
        (DerivedCategory.Q.obj P) ≫
      U.mapDerivedCategory.map (E.rightExact_cochainCounit P) ≫
        U.mapDerivedCategoryFactors.hom.app ((E.mapHomologicalComplex (.up ℤ)).obj P) =
      DerivedCategory.Q.map ((adj.mapHomologicalComplex (.up ℤ)).unit.app P) := by
  have h := scalarChangeCochainUnit E U adj P
  change _ ≫ U.mapDerivedCategory.map (E.rightExact_cochainCounit P) = _ at h
  rw [← Category.assoc, h, Category.assoc, Iso.inv_hom_id_app]
  exact Category.comp_id _

private theorem derived_tensor_unit_model
    (r : RestrictionTensorData U inferInstance)
    (P Q : CochainComplex C ℤ)
    (hP : (HomologicalComplex.quasiIso C (.up ℤ)).kFlat P)
    (hQ : (HomologicalComplex.quasiIso C (.up ℤ)).kFlat Q)
    (_hEP : (HomologicalComplex.quasiIso D (.up ℤ)).kFlat
      ((E.mapHomologicalComplex (.up ℤ)).obj P))
    (hEQ : (HomologicalComplex.quasiIso D (.up ℤ)).kFlat
      ((E.mapHomologicalComplex (.up ℤ)).obj Q)) :
    let a := adj.derivedAdjunction.ofNatIsoRight U.rightDerivedFunctorIsoMapDerivedCategory
    (a.unit.app (DerivedCategory.Q.obj P) ⊗ₘ a.unit.app (DerivedCategory.Q.obj Q)) ≫
        r.map (E.leftDerivedFunctor.obj (DerivedCategory.Q.obj P))
          (E.leftDerivedFunctor.obj (DerivedCategory.Q.obj Q)) =
      a.unit.app (DerivedCategory.Q.obj P ⊗ DerivedCategory.Q.obj Q) ≫
        U.mapDerivedCategory.map
          ((E.rightExact_leftDerivedTensorComparison.app (DerivedCategory.Q.obj P)).app
            (DerivedCategory.Q.obj Q)) := by
  intro a
  let EP := (E.mapHomologicalComplex (.up ℤ)).obj P
  let EQ := (E.mapHomologicalComplex (.up ℤ)).obj Q
  let εP := E.rightExact_cochainCounit P
  let εQ := E.rightExact_cochainCounit Q
  have : IsIso εP := E.rightExact_cochainCounit_isIso P hP
  have : IsIso εQ := E.rightExact_cochainCounit_isIso Q hQ
  have : IsIso (Functor.LaxMonoidal.μ DerivedCategory.Q EP EQ) :=
    Functor.tensorator_Q_isIso EP EQ hEQ
  apply (cancel_mono (U.mapDerivedCategory.map
    ((εP ⊗ₘ εQ) ≫ Functor.LaxMonoidal.μ DerivedCategory.Q EP EQ) ≫
      U.mapDerivedCategoryFactors.hom.app (EP ⊗ EQ))).1
  simp only [Functor.map_comp, Category.assoc]
  rw [← (reassoc_of% (r.naturality εP εQ)), r.normalization]
  simp only [tensorHom_comp_tensorHom_assoc]
  rw [cochain_unit E U adj P, cochain_unit E U adj Q]
  erw [Functor.LaxMonoidal.μ_natural_assoc]
  rw [← DerivedCategory.Q.map_comp, scalarRestrictionChainTensor_unique]
  rw [ordinary_tensor_unit E U adj P Q, DerivedCategory.Q.map_comp]
  have hc := E.rightExact_comparison_cochain P Q
  have hn := a.unit.naturality (Functor.LaxMonoidal.μ DerivedCategory.Q P Q)
  dsimp only [Functor.id_map, Functor.comp_map] at hn
  have hf := U.mapDerivedCategoryFactors.hom.naturality
    (((Functor.OplaxMonoidal.mapHomologicalComplexδNatTrans (.up ℤ) E).app P).app Q)
  dsimp only [Functor.comp_map] at hf
  have hcR := congrArg U.mapDerivedCategory.map hc
  simp only [Functor.map_comp] at hcR
  erw [← reassoc_of% hcR, ← reassoc_of% hn]
  erw [hf, reassoc_of% (cochain_unit E U adj (P ⊗ Q))]
  rfl

private theorem derived_tensor_unit
    (r : RestrictionTensorData U inferInstance) (K L : DerivedCategory C) :
    let a := adj.derivedAdjunction.ofNatIsoRight U.rightDerivedFunctorIsoMapDerivedCategory
    (a.unit.app K ⊗ₘ a.unit.app L) ≫
        r.map (E.leftDerivedFunctor.obj K) (E.leftDerivedFunctor.obj L) =
      a.unit.app (K ⊗ L) ≫ U.mapDerivedCategory.map
        ((E.rightExact_leftDerivedTensorComparison.app K).app L) := by
  intro a
  obtain ⟨P, hP, _, hEP, ⟨e⟩⟩ := E.good_representative K
  obtain ⟨Q, hQ, _, hEQ, ⟨d⟩⟩ := E.good_representative L
  have h := derived_tensor_unit_model E U adj r P Q hP hQ hEP hEQ
  have hn : (e.hom ⊗ₘ d.hom) ≫ (a.unit.app K ⊗ₘ a.unit.app L) =
      (a.unit.app (DerivedCategory.Q.obj P) ⊗ₘ
        a.unit.app (DerivedCategory.Q.obj Q)) ≫
      (U.mapDerivedCategory.map (E.leftDerivedFunctor.map e.hom) ⊗ₘ
        U.mapDerivedCategory.map (E.leftDerivedFunctor.map d.hom)) := by
    simp only [tensorHom_comp_tensorHom]
    congr 1
    · exact a.unit.naturality e.hom
    · exact a.unit.naturality d.hom
  apply (cancel_epi (e.hom ⊗ₘ d.hom)).1
  rw [← Category.assoc, hn, Category.assoc, r.naturality,
    ← Category.assoc, h, Category.assoc, ← U.mapDerivedCategory.map_comp,
    ← E.rightExact_comparison_naturality_tensorHom]
  have hu := a.unit.naturality (e.hom ⊗ₘ d.hom)
  dsimp only [Functor.id_map, Functor.comp_map] at hu
  rw [Functor.map_comp, ← Category.assoc]
  simpa only [Category.assoc] using congrArg (· ≫ U.mapDerivedCategory.map
    ((E.rightExact_leftDerivedTensorComparison.app K).app L)) hu.symm

-- Fix the map type before specializing the derived bifunctors to sheaf categories.

private def typed_tensorComparison (K L : DerivedCategory C) :
    E.leftDerivedFunctor.obj (K ⊗ L) ⟶
      E.leftDerivedFunctor.obj K ⊗ E.leftDerivedFunctor.obj L :=
  ((E.rightExact_leftDerivedTensorComparison.app K).app L)

private theorem typed_tensorComparison_isIso (K L : DerivedCategory C) :
    IsIso (typed_tensorComparison E K L) := by
  unfold typed_tensorComparison
  infer_instance

private theorem typed_tensor_unit (r : RestrictionTensorData U inferInstance)
    (K L : DerivedCategory C) :
    let a := adj.derivedAdjunction.ofNatIsoRight U.rightDerivedFunctorIsoMapDerivedCategory
    (a.unit.app K ⊗ₘ a.unit.app L) ≫
        r.map (E.leftDerivedFunctor.obj K) (E.leftDerivedFunctor.obj L) =
      a.unit.app (K ⊗ L) ≫ U.mapDerivedCategory.map (typed_tensorComparison E K L) :=
  derived_tensor_unit E U adj r K L

private theorem transpose_naturality
    {C₁ C₂ : Type*} [Category C₁] [Category C₂]
    {F : C₁ ⥤ C₂} {G : C₂ ⥤ C₁} (a : F ⊣ G)
    {P Q : C₁} {R S : C₂} (g : P ⟶ Q) (h : R ⟶ S)
    (v : P ⟶ G.obj R) (w : Q ⟶ G.obj S)
    (hw : g ≫ w = v ≫ G.map h) :
    F.map g ≫ (a.homEquiv Q S).symm w = (a.homEquiv P R).symm v ≫ h := by
  rw [← a.homEquiv_naturality_left_symm, ← a.homEquiv_naturality_right_symm, hw]

private theorem compactComparison_naturality
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (aX : scalar φ X ⊣ restrict φ X) (aY : scalar φ Y ⊣ restrict φ Y)
    {M N : D A X} (h : M ⟶ N) :
    (scalar φ Y).map ((support A c).map h) ≫ compactComparison φ c aX aY N =
      compactComparison φ c aX aY M ≫ (support B c).map ((scalar φ X).map h) := by
  unfold compactComparison
  apply transpose_naturality
  have hn := (compactSupportRestrictionIso (RingHom.ulift.{u + 1, u + 1} φ) c).hom.naturality
    ((scalar φ X).map h)
  simp only [Functor.comp_map] at hn
  have hu := aX.unit.naturality h
  simp only [Functor.id_map, Functor.comp_map] at hu
  rw [← Category.assoc, ← Functor.map_comp, hu]
  simp only [Functor.map_comp, Category.assoc]
  exact congrArg ((support A c).map (aX.unit.app M) ≫ ·) hn

private theorem scalarPull_naturality
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {X Y : Scheme.{u}} (f : X ⟶ Y)
    (aX : scalar φ X ⊣ restrict φ X) (aY : scalar φ Y ⊣ restrict φ Y)
    {K L : D A Y} (g : K ⟶ L) :
    (scalar φ X).map ((pull A f).map g) ≫ scalarPull φ f aX aY L =
      scalarPull φ f aX aY K ≫ (pull B f).map ((scalar φ Y).map g) := by
  unfold scalarPull
  apply transpose_naturality
  have hn := (fixedScalarRestrictionPullback (RingHom.ulift.{u + 1, u + 1} φ) f).hom.naturality
    ((scalar φ Y).map g)
  simp only [Functor.comp_map] at hn
  have hu := aY.unit.naturality g
  simp only [Functor.id_map, Functor.comp_map] at hu
  rw [← Category.assoc, ← Functor.map_comp, hu]
  simp only [Functor.map_comp, Category.assoc]
  rw [hn]

private theorem tensorTranspose_naturality
    {C₁ C₂ : Type*} [Category C₁] [Category C₂]
    [MonoidalCategory C₁] [MonoidalCategory C₂]
    {F : C₁ ⥤ C₂} {R : C₂ ⥤ C₁} (a : F ⊣ R)
    (r : ∀ P Q : C₂, R.obj P ⊗ R.obj Q ⟶ R.obj (P ⊗ Q))
    (hr : ∀ {P P' Q Q' : C₂} (g : P ⟶ P') (h : Q ⟶ Q'),
      (R.map g ⊗ₘ R.map h) ≫ r P' Q' = r P Q ≫ R.map (g ⊗ₘ h))
    {K K' L L' : C₁} (g : K ⟶ K') (h : L ⟶ L') :
    F.map (g ⊗ₘ h) ≫ (a.homEquiv _ _).symm
        ((a.unit.app K' ⊗ₘ a.unit.app L') ≫ r (F.obj K') (F.obj L')) =
      (a.homEquiv _ _).symm ((a.unit.app K ⊗ₘ a.unit.app L) ≫
        r (F.obj K) (F.obj L)) ≫ (F.map g ⊗ₘ F.map h) := by
  apply transpose_naturality
  have hg := a.unit.naturality g
  have hh := a.unit.naturality h
  simp only [Functor.id_map, Functor.comp_map] at hg hh
  rw [← Category.assoc, tensorHom_comp_tensorHom, hg, hh,
    ← tensorHom_comp_tensorHom, Category.assoc]
  simpa only [Category.assoc] using
    congrArg ((a.unit.app K ⊗ₘ a.unit.app L) ≫ ·) (hr (F.map g) (F.map h))

set_option maxHeartbeats 1600000 in
-- Match the concrete restriction tensor data without unfolding the scalar functor.
private theorem scalarTensor_naturality
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) (T : Scheme.{u}) (a : scalar φ T ⊣ restrict φ T)
    {K K' L L' : D A T} (g : K ⟶ K') (h : L ⟶ L') :
    (scalar φ T).map (g ⊗ₘ h) ≫ scalarTensor φ T a K' L' =
      scalarTensor φ T a K L ≫ ((scalar φ T).map g ⊗ₘ (scalar φ T).map h) := by
  unfold scalarTensor
  apply tensorTranspose_naturality a
  exact Etale.RestrictionTensorData.naturality _

private theorem sigma_naturality
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {X Y : Scheme.{u}} (f : X ⟶ Y)
    (aX : scalar φ X ⊣ restrict φ X) (aY : scalar φ Y ⊣ restrict φ Y)
    {K L : D A Y} {M N : D A X} (g : K ⟶ L) (h : M ⟶ N) :
    sigma φ f aX aY K M ≫
        ((pull B f).map ((scalar φ Y).map g) ⊗ₘ (scalar φ X).map h) =
      (scalar φ X).map ((pull A f).map g ⊗ₘ h) ≫ sigma φ f aX aY L N := by
  simp only [sigma, ← Category.assoc]
  rw [scalarTensor_naturality]
  simp only [Category.assoc, tensorHom_comp_tensorHom, Category.id_comp, Category.comp_id]
  rw [scalarPull_naturality]

@[reassoc]
private theorem braiding_naturality
    (A : Type u) [CommRing A] (T : Scheme.{u})
    {K K' L L' : D A T} (g : K ⟶ K') (h : L ⟶ L') :
    (g ⊗ₘ h) ≫ (braiding A T K' L').hom =
      (braiding A T K L).hom ≫ (h ⊗ₘ g) := by
  let := DerivedCategory.braidedCategory' (Sheaf (ProEt.topology T)
    (ModuleCat.{u + 1} (ULift.{u + 1} A)))
  exact BraidedCategory.braiding_naturality g h

private theorem projection_naturality
    (A : Type u) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    {K K' : D A Y} {M M' : D A X} (g : K ⟶ K') (h : M ⟶ M') :
    (g ⊗ₘ (support A c).map h) ≫ projection A c K' M' =
      projection A c K M ≫ (support A c).map ((pull A f).map g ⊗ₘ h) := by
  let t := projectionMapOfCompactification (ModuleCat.{u + 1} (ULift.{u + 1} A)) c
  have hn := ((t.app M').naturality g)
  have hm := congrArg (fun z ↦ z.app K) (t.naturality h)
  dsimp [derivedTensorRightDerivedLowerShriek,
    rightDerivedLowerShriekDerivedTensorLeftDerivedUpperStar, derivedTensor] at hn hm
  simp only [← id_tensorHom, ← tensorHom_id] at hn hm
  change (𝟙 ((support A c).obj M') ⊗ₘ g) ≫ (t.app M').app K' =
    (t.app M').app K ≫ (support A c).map (𝟙 M' ⊗ₘ (pull A f).map g) at hn
  change ((support A c).map h ⊗ₘ 𝟙 K) ≫ (t.app M').app K =
    (t.app M).app K ≫ (support A c).map (h ⊗ₘ 𝟙 ((pull A f).obj K)) at hm
  have ht : ((support A c).map h ⊗ₘ g) ≫ (t.app M').app K' =
      (t.app M).app K ≫ (support A c).map (h ⊗ₘ (pull A f).map g) := by
    calc
      _ = ((support A c).map h ⊗ₘ 𝟙 K) ≫
          ((𝟙 ((support A c).obj M') ⊗ₘ g) ≫ (t.app M').app K') := by
        simp only [← Category.assoc, tensorHom_comp_tensorHom,
          Category.comp_id, Category.id_comp]
      _ = _ := by
        rw [hn, ← Category.assoc, hm]
        simp only [Category.assoc, ← Functor.map_comp, tensorHom_comp_tensorHom,
          Category.comp_id, Category.id_comp]
  simp only [projection, Category.assoc]
  rw [braiding_naturality_assoc]
  erw [reassoc_of% ht]
  have hb := braiding_naturality A X h ((pull A f).map g)
  have hb' := congrArg (support A c).map hb
  simp only [Functor.map_comp] at hb'
  exact congrArg ((braiding A Y K ((support A c).obj M)).hom ≫
    (t.app M).app K ≫ ·) hb'

private meta def coherenceHeadAsApplication (e : Lean.Expr) : Lean.MetaM Lean.Expr := do
  let f := e.getAppFn.consumeMData
  if let .proj n i v := f then
    let env ← Lean.getEnv
    let some info := Lean.getStructureInfo? env n | throwError "unknown structure {n}"
    let some p := Lean.getProjFnForField? env n (info.fieldNames[i]!) |
      throwError "unknown projection {n} {i}"
    let t ← Lean.Meta.whnfD (← Lean.Meta.inferType v)
    let .const _ us := t.getAppFn | throwError "projection has non-structure argument"
    let f := Lean.mkAppN (.const p us) (t.getAppArgs.push v)
    return Lean.mkAppN f e.getAppArgs
  return e

private meta def coherenceHeadAsApplication (e : Lean.Expr) : Lean.MetaM Lean.Expr := do
  let f := e.getAppFn.consumeMData
  if let .proj n i v := f then
    let env ← Lean.getEnv
    let some info := Lean.getStructureInfo? env n | throwError "unknown structure {n}"
    let some p := Lean.getProjFnForField? env n (info.fieldNames[i]!) |
      throwError "unknown projection {n} {i}"
    let t ← Lean.Meta.whnfD (← Lean.Meta.inferType v)
    let .const _ us := t.getAppFn | throwError "projection has non-structure argument"
    let f := Lean.mkAppN (.const p us) (t.getAppArgs.push v)
    return Lean.mkAppN f e.getAppArgs
  return e

/- Factor coefficient-instance equalities at argument boundaries and cache them.
Every generated equality is checked by Lean's kernel. The cache shares equality
proofs at argument boundaries, avoiding repeated reduction of large functor data. -/
private meta def coherenceInstanceCongr (cache : IO.Ref (Std.HashMap Lean.Expr Lean.Expr))
    (fuel : Nat) (g : Lean.MVarId) : Lean.MetaM Unit := do
  match fuel with
  | 0 => throwError "congruence recursion limit"
  | fuel + 1 =>
    let (_, g) ← g.intros
    g.withContext do
      let t := (← Lean.instantiateMVars (← g.getType)).consumeMData
      let entries ← cache.get
      if let some pf := entries[t]? then
        g.assign pf
        return
      for d in ← Lean.getLCtx do
        if (← Lean.instantiateMVars d.type).consumeMData == t then
          g.assign d.toExpr
          return
      let (a, b) ← if let some (_, a, b) := t.eq? then pure (a, b)
        else if let some (_, a, _, b) := t.heq? then pure (a, b)
        else throwError "unexpected congruence goal {t}"
      let a := a.consumeMData
      let b := b.consumeMData
      for d in ← Lean.getLCtx do
        let dt := (← Lean.instantiateMVars d.type).consumeMData
        if let some (_, x, _, y) := dt.heq? then
          if t.isHEq && x.consumeMData == a && y.consumeMData == b then
            g.assign d.toExpr
            return
      if a == b then
        if t.isHEq then g.hrefl else g.refl
      else
        let a ← coherenceHeadAsApplication a
        let b ← coherenceHeadAsApplication b
        let common := a.getAppFn == b.getAppFn &&
          a.getAppNumArgs == b.getAppNumArgs && a.getAppNumArgs > 0
        let a ← if common then pure a else
          coherenceHeadAsApplication (← Lean.Meta.whnfD a)
        let b ← if common then pure b else
          coherenceHeadAsApplication (← Lean.Meta.whnfD b)
        if a == b then
          if t.isHEq then g.hrefl else g.refl
        else if ← g.proofIrrelHeq then pure ()
        else if t.isEq then
          let gs ← g.apply (← Lean.Meta.mkConstWithFreshMVarLevels ``eq_of_heq)
            { synthAssignedInstances := false }
          for g in gs do coherenceInstanceCongr cache fuel g
        else if a.isLambda && b.isLambda then
          let gs ← g.apply (← Lean.Meta.mkConstWithFreshMVarLevels ``Function.hfunext)
            { synthAssignedInstances := false }
          for g in gs do coherenceInstanceCongr cache fuel g
        else if a.getAppFn == b.getAppFn &&
            a.getAppNumArgs == b.getAppNumArgs && a.getAppNumArgs > 0 then
          let f := a.getAppFn
          let info ← Lean.Meta.getFunInfoNArgs f a.getAppNumArgs
          let fixed := a.getAppArgs.zipWith (· == ·) b.getAppArgs
          let c ← Lean.Meta.mkRichHCongr (← Lean.Meta.inferType f) info
            (fixedFun := true) (fixedParams := fixed) (forceHEq := t.isHEq)
          let mut pf := c.proof.beta #[f]
          for i in [:a.getAppNumArgs] do
            let k := c.argKinds[i + 1]!
            pf := Lean.mkApp pf a.getAppArgs[i]!
            unless k == .fixed do
              pf := Lean.mkApp pf b.getAppArgs[i]!
              if k == .eq || k == .heq then
                let ty ← Lean.Meta.whnfD (← Lean.Meta.inferType pf)
                unless ty.isForall do throwError "missing congruence equality binder"
                let h ← Lean.Meta.mkFreshExprMVar ty.bindingDomain!
                pf := Lean.mkApp pf h
                coherenceInstanceCongr cache fuel h.mvarId!
              else unless k == .subsingletonInst do
                throwError "unsupported congruence argument kind"
          g.assign pf
        else
          throwError "unsupported congruence at fuel {fuel}:\n{a}\nversus\n{b}"
      let pf ← Lean.instantiateMVars (Lean.mkMVar g)
      cache.modify (·.insert t pf)

private theorem rawProjection_isIso_of_property
    {C : Type*} [Category.{u + 1} C] [Abelian C]
    [IsGrothendieckAbelian.{u + 1} C] [MonoidalCategory C] [MonoidalPreadditive C]
    [SymmetricCategory C] [MonoidalClosed C] [Abelian.HasFunctorialFlatResolution C]
    [ProEtale.UpperStarPreservesFlat C]
    {X Y : Scheme.{u}} {f : X ⟶ Y} {c : Compactification f}
    {M : DerivedCategory (Sheaf (ProEt.topology X) C)}
    {K : DerivedCategory (Sheaf (ProEt.topology Y) C)}
    (h : HasProjectionFormulaOfCompactification C c M K) :
    IsIso (((projectionMapOfCompactification C c).app M).app K) := h

private theorem projection_isIso
    (A : Type u) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
    [CompactSpace Y] [QuasiSeparatedSpace Y]
    {f : X ⟶ Y} (c : Compactification f)
    (K : D A Y) (M : D A X) (hK : ctf A Y K) (hM : ctf A X M) :
    IsIso (projection A c K M) := by
  unfold projection
  have hKo := (FiniteDiscreteOrdinary.ordinaryBC_iff A Y K).mp hK.1
  have hMo := (FiniteDiscreteOrdinary.ordinaryBC_iff A X M).mp hM.1
  apply IsIso.comp_isIso'
  · exact (braiding A Y K ((support A c).obj M)).isIso_hom
  · apply IsIso.comp_isIso'
    · have hp := hasProjectionFormulaOfCompactification_of_boundedConstructible
        (ULift.{u + 1} A) c hMo ⟨hKo, hK.2⟩
      have hraw := rawProjection_isIso_of_property hp
      run_tac Lean.Elab.Tactic.withMainContext do
        let some r := (← Lean.getLCtx).findFromUserName? `hraw |
          throwError "missing raw projection isomorphism"
        let g ← Lean.Elab.Tactic.getMainGoal
        let src ← Lean.instantiateMVars (← Lean.Meta.inferType r.toExpr)
        let tgt ← Lean.instantiateMVars (← g.getType)
        let v ← Lean.Meta.mkFreshExprMVar (← Lean.Meta.mkEq src tgt)
        g.assign (← Lean.Meta.mkAppM ``Eq.mp #[v, r.toExpr])
        let cache ← IO.mkRef ({} : Std.HashMap Lean.Expr Lean.Expr)
        Lean.Meta.withTransparency .default do
          coherenceInstanceCongr cache 100 v.mvarId!
        Lean.Elab.Tactic.replaceMainGoal []
    · exact ((support A c).mapIso (braiding A X M ((pull A f).obj K))).isIso_hom

private theorem tensor_mate_isIso
    {C D : Type*} [Category C] [Category D] [MonoidalCategory C] [MonoidalCategory D]
    {F F₀ : C ⥤ D} {R : D ⥤ C} (a : F ⊣ R) (a₀ : F₀ ⊣ R)
    (r : ∀ P Q : D, R.obj P ⊗ R.obj Q ⟶ R.obj (P ⊗ Q))
    (hn : ∀ {P P' Q Q' : D} (g : P ⟶ P') (h : Q ⟶ Q'),
      (R.map g ⊗ₘ R.map h) ≫ r P' Q' = r P Q ≫ R.map (g ⊗ₘ h))
    (K L : C) (δ : F₀.obj (K ⊗ L) ⟶ F₀.obj K ⊗ F₀.obj L) [IsIso δ]
    (hu : (a₀.unit.app K ⊗ₘ a₀.unit.app L) ≫ r (F₀.obj K) (F₀.obj L) =
      a₀.unit.app (K ⊗ L) ≫ R.map δ) :
    IsIso ((a.homEquiv _ _).symm
      ((a.unit.app K ⊗ₘ a.unit.app L) ≫ r (F.obj K) (F.obj L))) := by
  let e := a.leftAdjointUniq a₀
  have he (V : C) : a₀.unit.app V ≫ R.map (e.inv.app V) = a.unit.app V := by
    rw [← a.unit_leftAdjointUniq_hom_app a₀ V]
    rw [Category.assoc, ← Functor.map_comp]
    change a.unit.app V ≫ R.map (e.hom.app V ≫ e.inv.app V) = _
    rw [e.hom_inv_id_app, CategoryTheory.Functor.map_id]
    exact CategoryTheory.Category.comp_id _
  have hδ : (a.homEquiv _ _).symm
      ((a.unit.app K ⊗ₘ a.unit.app L) ≫ r (F.obj K) (F.obj L)) =
      e.hom.app (K ⊗ L) ≫ δ ≫ (e.inv.app K ⊗ₘ e.inv.app L) := by
    apply (a.homEquiv _ _).injective
    rw [Equiv.apply_symm_apply, Adjunction.homEquiv_unit]
    rw [← he K, ← he L, ← tensorHom_comp_tensorHom_assoc, hn, ← Category.assoc, hu]
    simp only [Functor.map_comp, Category.assoc]
    simpa only [CategoryTheory.Functor.id_obj, Category.assoc, e] using
      congrArg (fun z ↦ z ≫ R.map δ ≫ R.map (e.inv.app K ⊗ₘ e.inv.app L))
        (a.unit_leftAdjointUniq_hom_app a₀ (K ⊗ L)).symm
  rw [hδ]
  infer_instance

private theorem unit_universal
    {C D : Type*} [Category C] [Category D]
    {F : C ⥤ D} {R : D ⥤ C} (a : F ⊣ R) (K : C) :
    ∀ N : D, Function.Bijective (fun g : F.obj K ⟶ N ↦ a.unit.app K ≫ R.map g) := by
  intro N
  have he : (fun g : F.obj K ⟶ N ↦ a.unit.app K ≫ R.map g) = a.homEquiv K N := by
    funext g
    exact (a.homEquiv_unit K N g).symm
  rw [he]
  exact (a.homEquiv K N).bijective

private theorem scalarPull_isIso
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {X Y : Scheme.{u}} (f : X ⟶ Y)
    (aX : scalar φ X ⊣ restrict φ X) (aY : scalar φ Y ⊣ restrict φ Y)
    (K : D A Y) : IsIso (scalarPull φ f aX aY K) := by
  let model : CoefficientTensorModel (RingHom.ulift.{u + 1, u + 1} φ) Y K :=
    ⟨(scalar φ Y).obj K, aY.unit.app K, unit_universal aY K⟩
  have hv := model.pullback_universal f
  unfold scalarPull
  apply Sheaf.IsDerivedBaseChange.isIso (unit_universal aX ((pull A f).obj K)) hv
  exact (aX.homEquiv _ _).apply_symm_apply _

private theorem orderedProjectionSquare
    {AX AY BX BY : Type*} [Category AX] [Category AY] [Category BX] [Category BY]
    [MonoidalCategory AX] [MonoidalCategory AY]
    [MonoidalCategory BX] [MonoidalCategory BY]
    [BraidedCategory AX] [BraidedCategory AY]
    [BraidedCategory BX] [BraidedCategory BY]
    (SA : AX ⥤ BX) (SB : AY ⥤ BY) (PA : AX ⥤ AY) (PB : BX ⥤ BY)
    (FA : AY ⥤ AX) (FB : BY ⥤ BX)
    (μX : ∀ U V, SA.obj (U ⊗ V) ⟶ SA.obj U ⊗ SA.obj V)
    (μY : ∀ U V, SB.obj (U ⊗ V) ⟶ SB.obj U ⊗ SB.obj V)
    (b : ∀ M, SB.obj (PA.obj M) ⟶ PB.obj (SA.obj M))
    (t : ∀ K, SA.obj (FA.obj K) ⟶ FB.obj (SB.obj K))
    (pfA : ∀ M K, PA.obj M ⊗ K ⟶ PA.obj (M ⊗ FA.obj K))
    (pfB : ∀ M K, PB.obj M ⊗ K ⟶ PB.obj (M ⊗ FB.obj K))
    (hb : ∀ {M N} (h : M ⟶ N), SB.map (PA.map h) ≫ b N = b M ≫ PB.map (SA.map h))
    (hsX : ∀ U V, SA.map (β_ U V).hom ≫ μX V U =
      μX U V ≫ (β_ (SA.obj U) (SA.obj V)).hom)
    (hsY : ∀ U V, SB.map (β_ U V).hom ≫ μY V U =
      μY U V ≫ (β_ (SB.obj U) (SB.obj V)).hom)
    (K : AY) (M : AX)
    (hpf : SB.map (pfA M K) ≫ b (M ⊗ FA.obj K) ≫
      PB.map (μX M (FA.obj K)) ≫ PB.map (𝟙 (SA.obj M) ⊗ₘ t K) =
      μY (PA.obj M) K ≫ (b M ⊗ₘ 𝟙 (SB.obj K)) ≫ pfB (SA.obj M) (SB.obj K)) :
    SB.map ((β_ K (PA.obj M)).hom ≫ pfA M K ≫
        PA.map (β_ M (FA.obj K)).hom) ≫ b (FA.obj K ⊗ M) ≫
        PB.map (μX (FA.obj K) M ≫ (t K ⊗ₘ 𝟙 (SA.obj M))) =
      μY K (PA.obj M) ≫ (𝟙 (SB.obj K) ⊗ₘ b M) ≫
        ((β_ (SB.obj K) (PB.obj (SA.obj M))).hom ≫ pfB (SA.obj M) (SB.obj K) ≫
          PB.map (β_ (SA.obj M) (FB.obj (SB.obj K))).hom) := by
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% (hb (β_ M (FA.obj K)).hom)]
  rw [← PB.map_comp_assoc, hsX]
  simp only [PB.map_comp, Category.assoc]
  have hn := congrArg PB.map (BraidedCategory.braiding_naturality
    (𝟙 (SA.obj M)) (t K))
  simp only [Functor.map_comp] at hn
  rw [← hn]
  rw [reassoc_of% hpf]
  rw [reassoc_of% (hsY K (PA.obj M))]
  rw [← BraidedCategory.braiding_naturality_assoc]

/-- The finite-or-algebraically-closed compact-support scalar projection statement.

Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/sec-smooth-purity/
sec-sp-grp-ladic-summary/sec-change-of-finite-coefficients/sk-lem-sp-reduction/
sk-lem-sp-reduction-compatibilities.proof.md, Proof (3), Tensor map
(blueprint: lem-sp-finite-or-algebraically-closed-compact-support-scalar-projection-coherence).

Proof: The ordinary bounded-constructible comparison and the source-library finite-ring
compactification projection theorem give the A-projection isomorphism. Adjunction units and
restriction tensor naturality give all scalar naturalities. Uniqueness of left adjoints
identifies the scalar tensor transpose with the invertible K-flat tensor comparison. The
existing universal scalar-extension arrow remains universal under pullback, so scalarPull
is invertible, and hence so is sigma.
The two ordinary normalization sublemmas supply the unit/symmetry constraints and the
coefficient-first proper/open square with b invertible at both required inputs. The explicit
categorical braiding calculation below converts that square to the displayed ordered
square. Cancellation of its invertible scalar factors then proves B-projection invertibility.
All maps are the recorded ordinary maps; no flatness hypothesis or finite-field restriction
is introduced.
-/
theorem finiteOrAlgebraicallyClosedCompactSupportScalarProjectionCoherence
    (k : Type u) [Field k] (p : ℕ) (hp : p.Prime) (hpk : ringChar k = p)
    (hscope : Finite k ∨ IsAlgClosed k) (ell : ℕ) (hell : ell.Prime) (hEll : ell ≠ p)
    (A B : Type u) [CommRing A] [CommRing B] [Finite A] [Finite B]
    (hA : ∃ n : ℕ, 1 ≤ n ∧ ∀ a : A, (ell ^ n) • a = 0)
    (hB : ∃ n : ℕ, 1 ≤ n ∧ ∀ b : B, (ell ^ n) • b = 0)
    (φ : A →+* B) {X Y : Scheme.{u}} (f : X ⟶ Y)
    [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))] [LocallyOfFiniteType (Y ↘ Spec (.of k))]
    [QuasiCompact (Y ↘ Spec (.of k))]
    (c : Compactification f) [c.Z.Over (Spec (.of k))]
    [IsSeparated (c.Z ↘ Spec (.of k))]
    [LocallyOfFiniteType (c.Z ↘ Spec (.of k))]
    [QuasiCompact (c.Z ↘ Spec (.of k))]
    [c.i.IsOver (Spec (.of k))] [c.g.IsOver (Spec (.of k))]
    (K : D A Y) (L : D A Y) (M : D A X) (hK : ctf A Y K)
    (hL : ctf A Y L) (hM : ctf A X M) (aX : scalar φ X ⊣ restrict φ X)
    (aY : scalar φ Y ⊣ restrict φ Y) (U V : D A Y) :
    IsIso (projection A c K M) ∧
      IsIso (projection B c ((scalar φ Y).obj K) ((scalar φ X).obj M)) ∧
      IsIso (compactComparison φ c aX aY M) ∧
      IsIso (compactComparison φ c aX aY ((pull A f).obj K ⊗ M)) ∧
      IsIso (scalarTensor φ Y aY K L) ∧
      IsIso (sigma φ f aX aY K M) ∧
      IsIso (scalarPull φ f aX aY K) ∧
      IsIso (scalarUnit φ Y aY) ∧
      (scalar φ Y).map (projection A c K M) ≫
          compactComparison φ c aX aY ((pull A f).obj K ⊗ M) ≫
          (support B c).map (sigma φ f aX aY K M) =
        scalarTensor φ Y aY K ((support A c).obj M) ≫
          (𝟙 ((scalar φ Y).obj K) ⊗ₘ compactComparison φ c aX aY M) ≫
          projection B c ((scalar φ Y).obj K) ((scalar φ X).obj M) ∧
      (∀ {K₁ K₂ : D A Y} {M₁ M₂ : D A X} (g : K₁ ⟶ K₂) (h : M₁ ⟶ M₂),
        (g ⊗ₘ (support A c).map h) ≫ projection A c K₂ M₂ =
          projection A c K₁ M₁ ≫ (support A c).map ((pull A f).map g ⊗ₘ h)) ∧
      (∀ {K₁ K₂ : D B Y} {M₁ M₂ : D B X} (g : K₁ ⟶ K₂) (h : M₁ ⟶ M₂),
        (g ⊗ₘ (support B c).map h) ≫ projection B c K₂ M₂ =
          projection B c K₁ M₁ ≫ (support B c).map ((pull B f).map g ⊗ₘ h)) ∧
      (∀ {U₁ U₂ V₁ V₂ : D A Y} (g : U₁ ⟶ U₂) (h : V₁ ⟶ V₂),
        (scalar φ Y).map (g ⊗ₘ h) ≫ scalarTensor φ Y aY U₂ V₂ =
          scalarTensor φ Y aY U₁ V₁ ≫
            ((scalar φ Y).map g ⊗ₘ (scalar φ Y).map h)) ∧
      (∀ {K₁ K₂ : D A Y} (g : K₁ ⟶ K₂),
        (scalar φ X).map ((pull A f).map g) ≫ scalarPull φ f aX aY K₂ =
          scalarPull φ f aX aY K₁ ≫ (pull B f).map ((scalar φ Y).map g)) ∧
      (∀ {M₁ M₂ : D A X} (h : M₁ ⟶ M₂),
        (scalar φ Y).map ((support A c).map h) ≫ compactComparison φ c aX aY M₂ =
          compactComparison φ c aX aY M₁ ≫ (support B c).map ((scalar φ X).map h)) ∧
      (∀ {K₁ K₂ : D A Y} {M₁ M₂ : D A X} (g : K₁ ⟶ K₂) (h : M₁ ⟶ M₂),
        sigma φ f aX aY K₁ M₁ ≫
            ((pull B f).map ((scalar φ Y).map g) ⊗ₘ (scalar φ X).map h) =
          (scalar φ X).map ((pull A f).map g ⊗ₘ h) ≫ sigma φ f aX aY K₂ M₂) ∧
      ((scalar φ Y).map (λ_ V).hom =
        scalarTensor φ Y aY (𝟙_ _) V ≫
          (scalarUnit φ Y aY ⊗ₘ 𝟙 ((scalar φ Y).obj V)) ≫
          (λ_ ((scalar φ Y).obj V)).hom) ∧
      ((scalar φ Y).map (braiding A Y U V).hom ≫ scalarTensor φ Y aY V U =
        scalarTensor φ Y aY U V ≫
          (braiding B Y ((scalar φ Y).obj U) ((scalar φ Y).obj V)).hom) := by
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of k))
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace (Y ↘ Spec (.of k))
  have : QuasiSeparatedSpace X :=
    quasiSeparatedSpace_of_quasiSeparated (X ↘ Spec (.of k))
  have : QuasiSeparatedSpace Y :=
    quasiSeparatedSpace_of_quasiSeparated (Y ↘ Spec (.of k))
  obtain ⟨hbM, hbT, hpf⟩ :=
    ordinaryFiniteCompactSupport_scalar_projection_normalization
      k p hp hpk hscope ell hell hEll A B hA hB φ f c K M hK hM aX aY
  let := hbM
  let := hbT
  let := scalarTensor_isIso φ Y aY K L
  let := scalarTensor_isIso φ Y aY K ((support A c).obj M)
  let := scalarTensor_isIso φ X aX ((pull A f).obj K) M
  let := scalarPull_isIso φ f aX aY K
  have : IsIso (sigma φ f aX aY K M) := by
    unfold sigma
    infer_instance
  have : IsIso (projection A c K M) := projection_isIso A c K M hK hM
  obtain ⟨hu, hlu, hsym⟩ := ordinaryFiniteScalar_unit_symmetry φ Y aY U V
  have hsquare :
      (scalar φ Y).map (projection A c K M) ≫
          compactComparison φ c aX aY ((pull A f).obj K ⊗ M) ≫
          (support B c).map (sigma φ f aX aY K M) =
        scalarTensor φ Y aY K ((support A c).obj M) ≫
          (𝟙 ((scalar φ Y).obj K) ⊗ₘ compactComparison φ c aX aY M) ≫
          projection B c ((scalar φ Y).obj K) ((scalar φ X).obj M) := by
    let := DerivedCategory.braidedCategory' (Sheaf (ProEt.topology X)
      (ModuleCat.{u + 1} (ULift.{u + 1} A)))
    let := DerivedCategory.braidedCategory' (Sheaf (ProEt.topology Y)
      (ModuleCat.{u + 1} (ULift.{u + 1} A)))
    let := DerivedCategory.braidedCategory' (Sheaf (ProEt.topology X)
      (ModuleCat.{u + 1} (ULift.{u + 1} B)))
    let := DerivedCategory.braidedCategory' (Sheaf (ProEt.topology Y)
      (ModuleCat.{u + 1} (ULift.{u + 1} B)))
    have h := orderedProjectionSquare (scalar φ X) (scalar φ Y)
      (support A c) (support B c) (pull A f) (pull B f)
      (scalarTensor φ X aX) (scalarTensor φ Y aY)
      (compactComparison φ c aX aY) (scalarPull φ f aX aY)
      (fun M K ↦ ((projectionMapOfCompactification
        (ModuleCat.{u + 1} (ULift.{u + 1} A)) c).app M).app K)
      (fun M K ↦ ((projectionMapOfCompactification
        (ModuleCat.{u + 1} (ULift.{u + 1} B)) c).app M).app K)
      (fun h ↦ compactComparison_naturality φ c aX aY h)
      (fun U V ↦ (ordinaryFiniteScalar_unit_symmetry φ X aX U V).2.2)
      (fun U V ↦ (ordinaryFiniteScalar_unit_symmetry φ Y aY U V).2.2)
      K M hpf
    simpa only [projection, sigma, braiding] using h
  have : IsIso (projection B c ((scalar φ Y).obj K) ((scalar φ X).obj M)) := by
    have : IsIso (scalarTensor φ Y aY K ((support A c).obj M) ≫
        (𝟙 ((scalar φ Y).obj K) ⊗ₘ compactComparison φ c aX aY M) ≫
        projection B c ((scalar φ Y).obj K) ((scalar φ X).obj M)) := by
      rw [← hsquare]
      infer_instance
    have := IsIso.of_isIso_comp_left (scalarTensor φ Y aY K ((support A c).obj M))
      ((𝟙 ((scalar φ Y).obj K) ⊗ₘ compactComparison φ c aX aY M) ≫
        projection B c ((scalar φ Y).obj K) ((scalar φ X).obj M))
    exact IsIso.of_isIso_comp_left (𝟙 ((scalar φ Y).obj K) ⊗ₘ compactComparison φ c aX aY M) _
  exact ⟨inferInstance, inferInstance, hbM, hbT, inferInstance, inferInstance,
    inferInstance, hu, hsquare,
    fun g h ↦ projection_naturality A c g h,
    fun g h ↦ projection_naturality B c g h,
    fun g h ↦ scalarTensor_naturality φ Y aY g h,
    fun g ↦ scalarPull_naturality φ f aX aY g,
    fun h ↦ compactComparison_naturality φ c aX aY h,
    fun g h ↦ sigma_naturality φ f aX aY g h, hlu, hsym⟩

end AlgebraicGeometry.ProEtale.FiniteOrAlgebraicallyClosed
