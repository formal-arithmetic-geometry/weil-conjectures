/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralHom.Reduction.IntegralHomReductionModels
import all WeilConjectures.Algebra.Homology.RingedDerivedTensorHomAdjunction
import all WeilConjectures.Algebra.Homology.Ringed.RingedDerivedTensorNativeSupplement
import all WeilConjectures.Algebra.Homology.KInjectiveHomComplexOfUniverses
import all WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import all WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import all WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import all Mathlib.Algebra.Category.Grp.FilteredColimits
import all Mathlib.Algebra.Homology.BifunctorShift
import all Mathlib.Algebra.Homology.QuasiIso
import all Mathlib.CategoryTheory.Sites.Equivalence
import all Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import all Mathlib.CategoryTheory.Limits.EssentiallySmall
import all WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import all WeilConjectures.Algebra.Homology.HomComplex
import all Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import all WeilConjectures.Algebra.Homology.HomTensorDegreewiseIso
import all WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import all Mathlib.CategoryTheory.Monoidal.Closed.Basic
import all Mathlib.CategoryTheory.Limits.ExactFunctor
import all WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import all Mathlib.Algebra.Category.Grp.AB
import all WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import all Mathlib.RingTheory.Flat.CategoryTheory
import all WeilConjectures.SecSmoothPurity.CochainTensoratorExistence
import all WeilConjectures.CategoryTheory.AlgebraicInverseImage
import all Mathlib.Algebra.Category.ModuleCat.Sheaf
import all Mathlib.Algebra.Category.Ring.Limits
import all Mathlib.Algebra.Category.Grp.Limits
import all Mathlib.CategoryTheory.Sites.Whiskering
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import all WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
import all WeilConjectures.Mathlib.Algebra.Homology.Monoidal
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import all Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainInverseComparison
import all WeilConjectures.CategoryTheory.RingedSiteModules
import all Mathlib.CategoryTheory.Adjunction.Limits
import all WeilConjectures.CategoryTheory.AdjunctionRingOperations
import all Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import all Mathlib.CategoryTheory.Adjunction.Basic
import all WeilConjectures.CategoryTheory.GeometricModuleConstruction
import all WeilConjectures.CategoryTheory.RingedToposRingData
import all WeilConjectures.CategoryTheory.Ringed.RingedToposMorphismSupplement
import all Mathlib.CategoryTheory.Sites.CartesianMonoidal
import all Mathlib.CategoryTheory.Monoidal.CommGrp_
import all WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
import all WeilConjectures.CategoryTheory.GeometricModuleTransport
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import all WeilConjectures.Algebra.Homology.InternalHom
import all WeilConjectures.Algebra.Homology.HomComplexComponents
import all WeilConjectures.CategoryTheory.Monoidal.Instances.CochainComplex
import all WeilConjectures.Algebra.Homology.HomotopyCategory.InternalHom
import all WeilConjectures.SecSmoothPurity.ModuleTensorGenerators
import all WeilConjectures.SecSmoothPurity.CochainCoefficientArrowsSupplement
import all WeilConjectures.Algebra.Homology.ScalarHomCancellation.ScalarHomTensorCancellation
import all WeilConjectures.SmoothPurity.Integral.IntegralTensorTransitionCompatibility
import all WeilConjectures.CategoryTheory.Scalar.ScalarHomTensorCoherence
import all WeilConjectures.CategoryTheory.Site.SiteDerivedTensorRestriction
import WeilConjectures.SixFunctors.CoefficientClosedStructure.CoefficientRingedTensorHomModelSupplement

/-! # K-flat computation of the normalized reduction tensor mate

Source: Stacks 03CZ, 06YY and 07A4; integral Hom reduction, paragraphs 1--2.
The representative calculation follows `IntegralTensorRestrictionMateModel`,
retaining independent site and coefficient universes.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe d t u
open CategoryTheory AlgebraicGeometry
open scoped ChangeOfRings
attribute [-instance] GrothendieckTopology.hasSheafify_of_essentiallySmall

namespace WeilConjectures.IntegralHom.StrengthModel
private noncomputable instance (priority := 2000) fixedSmall (Y : Scheme.{t}) :
    EssentiallySmall.{max u (t + 1)} Y.ProEt :=
  integralReductionSiteEssentiallySmall.{t, u} Y

private noncomputable instance (priority := 2000) fixedSheafify (Y : Scheme.{t}) :
    HasSheafify (Scheme.ProEt.topology Y) AddCommGrpCat.{max u (t + 1)} :=
  integralCoefficientAbSheafify.{t, u} Y

private noncomputable instance (priority := 2000) fixedLocallyBijective (Y : Scheme.{t}) :
    (Scheme.ProEt.topology Y).WEqualsLocallyBijective AddCommGrpCat.{max u (t + 1)} :=
  integralCoefficientAbLocallyBijective.{t, u} Y

private noncomputable instance (priority := 2000) fixedDerived (Y : Scheme.{t})
    (R : Sheaf (Scheme.ProEt.topology Y) CommRingCat.{max u (t + 1)}) :
    HasDerivedCategory (Modules.{t, u} Y R) := HasDerivedCategory.standard _

end WeilConjectures.IntegralHom.StrengthModel

namespace WeilConjectures.IntegralHom
section Wrappers
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (X : Scheme.{t})

private abbrev strengthReductionRestricted (n : ℕ) :=
  scalarReductionExtension l E X n ⋙ scalarReductionRestriction l E X n

private abbrev strengthDerivedReductionRestricted (n : ℕ) :=
  scalarReductionDerivedExtension l E X n ⋙ scalarReductionDerivedRestriction l E X n

private def strengthReductionTensor (n : ℕ) (M : scalarReductionSource l E X)
    (U : X.ProEtᵒᵖ) (s : (integralCoefficientCommRingSheaf l E X n).obj.obj U)
    (x : M.val.obj U) : ((scalarReductionExtension l E X n).obj M).val.obj U :=
  (eqToHom ((scalarReductionExistence l E X n).choose_spec.choose M).symm).val.app U
    ((CategoryTheory.toSheafify (Scheme.ProEt.topology X)
      (SheafOfModules.changeOfRingsPresheaf
        (completedIntegralCommRingProjectionUnrestricted l E X n) M).presheaf).app U
        (s ⊗ₜ[(completedIntegralCommRingSheafUnrestricted l E X).obj.obj U,
          ((completedIntegralCommRingProjectionUnrestricted l E X n).hom.app U).hom] x))

private def strengthReductionRepresentativeComparison (n : ℕ)
    (P : CochainComplex (scalarReductionSource l E X) ℤ) :
    (strengthDerivedReductionRestricted l E X n).obj (DerivedCategory.Q.obj P) ⟶
      DerivedCategory.Q.obj
        (((strengthReductionRestricted l E X n).mapHomologicalComplex (.up ℤ)).obj P) :=
  (scalarReductionDerivedRestriction l E X n).map
      ((scalarReductionCounit l E X n).app
        ((HomotopyCategory.quotient _ (.up ℤ)).obj P)) ≫
    (scalarReductionRestriction l E X n).mapDerivedCategoryFactorsh.hom.app
      (((scalarReductionExtension l E X n).mapHomotopyCategory (.up ℤ)).obj
        ((HomotopyCategory.quotient _ (.up ℤ)).obj P))

private theorem strengthUnitComparison (n : ℕ)
    (P : CochainComplex (scalarReductionSource l E X) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients
      (J := Scheme.ProEt.topology X)
      (R := completedIntegralCommRingSheafUnrestricted l E X) P) :
    (derivedScalarExtensionRestrictionAdjunction l E X n).choose.unit.app
        (DerivedCategory.Q.obj P) ≫
      strengthReductionRepresentativeComparison l E X n P =
      DerivedCategory.Q.map
        (((scalarReductionExtension_adjunction l E X n).choose.mapHomologicalComplex
          (.up ℤ)).unit.app P) := by
  have h := (derivedScalarExtensionRestrictionAdjunction l E X n).choose_spec P hP
  have hu := Adjunction.mapHomotopyCategory_unit_app_quotient (.up ℤ)
    (scalarReductionExtension_adjunction l E X n).choose P
  have hq := congrArg (DerivedCategory.Qh (C := scalarReductionSource l E X)).map hu
  exact h.trans hq

private theorem strengthComparison_isIso (n : ℕ)
    (P : CochainComplex (scalarReductionSource l E X) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients
      (J := Scheme.ProEt.topology X)
      (R := completedIntegralCommRingSheafUnrestricted l E X) P) :
    IsIso (strengthReductionRepresentativeComparison l E X n P) := by
  have hε : IsIso ((scalarReductionCounit l E X n).app
      ((HomotopyCategory.quotient _ (.up ℤ)).obj P)) :=
    (scalarReductionDerivedExistence l E X n).choose_spec.choose_spec.2.2 P hP
  unfold strengthReductionRepresentativeComparison
  infer_instance
end Wrappers
end WeilConjectures.IntegralHom

/- The mate calculation below only uses naturality, adjunction identities,
   and cancellation of the comparison and resolution isomorphisms. -/
namespace StrengthGenericMate
variable {C D : Type*} [Category C] [Category D]
  (T : C × C ⥤ C) (S : D × D ⥤ D)
  (L : C ⥤ D) (U : D ⥤ C) (adj : L ⊣ U)
  (μ : T ⋙ L ≅ L.prod L ⋙ S)

private def mate (p q : C) :=
  adj.homEquiv _ _ (μ.hom.app (p, U.obj (L.obj q)) ≫
    S.map (Prod.mkHom (𝟙 (L.obj p)) (adj.counit.app (L.obj q))) ≫ μ.inv.app (p, q))

private theorem mate_precomp (p q s : C) (f : L.obj s ⟶ L.obj q) :
    T.map (Prod.mkHom (𝟙 p) (adj.homEquiv _ _ f)) ≫ mate T S L U adj μ p q =
      adj.homEquiv _ _ (μ.hom.app (p, s) ≫
        S.map (Prod.mkHom (𝟙 (L.obj p)) f) ≫ μ.inv.app (p, q)) := by
  rw [mate, ← adj.homEquiv_naturality_left]
  congr 1
  have h := μ.hom.naturality
    (Prod.mkHom (𝟙 p) (adj.homEquiv _ _ f))
  change L.map (T.map (Prod.mkHom (𝟙 p) (adj.homEquiv _ _ f))) ≫
    μ.hom.app (p, U.obj (L.obj q)) =
      μ.hom.app (p, s) ≫
        S.map (Prod.mkHom (L.map (𝟙 p)) (L.map (adj.homEquiv _ _ f))) at h
  rw [reassoc_of% h, L.map_id, ← S.map_comp_assoc]
  have hp : Prod.mkHom (𝟙 (L.obj p)) (L.map (adj.homEquiv _ _ f)) ≫
      Prod.mkHom (𝟙 (L.obj p)) (adj.counit.app (L.obj q)) =
        Prod.mkHom (𝟙 (L.obj p)) f := by
    apply Prod.ext
    · simp
    · change L.map (adj.homEquiv _ _ f) ≫ adj.counit.app (L.obj q) = f
      simpa only [Adjunction.homEquiv_counit] using
        (adj.homEquiv s (L.obj q)).symm_apply_apply f
  rw [hp]

private theorem mate_paste {p q s z x y v : C} {w w' : D}
    (eS : x ≅ T.obj (p, s)) (eQ : y ≅ T.obj (p, q)) (eZ : v ≅ T.obj (p, z))
    (c : U.obj (L.obj q) ≅ z) (t : s ⟶ z) [IsIso t]
    (a : x ⟶ v) (b : v ⟶ U.obj w')
    (cX : L.obj x ⟶ w) (cY : L.obj y ⟶ w')
    (f : L.obj s ⟶ L.obj q) (g : w ⟶ w')
    (ht : eS.hom ≫ T.map (Prod.mkHom (𝟙 p) t) = a ≫ eZ.hom)
    (hf : adj.homEquiv _ _ f = t ≫ c.inv)
    (hμ : L.map eS.hom ≫ μ.hom.app (p, s) ≫
      S.map (Prod.mkHom (𝟙 (L.obj p)) f) ≫ μ.inv.app (p, q) ≫
      L.map eQ.inv ≫ cY = cX ≫ g)
    (hg : adj.homEquiv _ _ (cX ≫ g) = a ≫ b) :
    T.map (Prod.mkHom (𝟙 p) c.hom) ≫ eZ.inv ≫ b =
      mate T S L U adj μ p q ≫ U.map (L.map eQ.inv) ≫ U.map cY := by
  have : IsIso (Prod.mkHom (𝟙 p) (t ≫ c.inv)) := by
    rw [isIso_prod_iff]
    exact ⟨inferInstance, inferInstance⟩
  apply (cancel_epi (eS.hom ≫ T.map (Prod.mkHom (𝟙 p) (t ≫ c.inv)))).1
  simp only [Category.assoc]
  have hc : T.map (Prod.mkHom (𝟙 p) (t ≫ c.inv)) ≫
      T.map (Prod.mkHom (𝟙 p) c.hom) = T.map (Prod.mkHom (𝟙 p) t) := by
    rw [← T.map_comp]
    congr 1
    apply Prod.ext <;> simp
  rw [reassoc_of% hc, ← Category.assoc eS.hom, ht]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [← hf, reassoc_of% mate_precomp T S L U adj μ p q s f]
  have h := congrArg (adj.homEquiv x w') hμ
  have hg' := hg
  simp only [Adjunction.homEquiv_unit, Functor.map_comp, Category.assoc] at h hg' ⊢
  rw [adj.unit_naturality_assoc eS.hom] at h
  exact (h.trans hg').symm

private theorem normalize_conjugate
    {A : Type*} [Category A] (B : A × A ⥤ A)
    {p s q p' s' q' x y w w' : A}
    (aS : x ≅ B.obj (p, s)) (aQ : y ≅ B.obj (p, q))
    (cP : p ≅ p') (cS : s ≅ s') (cQ : q ≅ q')
    (dS : w ≅ B.obj (p', s')) (dQ : w' ≅ B.obj (p', q'))
    (cX : x ⟶ w) (cY : y ⟶ w') (t : s' ⟶ q')
    (hS : aS.hom ≫ B.map (Prod.mkHom cP.hom cS.hom) = cX ≫ dS.hom)
    (hQ : aQ.hom ≫ B.map (Prod.mkHom cP.hom cQ.hom) = cY ≫ dQ.hom) :
    aS.hom ≫ B.map (Prod.mkHom (𝟙 p) (cS.hom ≫ t ≫ cQ.inv)) ≫ aQ.inv ≫ cY =
      cX ≫ dS.hom ≫ B.map (Prod.mkHom (𝟙 p') t) ≫ dQ.inv := by
  apply (cancel_mono dQ.hom).1
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have hh : aQ.inv ≫ cY ≫ dQ.hom = B.map (Prod.mkHom cP.hom cQ.hom) := by
    rw [← hQ, Iso.inv_hom_id_assoc]
  rw [hh, ← B.map_comp]
  have hp : Prod.mkHom (𝟙 p) (cS.hom ≫ t ≫ cQ.inv) ≫
      Prod.mkHom cP.hom cQ.hom =
      Prod.mkHom cP.hom cS.hom ≫ Prod.mkHom (𝟙 p') t := by
    apply Prod.ext <;> simp
  rw [hp, B.map_comp, ← Category.assoc, hS, Category.assoc]

section Comparison
variable {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    (q : A ⥤ C) (r : B ⥤ D)
    (F : A ⥤ B) (V : B ⥤ A) (a : F ⊣ V)
    (L : C ⥤ D) (U : D ⥤ C) (adj : L ⊣ U)
    (e : q ⋙ L ⟶ F ⋙ r) (h : r ⋙ U ≅ V ⋙ q)

private theorem transpose_comparison (X : A) (Y : B) (f : F.obj X ⟶ Y)
    (hunit : adj.unit.app (q.obj X) ≫ U.map (e.app X) ≫ h.hom.app (F.obj X) =
      q.map (a.unit.app X)) :
    adj.homEquiv _ _ (e.app X ≫ r.map f) ≫ h.hom.app Y =
      q.map (a.homEquiv _ _ f) := by
  rw [Adjunction.homEquiv_unit, U.map_comp]
  simp only [Category.assoc]
  have hn := h.hom.naturality f
  change U.map (r.map f) ≫ h.hom.app Y =
    h.hom.app (F.obj X) ≫ q.map (V.map f) at hn
  rw [hn, reassoc_of% hunit, ← q.map_comp, Adjunction.homEquiv_unit]

private theorem transpose_iso_target (X Y : A) (f : F.obj X ⟶ F.obj Y)
    [IsIso (e.app Y)]
    (hunit : adj.unit.app (q.obj X) ≫ U.map (e.app X) ≫ h.hom.app (F.obj X) =
      q.map (a.unit.app X)) :
    adj.homEquiv _ _ (e.app X ≫ r.map f ≫ inv (e.app Y)) =
      q.map (a.homEquiv _ _ f) ≫
        (U.mapIso (asIso (e.app Y)) ≪≫ h.app (F.obj Y)).inv := by
  apply (Iso.eq_comp_inv (U.mapIso (asIso (e.app Y)) ≪≫ h.app (F.obj Y))).2
  simp only [Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom, asIso_hom]
  rw [← Category.assoc, ← adj.homEquiv_naturality_right]
  simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  exact transpose_comparison q r F V a L U adj e h X (F.obj Y) f hunit
end Comparison
end StrengthGenericMate

/- Compare the derived scalar counit and unit with their ordinary
   representatives, retaining the specified exact-restriction comparison. -/
namespace WeilConjectures.IntegralHom.StrengthDerived
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (X : Scheme.{t})
  (D : FiniteFieldDatum.{d}) (hl : l ≠ D.p) (n : ℕ)

set_option maxHeartbeats 1600000 in
-- Comparing the quotient and coefficient wrappers needs additional elaboration time.
private def reductionNat :
    DerivedCategory.Q ⋙ scalarReductionDerivedExtension l E X n ⟶
      (scalarReductionExtension l E X n).mapHomologicalComplex (.up ℤ) ⋙
        DerivedCategory.Q :=
  Functor.whiskerRight (DerivedCategory.quotientCompQhIso _).inv
      (integralDerivedReduction l E X D hl n) ≫
    Functor.whiskerLeft (HomotopyCategory.quotient _ (.up ℤ))
      (integralDerivedReductionCounit l E X D hl n) ≫
    Functor.whiskerRight
      ((integralReductionChangeOfRings l E X D hl n).mapHomotopyCategoryFactors (.up ℤ)).hom
      DerivedCategory.Qh ≫
    Functor.whiskerLeft
      ((integralReductionChangeOfRings l E X D hl n).mapHomologicalComplex (.up ℤ))
      (DerivedCategory.quotientCompQhIso _).hom

set_option maxHeartbeats 1600000 in
-- Comparing the quotient and coefficient wrappers needs additional elaboration time.
private theorem reductionNat_app
    (P : CochainComplex (scalarReductionSource l E X) ℤ) :
    (reductionNat l E X D hl n).app P = reductionCounit l E X D hl n P := rfl

set_option maxHeartbeats 1600000 in
-- Comparing the quotient and coefficient wrappers needs additional elaboration time.
private theorem reductionCounit_isIso
    (P : CochainComplex (scalarReductionSource l E X) ℤ)
    (hP : flat.{t, u} X (completedIntegralCommRingSheaf l E X D hl) P) :
    IsIso (reductionCounit l E X D hl n P) := by
  have := integralDerivedReduction_counit_isIso l E X D hl n P hP
  unfold reductionCounit
  infer_instance

set_option maxHeartbeats 1600000 in
-- Comparing the quotient and coefficient wrappers needs additional elaboration time.
private theorem restrictionComparison_eq
    (P : CochainComplex (scalarReductionSource l E X) ℤ) :
    (scalarReductionDerivedRestriction l E X n).map (reductionCounit l E X D hl n P) ≫
      (scalarReductionRestriction l E X n).mapDerivedCategoryFactors.hom.app
        (((scalarReductionExtension l E X n).mapHomologicalComplex (.up ℤ)).obj P) =
      strengthReductionRepresentativeComparison l E X n P := by
  have hc : reductionCounit l E X D hl n P =
      (scalarReductionCounit l E X n).app
        ((HomotopyCategory.quotient _ (.up ℤ)).obj P) := by
    unfold reductionCounit
    change (scalarReductionDerivedExtension l E X n).map (𝟙 _) ≫
        (scalarReductionCounit l E X n).app
          ((HomotopyCategory.quotient _ (.up ℤ)).obj P) ≫
        (DerivedCategory.Qh (C := scalarReductionTarget l E X n)).map
          (𝟙 (((scalarReductionExtension l E X n).mapHomotopyCategory (.up ℤ)).obj
            ((HomotopyCategory.quotient _ (.up ℤ)).obj P))) ≫ 𝟙 _ = _
    erw [(scalarReductionDerivedExtension l E X n).map_id,
      (DerivedCategory.Qh (C := scalarReductionTarget l E X n)).map_id]
    simp only [Category.id_comp, Category.comp_id]
    exact Category.comp_id _
  have hf : (scalarReductionRestriction l E X n).mapDerivedCategoryFactorsh.hom.app
      (((scalarReductionExtension l E X n).mapHomotopyCategory (.up ℤ)).obj
        ((HomotopyCategory.quotient _ (.up ℤ)).obj P)) =
      (scalarReductionRestriction l E X n).mapDerivedCategoryFactors.hom.app
        (((scalarReductionExtension l E X n).mapHomologicalComplex (.up ℤ)).obj P) := by
    change (scalarReductionRestriction l E X n).mapDerivedCategoryFactorsh.hom.app
      ((HomotopyCategory.quotient _ (.up ℤ)).obj
        (((scalarReductionExtension l E X n).mapHomologicalComplex (.up ℤ)).obj P)) = _
    rw [Functor.mapDerivedCategoryFactorsh_hom_app]
    change (scalarReductionDerivedRestriction l E X n).map (𝟙 _) ≫
      (scalarReductionRestriction l E X n).mapDerivedCategoryFactors.hom.app _ ≫
      𝟙 _ ≫ (DerivedCategory.Qh (C := scalarReductionSource l E X)).map
        (𝟙 ((HomotopyCategory.quotient _ (.up ℤ)).obj
          (((scalarReductionRestriction l E X n).mapHomologicalComplex (.up ℤ)).obj
            (((scalarReductionExtension l E X n).mapHomologicalComplex (.up ℤ)).obj P)))) = _
    erw [(scalarReductionDerivedRestriction l E X n).map_id,
      (DerivedCategory.Qh (C := scalarReductionSource l E X)).map_id]
    simp only [Category.id_comp]
    exact Category.comp_id _
  change _ = (scalarReductionDerivedRestriction l E X n).map
    ((scalarReductionCounit l E X n).app
      ((HomotopyCategory.quotient _ (.up ℤ)).obj P)) ≫ _
  exact congrArg₂ (fun f g ↦ (scalarReductionDerivedRestriction l E X n).map f ≫ g)
    hc hf.symm

set_option maxHeartbeats 1600000 in
-- Comparing the quotient and coefficient wrappers needs additional elaboration time.
private theorem unit_compatibility
    (P : CochainComplex (scalarReductionSource l E X) ℤ)
    (hP : flat.{t, u} X (completedIntegralCommRingSheaf l E X D hl) P) :
    (derivedScalarExtensionRestrictionAdjunction l E X n).choose.unit.app
        (DerivedCategory.Q.obj P) ≫
      (scalarReductionDerivedRestriction l E X n).map
        ((reductionNat l E X D hl n).app P) ≫
      (scalarReductionRestriction l E X n).mapDerivedCategoryFactors.hom.app
        (((scalarReductionExtension l E X n).mapHomologicalComplex (.up ℤ)).obj P) =
      DerivedCategory.Q.map
        (((scalarReductionExtension_adjunction l E X n).choose.mapHomologicalComplex
          (.up ℤ)).unit.app P) := by
  exact (congrArg (fun k ↦
    (derivedScalarExtensionRestrictionAdjunction l E X n).choose.unit.app
      (DerivedCategory.Q.obj P) ≫ k)
    (restrictionComparison_eq l E X D hl n P)).trans
      (strengthUnitComparison l E X n P hP)

end WeilConjectures.IntegralHom.StrengthDerived

/- The coefficient comparison is built from scalar restriction commuting with
   sheafification. This is the construction used for ordinary tensor contraction
   (Stacks 05V4 and 07A4), with its action on pure sections proved here. -/
namespace WeilConjectures.IntegralHom.StrengthCoefficient
open CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped TensorProduct ChangeOfRings

variable (X : Scheme.{t})
  (R S : Sheaf (Scheme.ProEt.topology X) CommRingCat.{max u (t + 1)}) (c : R ⟶ S)

private noncomputable abbrev forgetRing
    (A : Sheaf (Scheme.ProEt.topology X) CommRingCat.{max u (t + 1)}) :=
  (sheafCompose (Scheme.ProEt.topology X)
    (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).obj A

private noncomputable abbrev restriction :=
  SheafOfModules.restrictScalars.{max u (t + 1)} ((sheafCompose (Scheme.ProEt.topology X)
    (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).map c)

private noncomputable abbrev coefficient : Modules.{t, u} X R :=
  (restriction X R S c).obj (SheafOfModules.unit (forgetRing X S))

private noncomputable local instance (priority := 3000) fixedSmall :
    EssentiallySmall.{max u (t + 1)} X.ProEt :=
  WeilConjectures.integralReductionSiteEssentiallySmall.{t, u} X

attribute [local instance] SheafOfModules.monoidalCategory
  SheafOfModules.isMonoidal_W_independentCoefficients

attribute [local irreducible] SheafOfModules.monoidalCategory

private noncomputable def rawIso (M : Modules.{t, u} X R) :
    (PresheafOfModules.restrictScalars.{max u (t + 1)}
      ((sheafCompose (Scheme.ProEt.topology X)
        (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).map c).hom).obj
        (SheafOfModules.changeOfRingsPresheaf.{t, t + 1, max u (t + 1)} c M) ≅
      (coefficient X R S c).val ⊗ M.val :=
  PresheafOfModules.isoMk (fun _ ↦ Iso.refl _) (by
    intro U V f
    ext z
    induction z using TensorProduct.inductionOn with
    | add z w hz hw => simp only [map_add, hz, hw]
    | tmul s x =>
      exact (Classical.choose_spec (SheafOfModules.exists_changeOfRingsMap c M f) s x))

attribute [-instance] tensorLocalization abSheafify abLocallyBijective
  WeilConjectures.integralReductionSiteEssentiallySmall in
private noncomputable def coefficientIso (M : Modules.{t, u} X R) :
    (restriction X R S c).obj (SheafOfModules.changeOfRings.{t, t + 1, max u (t + 1)} c M) ≅
      ((ordinaryTensor.{t, u} X R).obj (coefficient X R S c)).obj M :=
  (SheafOfModules.ScalarHomCancellation.cancellationRestrictSheafifyIso
    ((sheafCompose (Scheme.ProEt.topology X)
      (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).map c)
    (SheafOfModules.changeOfRingsPresheaf.{t, t + 1, max u (t + 1)} c M)).symm ≪≫
    (PresheafOfModules.sheafification.{max u (t + 1)} (𝟙 (forgetRing X R).obj)).mapIso
      (rawIso X R S c M) ≪≫
    (SheafOfModules.tensorObjIsoSheafification.{t, t + 1, max u (t + 1)}
      (R := R) (coefficient X R S c) M).symm

set_option maxHeartbeats 800000 in
-- Compare the scalar and module sheafifications explicitly.
attribute [-instance] tensorLocalization abSheafify abLocallyBijective
  WeilConjectures.integralReductionSiteEssentiallySmall in
private theorem coefficientIso_pure (M : Modules.{t, u} X R) (U : X.ProEtᵒᵖ)
    (s : S.obj.obj U) (x : M.val.obj U) :
    (coefficientIso X R S c M).hom.val.app U
      ((toSheafify (Scheme.ProEt.topology X)
        (SheafOfModules.changeOfRingsPresheaf.{t, t + 1, max u (t + 1)} c M).presheaf).app U
          (s ⊗ₜ[R.obj.obj U, (c.hom.app U).hom] x)) =
      pair.{t, u} X R (coefficient X R S c) M U s x := by
  let A := forgetRing X R
  let B := forgetRing X S
  let α := (sheafCompose (Scheme.ProEt.topology X)
    (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).map c
  let P := SheafOfModules.changeOfRingsPresheaf.{t, t + 1, max u (t + 1)} c M
  let a := PresheafOfModules.sheafification.{max u (t + 1)} (𝟙 A.obj)
  let adj := PresheafOfModules.sheafificationAdjunction.{max u (t + 1)} (𝟙 A.obj)
  let e := SheafOfModules.ScalarHomCancellation.cancellationRestrictSheafifyIso α P
  have he : e.hom.val.app U
      ((adj.unit.app ((PresheafOfModules.restrictScalars.{max u (t + 1)} α.hom).obj P)).app U
        (s ⊗ₜ[R.obj.obj U, (c.hom.app U).hom] x)) =
      (toSheafify (Scheme.ProEt.topology X) P.presheaf).app U
        (s ⊗ₜ[R.obj.obj U, (c.hom.app U).hom] x) := by
    have h := SheafOfModules.ScalarHomCancellation.cancellationRestrictSheafifyHom_toSheaf
      α P
    exact congrArg (fun f ↦ f.hom.app U
      ((toSheafify (Scheme.ProEt.topology X) P.presheaf).app U
        (s ⊗ₜ[R.obj.obj U, (c.hom.app U).hom] x))) h
  have hei : e.inv.val.app U
      ((toSheafify (Scheme.ProEt.topology X) P.presheaf).app U
        (s ⊗ₜ[R.obj.obj U, (c.hom.app U).hom] x)) =
      (adj.unit.app ((PresheafOfModules.restrictScalars.{max u (t + 1)} α.hom).obj P)).app U
        (s ⊗ₜ[R.obj.obj U, (c.hom.app U).hom] x) := by
    rw [← he]
    exact congrArg (fun f ↦ f.val.app U
      ((adj.unit.app ((PresheafOfModules.restrictScalars.{max u (t + 1)} α.hom).obj P)).app U
        (s ⊗ₜ[R.obj.obj U, (c.hom.app U).hom] x))) e.hom_inv_id
  change (SheafOfModules.tensorObjIsoSheafification.{t, t + 1, max u (t + 1)}
    (R := R) (coefficient X R S c) M).inv.val.app U
    ((a.map (rawIso X R S c M).hom).val.app U (e.inv.val.app U _)) = _
  rw [hei]
  have hn := congrArg (fun f ↦ f.app U
    (s ⊗ₜ[R.obj.obj U, (c.hom.app U).hom] x))
    (adj.unit.naturality (rawIso X R S c M).hom)
  exact congrArg ((SheafOfModules.tensorObjIsoSheafification.{t, t + 1, max u (t + 1)}
    (R := R) (coefficient X R S c) M).inv.val.app U) hn.symm

section Levels

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

private noncomputable abbrev base := completedIntegralCommRingSheafUnrestricted l E X
private noncomputable abbrev level (n : ℕ) := integralCoefficientCommRingSheaf l E X n
private noncomputable abbrev projection (n : ℕ) :=
  completedIntegralCommRingProjectionUnrestricted l E X n
private noncomputable abbrev coeff (n : ℕ) :=
  coefficient X (base X l E) (level X l E n) (projection X l E n)

attribute [local irreducible] scalarReductionExistence
  completedIntegralCoefficientSheafUnrestricted constantSheaf
attribute [local implicit_reducible] scalarReductionExtension
set_option backward.defeqAttrib.useBackward true
attribute [local implicit_reducible] completedIntegralCommRingSheafUnrestricted

private noncomputable def levelIso (n : ℕ) (M : scalarReductionSource l E X) :
    (strengthReductionRestricted l E X n).obj M ≅
      ((ordinaryTensor.{t, u} X (base X l E)).obj (coeff X l E n)).obj M :=
  (scalarReductionRestriction l E X n).mapIso
    (eqToIso ((scalarReductionExistence.{t, u} l E X n).choose_spec.choose M)) ≪≫
    coefficientIso X (base X l E) (level X l E n) (projection X l E n) M

set_option maxHeartbeats 1600000 in
-- Total tensor comparison types require unfolding the coefficient wrappers.
private theorem levelIso_pure (n : ℕ) (M : scalarReductionSource l E X)
    (U : X.ProEtᵒᵖ) (s : (level X l E n).obj.obj U) (x : M.val.obj U) :
    (levelIso X l E n M).hom.val.app U (strengthReductionTensor l E X n M U s x) =
      pair.{t, u} X (base X l E) (coeff X l E n) M U s x := by
  let h := (scalarReductionExistence.{t, u} l E X n).choose_spec.choose M
  change (coefficientIso X (base X l E) (level X l E n)
    (projection X l E n) M).hom.val.app U
      (((eqToHom h.symm ≫ eqToHom h).val.app U) _) = _
  simp only [eqToHom_trans, eqToHom_refl]
  exact coefficientIso_pure X (base X l E) (level X l E n) (projection X l E n) M U s x

private theorem levelIso_inv_pure (n : ℕ) (M : scalarReductionSource l E X)
    (U : X.ProEtᵒᵖ) (s : (level X l E n).obj.obj U) (x : M.val.obj U) :
    (levelIso X l E n M).inv.val.app U
      (pair.{t, u} X (base X l E) (coeff X l E n) M U s x) =
      strengthReductionTensor l E X n M U s x := by
  rw [← levelIso_pure X l E n M U s x]
  exact congrArg (fun f ↦ f.val.app U (strengthReductionTensor l E X n M U s x))
    (levelIso X l E n M).hom_inv_id

end Levels
end WeilConjectures.IntegralHom.StrengthCoefficient

/- Extend the normalization from scalar generators to all local sections,
   then use total-summand extensionality to identify the ordinary transpose. -/
namespace WeilConjectures.IntegralHom.StrengthOrdinary

attribute [local irreducible] scalarReductionExistence constantSheaf
attribute [local implicit_reducible] integralCoefficientSheaf integralCoefficientCommRingSheaf
  completedIntegralCommRingSheafUnrestricted

variable (X : Scheme.{t}) (R : Sheaf (Scheme.ProEt.topology X) CommRingCat.{max u (t + 1)})

private def totalPairAdd (P Q : CochainComplex (Modules.{t, u} X R) ℤ)
    (i j : ℤ) (U : X.ProEtᵒᵖ) (x : (P.X i).val.obj U) :
    (Q.X j).val.obj U →+
      ((((totalTensor.{t, u} X R).obj P).obj Q).X (i + j)).val.obj U where
  toFun := fun y ↦ totalPair.{t, u} X R P Q i j U x y
  map_zero' := by simp only [totalPair, pair, TensorProduct.tmul_zero, map_zero]
  map_add' := by
    intro y z
    simp only [totalPair, pair, TensorProduct.tmul_add, map_add]

private theorem totalPair_smul_right (P Q : CochainComplex (Modules.{t, u} X R) ℤ)
    (i j : ℤ) (U : X.ProEtᵒᵖ) (r : R.obj.obj U)
    (x : (P.X i).val.obj U) (y : (Q.X j).val.obj U) :
    totalPair.{t, u} X R P Q i j U x (r • y) =
      r • totalPair.{t, u} X R P Q i j U x y := by
  simp only [totalPair, pair, TensorProduct.tmul_smul, map_smul]

private theorem totalPair_restrict (P Q : CochainComplex (Modules.{t, u} X R) ℤ)
    (i j : ℤ) {U V : X.ProEtᵒᵖ} (f : U ⟶ V)
    (x : (P.X i).val.obj U) (y : (Q.X j).val.obj U) :
    ((((totalTensor.{t, u} X R).obj P).obj Q).X (i + j)).val.map f
        (totalPair.{t, u} X R P Q i j U x y) =
      totalPair.{t, u} X R P Q i j V
        ((P.X i).val.map f x) ((Q.X j).val.map f y) := by
  let := SheafOfModules.isMonoidal_W_independentCoefficients.{t + 1, t, max u (t + 1)} R
  let := countableColimits.{t, u} X R
  let := ordinaryTensorZero.{t, u} X R
  let : ∀ M : Modules.{t, u} X R,
      ((ordinaryTensor.{t, u} X R).obj M).PreservesZeroMorphisms :=
    fun M ↦ ordinaryTensorObjZero.{t, u} X R M
  let ι := CochainComplex.ιMapBifunctor P Q (ordinaryTensor.{t, u} X R) i j (i + j) rfl
  exact (PresheafOfModules.naturality_apply ι.val f
    (pair.{t, u} X R (P.X i) (Q.X j) U x y)).symm.trans
      (congrArg (ι.val.app V)
        (CategoryTheory.CochainPullback.moduleTmul_restrict.{max u (t + 1), t + 1, t}
          (P.X i) (Q.X j) f x y))

private theorem totalPair_map {P P' Q Q' : CochainComplex (Modules.{t, u} X R) ℤ}
    (f : P ⟶ P') (g : Q ⟶ Q') (i j : ℤ) (U : X.ProEtᵒᵖ)
    (x : (P.X i).val.obj U) (y : (Q.X j).val.obj U) :
    ((((totalTensor.{t, u} X R).map f).app Q ≫
      ((totalTensor.{t, u} X R).obj P').map g).f (i + j)).val.app U
        (totalPair.{t, u} X R P Q i j U x y) =
      totalPair.{t, u} X R P' Q' i j U ((f.f i).val.app U x) ((g.f j).val.app U y) := by
  exact CategoryTheory.ScalarHomTensor.tensor_generator_map.{t + 1, t, u}
    (J := Scheme.ProEt.topology X) f g i j (i + j) rfl U x y

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

private abbrev B := completedIntegralCommRingSheafUnrestricted l E X
private abbrev S (n : ℕ) := integralCoefficientCommRingSheaf l E X n
private abbrev F (n : ℕ) :=
  (scalarReductionExtension l E X n).mapHomologicalComplex (.up ℤ)
private abbrev U (n : ℕ) :=
  (scalarReductionRestriction l E X n).mapHomologicalComplex (.up ℤ)

private theorem reduction_smul (n : ℕ) (M : scalarReductionSource l E X)
    (V : X.ProEtᵒᵖ) (s : (S X l E n).obj.obj V) (x : M.val.obj V) :
    strengthReductionTensor l E X n M V s x = s • strengthReductionTensor l E X n M V 1 x := by
  exact WeilConjectures.identifiedSection_smul
    (completedIntegralCommRingProjectionUnrestricted l E X n)
    (scalarReductionExtension l E X n)
    ((scalarReductionExistence l E X n).choose_spec.choose) M V s x

private theorem beta_scalar (n : ℕ)
    (P Q : CochainComplex (scalarReductionSource l E X) ℤ)
    (beta : ((totalTensor.{t, u} X (S X l E n)).obj ((F X l E n).obj P)).obj
      ((F X l E n).obj Q) ⟶
      (F X l E n).obj (((totalTensor.{t, u} X (B X l E)).obj P).obj Q))
    (hbeta : ∀ (i j : ℤ) (V : X.ProEtᵒᵖ)
      (x : (P.X i).val.obj V) (y : (Q.X j).val.obj V),
      (beta.f (i + j)).val.app V
        (totalPair.{t, u} X (S X l E n) ((F X l E n).obj P) ((F X l E n).obj Q)
          i j V (strengthReductionTensor l E X n (P.X i) V 1 x)
            (strengthReductionTensor l E X n (Q.X j) V 1 y)) =
      strengthReductionTensor l E X n _ V 1
        (totalPair.{t, u} X (B X l E) P Q i j V x y))
    (i j : ℤ) (V : X.ProEtᵒᵖ) (s : (S X l E n).obj.obj V)
    (x : (P.X i).val.obj V) (y : (Q.X j).val.obj V) :
    (beta.f (i + j)).val.app V
      (totalPair.{t, u} X (S X l E n) ((F X l E n).obj P) ((F X l E n).obj Q)
        i j V (strengthReductionTensor l E X n (P.X i) V 1 x)
          (strengthReductionTensor l E X n (Q.X j) V s y)) =
    strengthReductionTensor l E X n _ V s
      (totalPair.{t, u} X (B X l E) P Q i j V x y) := by
  rw [reduction_smul X l E n (Q.X j) V s y]
  erw [totalPair_smul_right, map_smul, hbeta]
  exact (reduction_smul X l E n _ V s _).symm

set_option maxHeartbeats 1600000 in
-- The unit normalization crosses the finite coefficient wrappers.
private theorem unit_restrict (n : ℕ) (M : scalarReductionSource l E X)
    {V W : X.ProEtᵒᵖ} (i : V ⟶ W) (x : M.val.obj V) :
    ((scalarReductionExtension l E X n).obj M).val.map i
        (strengthReductionTensor l E X n M V 1 x) =
      strengthReductionTensor l E X n M W 1 (M.val.map i x) := by
  have h := PresheafOfModules.naturality_apply
    (((scalarReductionExtension_adjunction l E X n).choose.unit.app M).val) i x
  have hu (W : X.ProEtᵒᵖ) (y : M.val.obj W) :
      (((scalarReductionExtension_adjunction l E X n).choose.unit.app M).val.app W y) =
        strengthReductionTensor l E X n M W 1 y :=
    (scalarReductionExtension_adjunction l E X n).choose_spec M W y
  change _ = _ at h
  rw [hu, hu] at h
  exact h.symm

private theorem beta_restricted (n : ℕ)
    (P Q : CochainComplex (scalarReductionSource l E X) ℤ)
    (beta : ((totalTensor.{t, u} X (S X l E n)).obj ((F X l E n).obj P)).obj
      ((F X l E n).obj Q) ⟶
      (F X l E n).obj (((totalTensor.{t, u} X (B X l E)).obj P).obj Q))
    (b : ((totalTensor.{t, u} X (B X l E)).obj P).obj
        ((U X l E n).obj ((F X l E n).obj Q)) ⟶
      (U X l E n).obj ((F X l E n).obj
        (((totalTensor.{t, u} X (B X l E)).obj P).obj Q)))
    (hbeta : ∀ (i j : ℤ) (V : X.ProEtᵒᵖ) (s : (S X l E n).obj.obj V)
      (x : (P.X i).val.obj V) (y : (Q.X j).val.obj V),
      (beta.f (i + j)).val.app V
        (totalPair.{t, u} X (S X l E n) ((F X l E n).obj P) ((F X l E n).obj Q)
          i j V (strengthReductionTensor l E X n (P.X i) V 1 x)
            (strengthReductionTensor l E X n (Q.X j) V s y)) =
      strengthReductionTensor l E X n _ V s
        (totalPair.{t, u} X (B X l E) P Q i j V x y))
    (hb : ∀ (i j : ℤ) (V : X.ProEtᵒᵖ) (s : (S X l E n).obj.obj V)
      (x : (P.X i).val.obj V) (y : (Q.X j).val.obj V),
      (b.f (i + j)).val.app V
        (totalPair.{t, u} X (B X l E) P ((U X l E n).obj ((F X l E n).obj Q))
          i j V x (strengthReductionTensor l E X n (Q.X j) V s y)) =
      strengthReductionTensor l E X n _ V s
        (totalPair.{t, u} X (B X l E) P Q i j V x y))
    (i j : ℤ) (V : X.ProEtᵒᵖ) (x : (P.X i).val.obj V)
    (z : (((F X l E n).obj Q).X j).val.obj V) :
    (beta.f (i + j)).val.app V
      (totalPair.{t, u} X (S X l E n) ((F X l E n).obj P) ((F X l E n).obj Q)
        i j V (strengthReductionTensor l E X n (P.X i) V 1 x) z) =
    (b.f (i + j)).val.app V
      (totalPair.{t, u} X (B X l E) P ((U X l E n).obj ((F X l E n).obj Q))
        i j V x z) := by
  let M : Modules.{t, u} X (B X l E) :=
    (SheafOfModules.restrictScalars.{max u (t + 1)}
      ((sheafCompose (Scheme.ProEt.topology X)
        (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).map
          (completedIntegralCommRingProjectionUnrestricted l E X n))).obj
      (SheafOfModules.unit ((sheafCompose (Scheme.ProEt.topology X)
        (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).obj (S X l E n)))
  let H := ((U X l E n).obj ((F X l E n).obj
    (((totalTensor.{t, u} X (B X l E)).obj P).obj Q))).X (i + j)
  let e : (((U X l E n).obj ((F X l E n).obj Q)).X j) ≅
      ((ordinaryTensor.{t, u} X (B X l E)).obj M).obj (Q.X j) :=
    WeilConjectures.IntegralHom.StrengthCoefficient.levelIso X l E n (Q.X j)
  let f (W : X.ProEtᵒᵖ) (x : (P.X i).val.obj W) :=
    (beta.f (i + j)).val.app W |>.hom.toAddMonoidHom.comp
      ((totalPairAdd X (S X l E n) ((F X l E n).obj P) ((F X l E n).obj Q)
        i j W (strengthReductionTensor l E X n (P.X i) W 1 x)).comp
          (e.inv.val.app W).hom.toAddMonoidHom)
  let g (W : X.ProEtᵒᵖ) (x : (P.X i).val.obj W) :=
    (b.f (i + j)).val.app W |>.hom.toAddMonoidHom.comp
      ((totalPairAdd X (B X l E) P ((U X l E n).obj ((F X l E n).obj Q))
        i j W x).comp (e.inv.val.app W).hom.toAddMonoidHom)
  have hf {V W : X.ProEtᵒᵖ} (a : V ⟶ W) (x : (P.X i).val.obj V) (z) :
      H.val.map a (f V x z) =
        f W ((P.X i).val.map a x) (((ordinaryTensor.{t, u} X (B X l E)).obj M).obj
          (Q.X j) |>.val.map a z) := by
    have hn := (PresheafOfModules.naturality_apply (beta.f (i + j)).val a
      (totalPair.{t, u} X (S X l E n) ((F X l E n).obj P) ((F X l E n).obj Q)
        i j V (strengthReductionTensor l E X n (P.X i) V 1 x) (e.inv.val.app V z))).symm
    have hp := totalPair_restrict X (S X l E n)
      ((F X l E n).obj P) ((F X l E n).obj Q) i j a
      (strengthReductionTensor l E X n (P.X i) V 1 x) (e.inv.val.app V z)
    have hu := unit_restrict X l E n (P.X i) a x
    have he := (PresheafOfModules.naturality_apply e.inv.val a z).symm
    exact hn.trans (congrArg ((beta.f (i + j)).val.app W)
      (hp.trans (congrArg₂
        (totalPair.{t, u} X (S X l E n) ((F X l E n).obj P) ((F X l E n).obj Q)
          i j W) hu he)))
  have hg {V W : X.ProEtᵒᵖ} (a : V ⟶ W) (x : (P.X i).val.obj V) (z) :
      H.val.map a (g V x z) =
        g W ((P.X i).val.map a x) (((ordinaryTensor.{t, u} X (B X l E)).obj M).obj
          (Q.X j) |>.val.map a z) := by
    have hn := (PresheafOfModules.naturality_apply (b.f (i + j)).val a
      (totalPair.{t, u} X (B X l E) P ((U X l E n).obj ((F X l E n).obj Q))
        i j V x (e.inv.val.app V z))).symm
    have hp := totalPair_restrict X (B X l E)
      P ((U X l E n).obj ((F X l E n).obj Q)) i j a x (e.inv.val.app V z)
    have he := (PresheafOfModules.naturality_apply e.inv.val a z).symm
    exact hn.trans (congrArg ((b.f (i + j)).val.app W)
      (hp.trans (congrArg
        (totalPair.{t, u} X (B X l E) P ((U X l E n).obj ((F X l E n).obj Q))
          i j W ((P.X i).val.map a x)) he)))
  have hp (W : X.ProEtᵒᵖ) (x : (P.X i).val.obj W)
      (s : M.val.obj W) (y : (Q.X j).val.obj W) :
      f W x (pair.{t, u} X (B X l E) M (Q.X j) W s y) =
        g W x (pair.{t, u} X (B X l E) M (Q.X j) W s y) := by
    change (beta.f (i + j)).val.app W
      (totalPair.{t, u} X (S X l E n) ((F X l E n).obj P) ((F X l E n).obj Q)
        i j W (strengthReductionTensor l E X n (P.X i) W 1 x) (e.inv.val.app W _)) =
      (b.f (i + j)).val.app W
        (totalPair.{t, u} X (B X l E) P ((U X l E n).obj ((F X l E n).obj Q))
          i j W x (e.inv.val.app W _))
    have hc : e.inv.val.app W (pair.{t, u} X (B X l E) M (Q.X j) W s y) =
        strengthReductionTensor l E X n (Q.X j) W s y :=
      WeilConjectures.IntegralHom.StrengthCoefficient.levelIso_inv_pure
        X l E n (Q.X j) W s y
    have hleft := congrArg (fun z ↦ (beta.f (i + j)).val.app W
      (totalPair.{t, u} X (S X l E n) ((F X l E n).obj P) ((F X l E n).obj Q)
        i j W (strengthReductionTensor l E X n (P.X i) W 1 x) z)) hc
    have hright := congrArg (fun z ↦ (b.f (i + j)).val.app W
      (totalPair.{t, u} X (B X l E) P ((U X l E n).obj ((F X l E n).obj Q))
        i j W x z)) hc
    exact (hleft.trans (hbeta i j W s x y)).trans
      (hright.trans (hb i j W s x y)).symm
  have hh := WeilConjectures.pure_local_ext (B X l E) M (Q.X j) H
    ((P.X i).val.presheaf) f g hf hg hp V x (e.hom.val.app V z)
  have he : e.inv.val.app V (e.hom.val.app V z) = z := by
    have hh := congrArg (fun f ↦
      fun w : ((((U X l E n).obj ((F X l E n).obj Q)).X j).val.obj V) ↦
        f.val.app V w) e.hom_inv_id
    exact congrFun hh z
  change (beta.f (i + j)).val.app V
      (totalPair.{t, u} X (S X l E n) ((F X l E n).obj P) ((F X l E n).obj Q)
        i j V (strengthReductionTensor l E X n (P.X i) V 1 x)
          (e.inv.val.app V (e.hom.val.app V z))) =
    (b.f (i + j)).val.app V
      (totalPair.{t, u} X (B X l E) P ((U X l E n).obj ((F X l E n).obj Q))
        i j V x (e.inv.val.app V (e.hom.val.app V z))) at hh
  rw [he] at hh
  exact hh

private theorem totalPair_map_second
    {P Q Q' : CochainComplex (Modules.{t, u} X R) ℤ}
    (g : Q ⟶ Q') (i j : ℤ) (V : X.ProEtᵒᵖ)
    (x : (P.X i).val.obj V) (y : (Q.X j).val.obj V) :
    ((((totalTensor.{t, u} X R).obj P).map g).f (i + j)).val.app V
        (totalPair.{t, u} X R P Q i j V x y) =
      totalPair.{t, u} X R P Q' i j V x ((g.f j).val.app V y) := by
  have h := totalPair_map X R (𝟙 P) g i j V x y
  erw [(totalTensor.{t, u} X R).map_id, NatTrans.id_app, Category.id_comp] at h
  simpa using h

private theorem ordinary_square (n : ℕ)
    (P Q Z : CochainComplex (scalarReductionSource l E X) ℤ)
    (t : Z ⟶ (U X l E n).obj ((F X l E n).obj Q))
    (betaZ : ((totalTensor.{t, u} X (S X l E n)).obj ((F X l E n).obj P)).obj
      ((F X l E n).obj Z) ⟶
      (F X l E n).obj (((totalTensor.{t, u} X (B X l E)).obj P).obj Z))
    [IsIso betaZ]
    (betaQ : ((totalTensor.{t, u} X (S X l E n)).obj ((F X l E n).obj P)).obj
      ((F X l E n).obj Q) ⟶
      (F X l E n).obj (((totalTensor.{t, u} X (B X l E)).obj P).obj Q))
    (b : ((totalTensor.{t, u} X (B X l E)).obj P).obj
        ((U X l E n).obj ((F X l E n).obj Q)) ⟶
      (U X l E n).obj ((F X l E n).obj
        (((totalTensor.{t, u} X (B X l E)).obj P).obj Q)))
    (hZ : ∀ (i j : ℤ) (V : X.ProEtᵒᵖ)
      (x : (P.X i).val.obj V) (z : (Z.X j).val.obj V),
      (betaZ.f (i + j)).val.app V
        (totalPair.{t, u} X (S X l E n) ((F X l E n).obj P) ((F X l E n).obj Z)
          i j V (strengthReductionTensor l E X n (P.X i) V 1 x)
            (strengthReductionTensor l E X n (Z.X j) V 1 z)) =
      strengthReductionTensor l E X n _ V 1
        (totalPair.{t, u} X (B X l E) P Z i j V x z))
    (hQ : ∀ (i j : ℤ) (V : X.ProEtᵒᵖ)
      (x : (P.X i).val.obj V) (y : (Q.X j).val.obj V),
      (betaQ.f (i + j)).val.app V
        (totalPair.{t, u} X (S X l E n) ((F X l E n).obj P) ((F X l E n).obj Q)
          i j V (strengthReductionTensor l E X n (P.X i) V 1 x)
            (strengthReductionTensor l E X n (Q.X j) V 1 y)) =
      strengthReductionTensor l E X n _ V 1
        (totalPair.{t, u} X (B X l E) P Q i j V x y))
    (hb : ∀ (i j : ℤ) (V : X.ProEtᵒᵖ) (s : (S X l E n).obj.obj V)
      (x : (P.X i).val.obj V) (y : (Q.X j).val.obj V),
      (b.f (i + j)).val.app V
        (totalPair.{t, u} X (B X l E) P ((U X l E n).obj ((F X l E n).obj Q))
          i j V x (strengthReductionTensor l E X n (Q.X j) V s y)) =
      strengthReductionTensor l E X n _ V s
        (totalPair.{t, u} X (B X l E) P Q i j V x y)) :
    let adj := (scalarReductionExtension_adjunction l E X n).choose.mapHomologicalComplex (.up ℤ)
    let t' := (adj.homEquiv _ _).symm t
    adj.homEquiv _ _ (inv betaZ ≫
        ((totalTensor.{t, u} X (S X l E n)).obj ((F X l E n).obj P)).map t' ≫ betaQ) =
      ((totalTensor.{t, u} X (B X l E)).obj P).map t ≫ b := by
  dsimp only
  let adj := (scalarReductionExtension_adjunction l E X n).choose.mapHomologicalComplex (.up ℤ)
  let t' := (adj.homEquiv _ _).symm t
  rw [Adjunction.homEquiv_unit]
  ext k : 1
  apply CategoryTheory.ScalarHomTensor.total_pure_hom_ext.{t + 1, t, u}
    P Z k _
  intro i j hij V x z
  subst k
  have hu (M : scalarReductionSource l E X) (V : X.ProEtᵒᵖ) (x : M.val.obj V) :
      ((scalarReductionExtension_adjunction l E X n).choose.unit.app M).val.app V x =
        strengthReductionTensor l E X n M V 1 x :=
    (scalarReductionExtension_adjunction l E X n).choose_spec M V x
  have ht := congrArg (fun a ↦ (a.f j).val.app V z)
    ((adj.homEquiv _ _).apply_symm_apply t)
  change (t'.f j).val.app V
      (((scalarReductionExtension_adjunction l E X n).choose.unit.app (Z.X j)).val.app V z) =
    (t.f j).val.app V z at ht
  rw [hu] at ht
  have hz := congrArg (fun a ↦ (inv betaZ).f (i + j) |>.val.app V a) (hZ i j V x z)
  have hi (a) : ((inv betaZ).f (i + j)).val.app V ((betaZ.f (i + j)).val.app V a) = a :=
    ConcreteCategory.congr_hom
      (congrArg (fun f ↦ (f.f (i + j)).val.app V) (asIso betaZ).hom_inv_id) a
  rw [hi] at hz
  change (betaQ.f (i + j)).val.app V
      (((((totalTensor.{t, u} X (S X l E n)).obj ((F X l E n).obj P)).map t').f
        (i + j)).val.app V
        (((inv betaZ).f (i + j)).val.app V
          (((scalarReductionExtension_adjunction l E X n).choose.unit.app
            ((((totalTensor.{t, u} X (B X l E)).obj P).obj Z).X (i + j))).val.app V
              (totalPair.{t, u} X (B X l E) P Z i j V x z)))) =
    (b.f (i + j)).val.app V
      (((((totalTensor.{t, u} X (B X l E)).obj P).map t).f (i + j)).val.app V
        (totalPair.{t, u} X (B X l E) P Z i j V x z))
  rw [hu, ← hz, totalPair_map_second, totalPair_map_second]
  erw [ht]
  exact beta_restricted X l E n P Q betaQ b
    (beta_scalar X l E n P Q betaQ hQ) hb i j V x ((t.f j).val.app V z)

end WeilConjectures.IntegralHom.StrengthOrdinary

namespace WeilConjectures.IntegralHom

namespace StrengthModel

open CategoryTheory.Limits CategoryTheory.MonoidalCategory

private def extendIso
    {A B E K : Type*} [Category A] [Category B] [Category E] [Category K]
    (W : MorphismProperty A) (q : A ⥤ B) [q.IsLocalization W]
    (I : K ⥤ A) [(I ⋙ q).IsLocalization (W.inverseImage I)]
    (F : B ⥤ E) (H : A ⥤ E) (hH : W.IsInvertedBy H)
    (e : I ⋙ H ≅ I ⋙ q ⋙ F) :
    { c : H ≅ q ⋙ F // ∀ X, c.app (I.obj X) = e.app X } := by
  let H' := Localization.lift H hH q
  let φ := Localization.fac H hH q
  let b : (I ⋙ q) ⋙ H' ≅ (I ⋙ q) ⋙ F := Functor.isoWhiskerLeft I φ ≪≫ e
  let ff := Localization.fullyFaithfulWhiskeringLeft (I ⋙ q) (W.inverseImage I) E
  let b' := ff.preimageIso b
  refine ⟨φ.symm ≪≫ Functor.isoWhiskerLeft q b', ?_⟩
  intro X
  apply Iso.ext
  have hb := congr_app (ff.map_preimage b.hom) X
  change φ.inv.app (I.obj X) ≫ b'.hom.app (q.obj (I.obj X)) = (e.app X).hom
  rw [show b'.hom.app (q.obj (I.obj X)) = b.hom.app X from hb]
  simp [b]

variable (Y : Scheme.{t})
    (R : Sheaf (Scheme.ProEt.topology Y) CommRingCat.{max u (t + 1)})

private theorem tensor_inverts (P : CochainComplex (Modules.{t, u} Y R) ℤ)
    (hP : flat.{t, u} Y R P) :
    (HomologicalComplex.quasiIso (Modules.{t, u} Y R) (.up ℤ)).IsInvertedBy
      ((totalTensor.{t, u} Y R).obj P ⋙ DerivedCategory.Q) := by
  let := SheafOfModules.isMonoidal_W_independentCoefficients.{t + 1, t, max u (t + 1)} R
  let : MonoidalCategory (Modules.{t, u} Y R) := SheafOfModules.monoidalCategory R
  let : MonoidalPreadditive (Modules.{t, u} Y R) :=
    SheafOfModules.cochainModulesPreadditive R
  have hk := (HomotopyCategory.kFlat_quotient_obj_iff P).1
    (CategoryTheory.RingedDerivedNative.kFlat.{t + 1, t, u} (Scheme.ProEt.topology Y) R P hP)
  intro A B f hf
  change IsIso (DerivedCategory.Q.map (((totalTensor.{t, u} Y R).obj P).map f))
  apply (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2
  exact hk.1 f hf

private theorem comparison_exists (a : TensorPresentation.{t, u} Y R)
    (P : CochainComplex (Modules.{t, u} Y R) ℤ) (hP : flat.{t, u} Y R P) :
    ∃ e : (totalTensor.{t, u} Y R).obj P ⋙ DerivedCategory.Q ≅
        DerivedCategory.Q ⋙ (Functor.curry.obj a.tensor).obj (DerivedCategory.Q.obj P),
      ∀ (Q : CochainComplex (Modules.{t, u} Y R) ℤ) (hQ : flat.{t, u} Y R Q),
        e.hom.app Q = a.representative.hom.app (⟨P, hP⟩, ⟨Q, hQ⟩) := by
  let I := (flat.{t, u} Y R).ι
  let A := (Functor.curry.obj a.tensor).obj (DerivedCategory.Q.obj P)
  let H := (totalTensor.{t, u} Y R).obj P ⋙ DerivedCategory.Q
  let e : I ⋙ H ≅ I ⋙ DerivedCategory.Q ⋙ A :=
    NatIso.ofComponents (fun Q ↦ a.representative.app (⟨P, hP⟩, Q)) (by
      intro Q Q' f
      have h := a.representative.hom.naturality
        (X := (⟨P, hP⟩, Q)) (Y := (⟨P, hP⟩, Q')) (𝟙 _, f)
      simpa [I, H, A, totalTensor] using h)
  let : (I ⋙ DerivedCategory.Q).IsLocalization
      ((HomologicalComplex.quasiIso (Modules.{t, u} Y R) (.up ℤ)).inverseImage I) :=
    CategoryTheory.RingedDerivedNative.kFlatLocalization.{t + 1, t, u, max u (t + 1) + 1}
      (Scheme.ProEt.topology Y) R
  let c := extendIso (HomologicalComplex.quasiIso (Modules.{t, u} Y R) (.up ℤ))
    DerivedCategory.Q I A H (tensor_inverts Y R P hP) e
  refine ⟨c.val, ?_⟩
  intro Q hQ
  exact congrArg Iso.hom (c.property ⟨Q, hQ⟩)

end StrengthModel

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (X : Scheme.{t})

variable (D : FiniteFieldDatum.{d}) (hl : l ≠ D.p)

attribute [-instance] StrengthModel.fixedSmall StrengthModel.fixedSheafify
  StrengthModel.fixedLocallyBijective StrengthModel.fixedDerived

attribute [local irreducible] scalarReductionExistence scalarReductionDerivedExistence
  integralReductionExistence integralReductionDerivedExistence constantSheaf
  completedIntegralCoefficientSheafUnrestricted HasDerivedCategory.standard

attribute [local implicit_reducible] completedIntegralCommRingSheaf
  completedIntegralCommRingSheafUnrestricted integralCoefficientCommRingSheaf
  integralCoefficientSheaf

set_option maxHeartbeats 16000000 in
-- Keep the coefficient wrappers folded while elaborating the comparison squares.
/-- The scalar-adjunction tensor mate is represented by the ordinary contraction.
This is a one-level calculation: no consecutive quotient map occurs in it.

Source: Stacks 03CZ, lemma-adjointness-tensor-restrict; 06YY,
lemma-derived-base-change; 07A4, lemma-pullback-tensor-product.

Proof: fix the K-flat first factor P. Tensoring with P sends acyclic complexes
to acyclic complexes, hence preserves quasi-isomorphisms, by the native K-flat
tensor API. Extend a.representative in the second argument along the K-flat
localization. This gives e, natural on all complexes, with its prescribed value
on K-flat Q. To calculate the mate, resolve the restricted extension of Q by a
K-flat complex S. Use naturality to replace e there by its value on S. Transpose
through the scalar adjunction. Its ordinary counit multiplies scalar factors.
ReductionPresentation.normalization fixes the two tensor comparisons on the
K-flat pairs (P, S) and (P, Q). Cancel these comparisons and the resolution of S.
On each homogeneous pure tensor the resulting chain map sends
x tensor (s tensor y) to s tensor (x tensor y). Thus it is b by the tensor
universal property, sheafification, and total-summand extensionality. Localize
this identity. The restriction comparison is the exact-restriction factor of
the scalar counit, giving precisely the displayed equation. The construction
of e is independent of the coefficient level; the calculation applies separately
to every n and every normalized m, so it assumes no compatibility between them.
(blueprint: lem-sf-integral-tensor-restriction-mate-model). -/
private theorem restrictionTensor_mate_model
    (a : TensorPresentation.{t, u} X (completedIntegralCommRingSheaf l E X D hl))
    (P : CochainComplex (scalarReductionSource l E X) ℤ)
    (hP : flat.{t, u} X (completedIntegralCommRingSheaf l E X D hl) P) :
    let R := completedIntegralCommRingSheafUnrestricted l E X
    let F := fun n : ℕ ↦ (strengthReductionRestricted l E X n).mapHomologicalComplex (.up ℤ)
    let T := totalTensor.{t, u} X R
    let A := (Functor.curry.obj a.tensor).obj (DerivedCategory.Q.obj P)
    ∃ e : (T.obj P) ⋙ DerivedCategory.Q ≅ DerivedCategory.Q ⋙ A,
      (∀ (Q : CochainComplex (scalarReductionSource l E X) ℤ)
          (_hQ : flat.{t, u} X R Q),
        e.hom.app Q = a.representative.hom.app (⟨P, hP⟩, ⟨Q, _hQ⟩)) ∧
      ∀ (n : ℕ) (m : ReductionPresentation l E X D hl a n)
          (Q : CochainComplex (scalarReductionSource l E X) ℤ)
          (_hQ : flat.{t, u} X R Q)
          (b :
            (T.obj P).obj ((F n).obj Q) ⟶ (F n).obj ((T.obj P).obj Q)),
        (∀ (i j : ℤ) (U : X.ProEtᵒᵖ)
            (s : (integralCoefficientCommRingSheaf l E X n).obj.obj U)
            (x : (P.X i).val.obj U) (y : (Q.X j).val.obj U),
          (b.f (i + j)).val.app U
              (totalPair.{t, u} X R P ((F n).obj Q) i j U x
                (strengthReductionTensor l E X n (Q.X j) U s y)) =
            strengthReductionTensor l E X n (((T.obj P).obj Q).X (i + j)) U s
              (totalPair.{t, u} X R P Q i j U x y)) →
          A.map (strengthReductionRepresentativeComparison l E X n Q) ≫
              e.inv.app ((F n).obj Q) ≫ DerivedCategory.Q.map b =
            (derivedScalarExtensionRestrictionAdjunction.{t, u} l E X n).choose.homEquiv _ _
              (m.mu.hom.app (DerivedCategory.Q.obj P,
                  (strengthDerivedReductionRestricted l E X n).obj (DerivedCategory.Q.obj Q)) ≫
                m.target.tensor.map
                  (Prod.mkHom (𝟙 ((scalarReductionDerivedExtension l E X n).obj
                    (DerivedCategory.Q.obj P)))
                    ((derivedScalarExtensionRestrictionAdjunction.{t, u}
                      l E X n).choose.counit.app
                        ((scalarReductionDerivedExtension l E X n).obj
                          (DerivedCategory.Q.obj Q)))) ≫
                m.mu.inv.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q)) ≫
              (strengthDerivedReductionRestricted l E X n).map (e.inv.app Q) ≫
              strengthReductionRepresentativeComparison l E X n ((T.obj P).obj Q) := by
  classical
  let : EssentiallySmall.{max u (t + 1)} X.ProEt := StrengthModel.fixedSmall X
  let : HasSheafify (Scheme.ProEt.topology X) AddCommGrpCat.{max u (t + 1)} :=
    StrengthModel.fixedSheafify X
  let : (Scheme.ProEt.topology X).WEqualsLocallyBijective AddCommGrpCat.{max u (t + 1)} :=
    StrengthModel.fixedLocallyBijective X
  let : HasDerivedCategory (scalarReductionSource.{t, u} l E X) :=
    HasDerivedCategory.standard _
  dsimp only
  let R := completedIntegralCommRingSheafUnrestricted l E X
  let q := @DerivedCategory.Q (scalarReductionSource.{t, u} l E X) _ _
    (HasDerivedCategory.standard _)
  let T := totalTensor.{t, u} X R
  let A := (Functor.curry.obj a.tensor).obj (q.obj P)
  let a₀ : TensorPresentation.{t, u} X R := a
  have hP₀ : flat.{t, u} X R P := hP
  have hh := StrengthModel.comparison_exists X R a₀ P hP₀
  obtain ⟨e, he⟩ := hh
  refine ⟨e, he, ?_⟩
  intro n m Q hQ b hb
  let : HasDerivedCategory (scalarReductionTarget.{t, u} l E X n) :=
    HasDerivedCategory.standard _
  let S := integralCoefficientCommRingSheaf l E X n
  let r := @DerivedCategory.Q (scalarReductionTarget.{t, u} l E X n) _ _
    (HasDerivedCategory.standard _)
  let F := (scalarReductionExtension l E X n).mapHomologicalComplex (.up ℤ)
  let U := (scalarReductionRestriction l E X n).mapHomologicalComplex (.up ℤ)
  let L := scalarReductionDerivedExtension l E X n
  let V := scalarReductionDerivedRestriction l E X n
  let adj := (derivedScalarExtensionRestrictionAdjunction l E X n).choose
  let adj₀ := (scalarReductionExtension_adjunction l E X n).choose.mapHomologicalComplex (.up ℤ)
  let c : q ⋙ L ⟶ F ⋙ r := StrengthDerived.reductionNat l E X D hl n
  let h := (scalarReductionRestriction l E X n).mapDerivedCategoryFactors
  let TP := T.obj P
  let T' := (totalTensor.{t, u} X S).obj (F.obj P)
  let G : CochainComplex (Modules.{t, u} X R) ℤ := U.obj (F.obj Q)
  have hres :=
    CochainComplex.exists_isKFlatResolutionIndependentCoefficients.{max u (t + 1), t + 1, t}
    (C := X.ProEt) (J := Scheme.ProEt.topology X) (R := R) G
  obtain ⟨Z, t, hZ, _, ht, _⟩ := hres
  have : IsIso (q.map t) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso (Modules.{t, u} X R) t).2 ht
  have hcP : IsIso (c.app P) := by
    simpa only [c, StrengthDerived.reductionNat_app] using
      (StrengthDerived.reductionCounit_isIso l E X D hl n P hP)
  have hcZ : IsIso (c.app Z) := by
    simpa only [c, StrengthDerived.reductionNat_app] using
      (StrengthDerived.reductionCounit_isIso l E X D hl n Z hZ)
  have hcQ : IsIso (c.app Q) := by
    simpa only [c, StrengthDerived.reductionNat_app] using
      (StrengthDerived.reductionCounit_isIso l E X D hl n Q hQ)
  let t' : F.obj Z ⟶ F.obj Q := (adj₀.homEquiv Z (F.obj Q)).symm t
  have hZ₀ : flat.{t, u} X (completedIntegralCommRingSheaf l E X D hl) Z := hZ
  have normZ := m.normalization P Z hP hZ₀
  obtain ⟨hFP, hFZ, betaZ₀, hiZ₀, hbZ, hnZ⟩ := normZ
  obtain ⟨hFP', hFQ, betaQ₀, hiQ₀, hbQ, hnQ⟩ := m.normalization P Q hP hQ
  let betaZ : T'.obj (F.obj Z) ⟶ F.obj (TP.obj Z) := betaZ₀
  let betaQ : T'.obj (F.obj Q) ⟶ F.obj (TP.obj Q) := betaQ₀
  have hiZ : IsIso betaZ := hiZ₀
  have hiQ : IsIso betaQ := hiQ₀
  let ψ := inv betaZ ≫ T'.map t' ≫ betaQ
  have ho : adj₀.homEquiv _ _ ψ = TP.map t ≫ b := by
    apply StrengthOrdinary.ordinary_square X l E n P Q Z t betaZ betaQ b
    · intro i j W x z
      have hh := hbZ i j W x z
      dsimp only [reductionUnit] at hh
      erw [(scalarReductionExtension_adjunction l E X n).choose_spec,
        (scalarReductionExtension_adjunction l E X n).choose_spec,
        (scalarReductionExtension_adjunction l E X n).choose_spec] at hh
      exact hh
    · intro i j W x y
      have hh := hbQ i j W x y
      dsimp only [reductionUnit] at hh
      erw [(scalarReductionExtension_adjunction l E X n).choose_spec,
        (scalarReductionExtension_adjunction l E X n).choose_spec,
        (scalarReductionExtension_adjunction l E X n).choose_spec] at hh
      exact hh
    · exact hb
  let repZ := m.target.representative.app (⟨F.obj P, hFP⟩, ⟨F.obj Z, hFZ⟩)
  let repQ := m.target.representative.app (⟨F.obj P, hFP'⟩, ⟨F.obj Q, hFQ⟩)
  let eZ := L.mapIso (e.app Z) ≪≫ m.mu.app (q.obj P, q.obj Z)
  let eQ := L.mapIso (e.app Q) ≪≫ m.mu.app (q.obj P, q.obj Q)
  let dZ := (r.mapIso (asIso betaZ)).symm ≪≫ repZ
  let dQ := (r.mapIso (asIso betaQ)).symm ≪≫ repQ
  have hNZ : eZ.hom ≫ m.target.tensor.map
      (Prod.mkHom (c.app P) (c.app Z)) = c.app (TP.obj Z) ≫ dZ.hom := by
    have hs := hnZ
    change L.map (a.representative.hom.app (⟨P, hP⟩, ⟨Z, hZ⟩)) ≫
      m.mu.hom.app (q.obj P, q.obj Z) ≫
      m.target.tensor.map (Prod.mkHom (reductionCounit l E X D hl n P)
        (reductionCounit l E X D hl n Z)) ≫ repZ.inv ≫ r.map betaZ =
      reductionCounit l E X D hl n (TP.obj Z) at hs
    rw [← he Z hZ] at hs
    have hh := congrArg (fun k ↦ k ≫ r.map (inv betaZ) ≫ repZ.hom) hs
    simp only [Category.assoc, ← r.map_comp_assoc, IsIso.hom_inv_id,
      r.map_id, Category.id_comp, Iso.inv_hom_id, Category.comp_id] at hh
    simpa only [eZ, dZ, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom,
      Functor.mapIso_inv, asIso_inv, Category.assoc, Iso.app_hom,
      c, StrengthDerived.reductionNat_app] using hh
  have hNQ : eQ.hom ≫ m.target.tensor.map
      (Prod.mkHom (c.app P) (c.app Q)) = c.app (TP.obj Q) ≫ dQ.hom := by
    have hs := hnQ
    change L.map (a.representative.hom.app (⟨P, hP⟩, ⟨Q, hQ⟩)) ≫
      m.mu.hom.app (q.obj P, q.obj Q) ≫
      m.target.tensor.map (Prod.mkHom (reductionCounit l E X D hl n P)
        (reductionCounit l E X D hl n Q)) ≫ repQ.inv ≫ r.map betaQ =
      reductionCounit l E X D hl n (TP.obj Q) at hs
    rw [← he Q hQ] at hs
    have hh := congrArg (fun k ↦ k ≫ r.map (inv betaQ) ≫ repQ.hom) hs
    simp only [Category.assoc, ← r.map_comp_assoc, IsIso.hom_inv_id,
      r.map_id, Category.id_comp, Iso.inv_hom_id, Category.comp_id] at hh
    simpa only [eQ, dQ, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom,
      Functor.mapIso_inv, asIso_inv, Category.assoc, Iso.app_hom,
      c, StrengthDerived.reductionNat_app] using hh
  have hr := m.target.representative.hom.naturality
    (X := (⟨F.obj P, hFP⟩, ⟨F.obj Z, hFZ⟩))
    (Y := (⟨F.obj P, hFP'⟩, ⟨F.obj Q, hFQ⟩)) (𝟙 _, ObjectProperty.homMk t')
  have hr' : repZ.hom ≫ m.target.tensor.map
      (Prod.mkHom (𝟙 (r.obj (F.obj P))) (r.map t')) =
        r.map (T'.map t') ≫ repQ.hom := by
    change r.map ((((totalTensor.{t, u} X S).map (𝟙 (F.obj P))).app (F.obj Z)) ≫
      T'.map t') ≫ repQ.hom = repZ.hom ≫
      m.target.tensor.map (Prod.mkHom (r.map (𝟙 (F.obj P))) (r.map t')) at hr
    erw [(totalTensor.{t, u} X S).map_id, NatTrans.id_app, Category.id_comp,
      r.map_id] at hr
    exact hr.symm
  have hμ := StrengthGenericMate.normalize_conjugate m.target.tensor eZ eQ
    (asIso (c.app P)) (asIso (c.app Z)) (asIso (c.app Q))
    dZ dQ (c.app (TP.obj Z)) (c.app (TP.obj Q)) (r.map t') hNZ hNQ
  have hμ' := hμ
  simp only [eZ, eQ, dZ, dQ, Iso.trans_hom, Iso.trans_inv,
    Functor.mapIso_hom, Functor.mapIso_inv, Iso.symm_hom, Iso.symm_inv,
    Iso.app_hom, Iso.app_inv, asIso_hom, asIso_inv, Category.assoc] at hμ'
  erw [reassoc_of% hr', Iso.hom_inv_id_assoc] at hμ'
  simp only [← r.map_comp] at hμ'
  have hf := StrengthGenericMate.transpose_iso_target q r F U adj₀ L V adj c h Z Q t'
    (StrengthDerived.unit_compatibility l E X D hl n Z hZ)
  have := strengthComparison_isIso l E X n Q hQ
  have hf' : adj.homEquiv _ _ (c.app Z ≫ r.map t' ≫ inv (c.app Q)) =
      q.map t ≫ (asIso (strengthReductionRepresentativeComparison l E X n Q)).inv := by
    have := strengthComparison_isIso l E X n Q hQ
    have hc : (V.mapIso (asIso (c.app Q)) ≪≫ h.app (F.obj Q)) =
        asIso (strengthReductionRepresentativeComparison l E X n Q) := by
      apply Iso.ext
      exact StrengthDerived.restrictionComparison_eq l E X D hl n Q
    have ht' : adj₀.homEquiv Z (F.obj Q) t' = t :=
      (adj₀.homEquiv Z (F.obj Q)).apply_symm_apply t
    rw [ht', hc] at hf
    exact hf
  have hTPZ : flat.{t, u} X R (TP.obj Z) :=
    coefficientTotalTensor_isKFlat.{u, t + 1, t} (Scheme.ProEt.topology X) R P Z hP hZ
  have hg := StrengthGenericMate.transpose_comparison q r F U adj₀ L V adj c h
    (TP.obj Z) (F.obj (TP.obj Q)) ψ
    (StrengthDerived.unit_compatibility l E X D hl n (TP.obj Z) hTPZ)
  have hg' : adj.homEquiv _ _ (c.app (TP.obj Z) ≫ r.map ψ) =
      q.map (TP.map t) ≫ q.map b ≫ h.inv.app (F.obj (TP.obj Q)) := by
    have hg₀ := hg
    erw [ho, q.map_comp] at hg₀
    apply (cancel_mono (h.hom.app (F.obj (TP.obj Q)))).1
    simp only [Category.assoc]
    erw [Iso.inv_hom_id_app, Category.comp_id]
    exact hg₀
  have hnat := e.hom.naturality t
  have hnat' : (e.app Z).hom ≫ a.tensor.map (Prod.mkHom (𝟙 (q.obj P)) (q.map t)) =
      q.map (TP.map t) ≫ (e.app (U.obj (F.obj Q))).hom := by
    exact hnat.symm
  have := strengthComparison_isIso l E X n Q hQ
  have hh := StrengthGenericMate.mate_paste a.tensor m.target.tensor L V adj m.mu
    (e.app Z) (e.app Q) (e.app (U.obj (F.obj Q)))
    (asIso (strengthReductionRepresentativeComparison l E X n Q)) (q.map t)
    (q.map (TP.map t)) (q.map b ≫ h.inv.app (F.obj (TP.obj Q)))
    (c.app (TP.obj Z)) (c.app (TP.obj Q))
    (c.app Z ≫ r.map t' ≫ inv (c.app Q)) (r.map ψ) hnat' hf' hμ' hg'
  have hh' := congrArg (fun k ↦ k ≫ h.hom.app (F.obj (TP.obj Q))) hh
  change a.tensor.map (Prod.mkHom (𝟙 (q.obj P))
      (strengthReductionRepresentativeComparison l E X n Q)) ≫
    (e.app (U.obj (F.obj Q))).inv ≫ q.map b =
    StrengthGenericMate.mate a.tensor m.target.tensor L V adj m.mu (q.obj P) (q.obj Q) ≫
      V.map (L.map (e.app Q).inv) ≫
      strengthReductionRepresentativeComparison l E X n (TP.obj Q)
  have hc : V.map (c.app (TP.obj Q)) ≫ h.hom.app (F.obj (TP.obj Q)) =
      strengthReductionRepresentativeComparison l E X n (TP.obj Q) := by
    simpa only [c, StrengthDerived.reductionNat_app] using
      (StrengthDerived.restrictionComparison_eq l E X D hl n (TP.obj Q))
  simp only [Category.assoc, Iso.inv_hom_id_app, asIso_hom] at hh'
  erw [Category.comp_id] at hh'
  rw [hc] at hh'
  exact hh'

end WeilConjectures.IntegralHom

namespace WeilConjectures.IntegralHom
open CategoryTheory.Limits

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (X : Scheme.{t}) (D : FiniteFieldDatum.{d}) (hl : l ≠ D.p)

set_option maxHeartbeats 16000000 in
-- Elaborating the normalized contraction retains independent coefficient universes.
/-- The normalized reduction tensor mate is invertible on K-flat representatives.
Source: Stacks 03CZ, 06YY, 07A4; integral Hom reduction, paragraphs 1--2.
Proof: extend the representative tensor comparison in its second argument by
K-flat localization. On complexes, tensor cancellation followed by the normalized
scalar tensor comparison is an isomorphism. Its local formula sends
x tensor (s tensor y) to s tensor (x tensor y). The scalar adjunction's normalized
unit identifies its localization with the tensor mate, after the invertible
representative comparisons. Cancel these isomorphisms.
(blueprint: lem-sf-reduction-tensor-strength-kflat-representative). -/
theorem scalarTensorStrength_on_kflat_representatives
    (a : TensorPresentation.{t, u} X (completedIntegralCommRingSheaf l E X D hl))
    (n : ℕ) (m : ReductionPresentation l E X D hl a n)
    (P Q : CochainComplex (scalarReductionSource l E X) ℤ)
    (hP : flat.{t, u} X (completedIntegralCommRingSheaf l E X D hl) P)
    (hQ : flat.{t, u} X (completedIntegralCommRingSheaf l E X D hl) Q) :
    IsIso ((derivedScalarExtensionRestrictionAdjunction l E X n).choose.homEquiv _ _
      (m.mu.hom.app (DerivedCategory.Q.obj P,
          (scalarReductionDerivedRestriction l E X n).obj
            ((scalarReductionDerivedExtension l E X n).obj (DerivedCategory.Q.obj Q))) ≫
        m.target.tensor.map
          (Prod.mkHom (𝟙 ((scalarReductionDerivedExtension l E X n).obj
            (DerivedCategory.Q.obj P)))
            ((derivedScalarExtensionRestrictionAdjunction l E X n).choose.counit.app
              ((scalarReductionDerivedExtension l E X n).obj (DerivedCategory.Q.obj Q)))) ≫
        m.mu.inv.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q))) := by
  classical
  let J := Scheme.ProEt.topology X
  let R := completedIntegralCommRingSheafUnrestricted l E X
  let S := integralCoefficientCommRingSheaf l E X n
  let : EssentiallySmall.{max u (t + 1)} X.ProEt := integralReductionSiteEssentiallySmall X
  let : HasSheafify J AddCommGrpCat.{max u (t + 1)} := integralCoefficientAbSheafify X
  let : J.WEqualsLocallyBijective AddCommGrpCat.{max u (t + 1)} :=
    integralCoefficientAbLocallyBijective X
  let E₀ := scalarReductionExtension l E X n
  let U₀ := scalarReductionRestriction l E X n
  let : E₀.Additive := scalarReductionExtensionAdditive l E X n
  let : PreservesFiniteLimits U₀ := scalarReductionRestrictionLimits l E X n
  let : PreservesFiniteColimits U₀ := scalarReductionRestrictionColimits l E X n
  let EC := E₀.mapHomologicalComplex (.up ℤ)
  let UC := U₀.mapHomologicalComplex (.up ℤ)
  let T := totalTensor.{t, u} X R
  let TS := totalTensor.{t, u} X S
  obtain ⟨hEP, hEQ, beta, hbeta, hsec, _⟩ := m.normalization P Q hP hQ
  have : IsIso beta := hbeta
  obtain ⟨bc, _, hbc⟩ := CategoryTheory.tensorComplexCancellation
    (completedIntegralCommRingProjectionUnrestricted l E X n) E₀
    (scalarReductionExistence l E X n).choose_spec.choose
    (scalarReductionExistence l E X n).choose_spec.choose_spec.choose
  let b : (T.obj P).obj (UC.obj (EC.obj Q)) ≅ UC.obj (EC.obj ((T.obj P).obj Q)) :=
    bc P (EC.obj Q) ≪≫ UC.mapIso (asIso beta)
  have hb (i j : ℤ) (V : X.ProEtᵒᵖ) (s : S.obj.obj V)
      (x : (P.X i).val.obj V) (y : (Q.X j).val.obj V) :
      (b.hom.f (i + j)).val.app V
        (totalPair.{t, u} X R P (UC.obj (EC.obj Q)) i j V x
          (strengthReductionTensor l E X n (Q.X j) V s y)) =
      strengthReductionTensor l E X n (((T.obj P).obj Q).X (i + j)) V s
        (totalPair.{t, u} X R P Q i j V x y) := by
    have hi := hbc P (EC.obj Q) i j V x 1
      (strengthReductionTensor l E X n (Q.X j) V s y)
    have hi' := congrArg (fun z ↦ ((bc P (EC.obj Q)).hom.f (i+j)).val.app V z) hi
    have hc (z) : ((bc P (EC.obj Q)).hom.f (i+j)).val.app V
        (((bc P (EC.obj Q)).inv.f (i+j)).val.app V z) = z :=
      ConcreteCategory.congr_hom
        (congrArg (fun f ↦ (f.f (i+j)).val.app V) (bc P (EC.obj Q)).inv_hom_id) z
    rw [hc] at hi'
    simp only [one_smul] at hi'
    change (beta.f (i+j)).val.app V
      (((bc P (EC.obj Q)).hom.f (i+j)).val.app V _) = _
    erw [← hi']
    apply StrengthOrdinary.beta_scalar X l E n P Q beta
    intro i j V x y
    have hh := hsec i j V x y
    dsimp only [reductionUnit] at hh
    erw [(scalarReductionExtension_adjunction l E X n).choose_spec,
      (scalarReductionExtension_adjunction l E X n).choose_spec,
      (scalarReductionExtension_adjunction l E X n).choose_spec] at hh
    exact hh
  obtain ⟨e, _, he⟩ := restrictionTensor_mate_model l E X D hl a P hP
  have hpq := he n m Q hQ b.hom hb
  have hTPQ : flat.{t, u} X R ((T.obj P).obj Q) :=
    coefficientTotalTensor_isKFlat.{u, t + 1, t} J R P Q hP hQ
  have := strengthComparison_isIso l E X n Q hQ
  have := strengthComparison_isIso l E X n ((T.obj P).obj Q) hTPQ
  have hleft : IsIso
      (((Functor.curry.obj a.tensor).obj (DerivedCategory.Q.obj P)).map
          (strengthReductionRepresentativeComparison l E X n Q) ≫
        e.inv.app (UC.obj (EC.obj Q)) ≫ DerivedCategory.Q.map b.hom) := by
    infer_instance
  erw [hpq] at hleft
  exact @IsIso.of_isIso_comp_right _ _ _ _ _ _
    ((strengthDerivedReductionRestricted l E X n).map (e.inv.app Q) ≫
      strengthReductionRepresentativeComparison l E X n ((T.obj P).obj Q))
    (by infer_instance) hleft

end WeilConjectures.IntegralHom
