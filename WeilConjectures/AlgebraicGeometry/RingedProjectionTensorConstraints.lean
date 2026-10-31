/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.RingedProjectionCoherenceData
import WeilConjectures.Algebra.Homology.CochainTensorModelRigidity
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import WeilConjectures.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.CategoryTheory.Localization.Construction
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import Mathlib.CategoryTheory.Functor.Currying
import Mathlib.CategoryTheory.Whiskering
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.RingTheory.Flat.CategoryTheory
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.CategoryTheory.Localization.Prod
import Mathlib.Algebra.Homology.BifunctorFlip
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorHomotopy
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import Mathlib.Algebra.Homology.DerivedCategory.Fractions
import Mathlib.CategoryTheory.Localization.CalculusOfFractions
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.SiteTensorFunctorialitySupplement
import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import WeilConjectures.Algebra.Homology.DerivedTensorAdditiveConstraints
import WeilConjectures.AlgebraicGeometry.RingedProjectionAssociatorCompletion
import WeilConjectures.AlgebraicGeometry.RingedProjectionSymmetryCompletion

/-! Canonical tensor constraints for arbitrary recorded representative models.
(blueprint: lem-sfb-ringed-projection-tensor-constraints)
-/

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits MonoidalCategory
namespace SheafOfModules.ProjectionCoherence

attribute [local irreducible] SheafOfModules.monoidalCategory
  SheafOfModules.siteDerivedTensorIndependentCoefficients
  HomologicalComplex₂.total MorphismProperty.Q'
  SheafOfModules.KFlatFixedTensor.representativeIso

private theorem representativeArrow (X : RingedTensorCorner.{u, w})
    (P Q : CochainComplex X.mateModules ℤ)
    (hp : SheafOfModules.cochainTensorFlatRepresentatives X.topology X.ring P)
    (hq : SheafOfModules.cochainTensorFlatRepresentatives X.topology X.ring Q) :
    SheafOfModules.cochainTensorRepresentativeArrow X.topology X.ring (⟨P, hp⟩, ⟨Q, hq⟩) =
      (SheafOfModules.KFlatFixedTensor.representativeIso X.ring P Q
        hp.1 hq.1 hp.2 hq.2).hom := by
  unfold SheafOfModules.cochainTensorRepresentativeArrow
  change (𝟙 _) ≫ _ ≫ _ ≫
    (SheafOfModules.siteDerivedTensorIndependentCoefficients X.topology X.ring).map (𝟙 _) = _
  simp only [CategoryTheory.Functor.map_id, Category.comp_id, Category.id_comp]
  unfold SheafOfModules.KFlatFixedTensor.representativeIso
  rfl

set_option maxHeartbeats 800000 in
-- The representative comparison and normalized derived constraints require this budget.
/-- Every recorded representative presentation admits normalized tensor constraints.
Source: Stacks 06YS, 06YU and 07A4.
The proof identifies the recorded flat K-flat predicate with the independent-coefficient
one, extends the representative comparison to an isomorphism `e` from the fixed derived
tensor by `cochain_tensor_model_rigidity`, and conjugates the normalized derived
associator and Koszul symmetry of `existsUnique_derived_tensor_constraints` by `e`.
Naturality and the representative equations are
`ringedProjectionAssociatorCompletion` and `ringedProjectionSymmetryCompletion`.
(blueprint: lem-sfb-ringed-projection-tensor-constraints). -/
theorem ringedProjectionTensorConstraints :
    Nonempty (∀ (X : RingedTensorCorner.{u, w}) (a : RingedTensorModel X),
      TensorConstraints X a) := by
  refine ⟨fun X a => ?_⟩
  letI := SheafOfModules.monoidalCategory X.ring
  letI := SheafOfModules.cochainModulesPreadditive X.ring
  have hflat :
      (fun P : CochainComplex X.mateModules ℤ =>
        P.IsAcyclicTensorKFlat ∧ ∀ n : ℤ, (P.X n).IsFlat) =
      (fun P : CochainComplex X.mateModules ℤ =>
        P.IsKFlatIndependentCoefficients ∧
          ∀ n : ℤ, (P.X n).IsFlatOnSite) := by
    funext P
    apply propext
    constructor
    · rintro ⟨hk, hf⟩
      exact ⟨(CochainComplex.isKFlatIndependentCoefficients_iff_isKFlat P).2 hk,
        fun n => by
          exact (show (P.X n).IsFlat ↔ _ from by
            constructor
            · exact ObjectProperty.prop_of_iso (exactFunctor _ _)
                (siteSheafTensorRightIso X.ring (P.X n)).symm
            · exact ObjectProperty.prop_of_iso (exactFunctor _ _)
                (siteSheafTensorRightIso X.ring (P.X n))) |>.1 (hf n)⟩
    · rintro ⟨hk, hf⟩
      exact ⟨(CochainComplex.isKFlatIndependentCoefficients_iff_isKFlat P).1 hk,
        fun n => by
          exact (show (P.X n).IsFlat ↔ _ from by
            constructor
            · exact ObjectProperty.prop_of_iso (exactFunctor _ _)
                (siteSheafTensorRightIso X.ring (P.X n)).symm
            · exact ObjectProperty.prop_of_iso (exactFunctor _ _)
                (siteSheafTensorRightIso X.ring (P.X n))) |>.2 (hf n)⟩
  let arep := hflat ▸ a.representative
  let rr := SheafOfModules.cochain_tensor_model_rigidity.{u, u, u, w,
    max (u + 1) w + 1, max (u + 1) w} X.topology X.ring
  let r := rr.choose
  have hr := rr.choose_spec.1
  have hext := rr.choose_spec.2.1
  let ee := hext X.tensor arep
  let e := ee.choose
  have he := ee.choose_spec
  have hrep : let arep := hflat ▸ a.representative
      ∀ z : (SheafOfModules.cochainTensorFlatRepresentatives X.topology X.ring).FullSubcategory ×
        (SheafOfModules.cochainTensorFlatRepresentatives X.topology X.ring).FullSubcategory,
      SheafOfModules.cochainTensorRepresentativeArrow X.topology X.ring z ≫
        e.hom.app (DerivedCategory.Q.obj z.1.obj, DerivedCategory.Q.obj z.2.obj) =
      arep.hom.app z := by
    dsimp only
    intro z
    have h := congr_app he.1 z
    change r.hom.app z ≫ e.hom.app _ = arep.hom.app z at h
    rw [hr] at h
    exact h
  let ss := SheafOfModules.DerivedTensorConstraints.existsUnique_derived_tensor_constraints X.ring
  let s := ss.choose
  have hs := ss.choose_spec
  let α := s.2.1
  let σ := s.2.2
  let N := SheafOfModules.DerivedTensorConstraints.tensor X.ring
  let assoc (E F G : X.mateDerived) :
      X.tensor.obj (X.tensor.obj (E, F), G) ≅ X.tensor.obj (E, X.tensor.obj (F, G)) :=
    X.tensor.mapIso (Iso.prod (asIso (e.inv.app (E, F))) (Iso.refl G)) ≪≫
      asIso (e.inv.app (N.obj (E, F), G)) ≪≫ α.app ((E, F), G) ≪≫
      asIso (e.hom.app (E, N.obj (F, G))) ≪≫
      X.tensor.mapIso (Iso.prod (Iso.refl E) (asIso (e.hom.app (F, G))))
  let sym (E F : X.mateDerived) : X.tensor.obj (E, F) ≅ X.tensor.obj (F, E) :=
    asIso (e.inv.app (E, F)) ≪≫ σ.app (E, F) ≪≫ asIso (e.hom.app (F, E))
  obtain ⟨hAN, hAR⟩ := ringedProjectionAssociatorCompletion X a e hflat hrep s.1 α σ assoc (by
    intro E F G
    rfl) hs.1
  obtain ⟨hSN, hSR⟩ := ringedProjectionSymmetryCompletion X a e hflat hrep s.1 α σ sym (by
    intro E F
    rfl) hs.1
  exact {
    associator := assoc
    symmetry := sym
    associator_naturality := hAN
    symmetry_naturality := hSN
    associator_representative := hAR
    symmetry_representative := hSR }
end SheafOfModules.ProjectionCoherence
