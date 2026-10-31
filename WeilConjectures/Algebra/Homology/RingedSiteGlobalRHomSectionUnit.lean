/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.RingedSiteGlobalRHomModel
import all WeilConjectures.Algebra.Homology.DerivedInternalHomSectionsModel
import all WeilConjectures.Algebra.Homology.HomComplexGlobalHomotopyOfUniverses
import WeilConjectures.Algebra.Homology.KInjectiveHomComplexOfUniverses
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
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
import WeilConjectures.CategoryTheory.RingedSiteModules
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
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.ShortExactPullback


/-! Invertibility of the derived-section unit on Hom into K-injective complexes. -/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe c v r a w z

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory.RingedSiteGlobalRHom

variable {C : Type c} [Category.{v} C] {J : GrothendieckTopology C}
  (R : Sheaf J CommRingCat.{max c v r})
  [HasSheafify J AddCommGrpCat.{max c v r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
  [HasDerivedCategory.{w} (Modules.{c, v, max c v r} R)]
  (A : Type a) [CommRing A] (φ : A →+* Scalars.{c, v, max c v r} R)
  [HasDerivedCategory.{z} (ModuleCat.{max c v r} A)]

attribute [local irreducible] homComplexFunctor derivedInternalHomOfUniverses
  Functor.rightDerivedFunctor Functor.rightDerivedFunctorUnit

private theorem reflects_quasiIso
    {D B : Type*} [Category* D] [Category* B] [Abelian D] [Abelian B]
    (F : D ⥤ B) [F.Additive] [F.PreservesHomology] [F.ReflectsIsomorphisms]
    {K T : CochainComplex D ℤ} (f : K ⟶ T)
    [QuasiIso ((F.mapHomologicalComplex (.up ℤ)).map f)] : QuasiIso f := by
  constructor
  intro n
  rw [quasiIsoAt_iff]
  apply (ShortComplex.quasiIso_map_iff_of_preservesLeftHomology
    F ((HomologicalComplex.shortComplexFunctor D (.up ℤ) n).map f)).mp
  exact (quasiIsoAt_iff ((F.mapHomologicalComplex (.up ℤ)).map f) n).mp inferInstance

private def forgetSectionsIso :
    (sections.{c, v, max c v r} R A φ).mapHomologicalComplex (.up ℤ) ⋙
      (forget₂ (ModuleCat.{max c v r} A) AddCommGrpCat.{max c v r}).mapHomologicalComplex
        (.up ℤ) ≅
    (preadditiveCoyoneda.obj (op (SheafOfModules.unit
      ((sheafCompose J
        (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)))).mapHomologicalComplex
        (.up ℤ) :=
  Functor.mapHomologicalComplexCompIso
    (NatIso.ofComponents (fun _ ↦ Iso.refl _) (by intros; rfl)) (.up ℤ)

attribute [local irreducible] forgetSectionsIso

omit [HasDerivedCategory.{z} (ModuleCat.{max c v r} A)] in
private theorem section_precomp_quasiIso
    {L P I : CochainComplex (Modules.{c, v, max c v r} R) ℤ}
    (p : P ⟶ L) [QuasiIso p] [I.IsKInjective] :
    QuasiIso (((sections.{c, v, max c v r} R A φ).mapHomologicalComplex (.up ℤ)).map
      (((homComplexFunctor (R := R)).map p.op).app I)) := by
  let F := forget₂ (ModuleCat.{max c v r} A) AddCommGrpCat.{max c v r}
  have h := DerivedInternalHomSectionsModel.globalMap_quasiIso.{c, v, r, w} (I := I) R p
  let e := forgetSectionsIso.{c, v, r, a} R A φ
  let f := ((homComplexFunctor (R := R)).map p.op).app I
  have hn := e.hom.naturality f
  dsimp only [Functor.comp_map] at hn
  have : QuasiIso (((preadditiveCoyoneda.obj (op (SheafOfModules.unit
      ((sheafCompose J
        (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)))).mapHomologicalComplex
      (.up ℤ)).map f) := by
    simpa only [globalBifunctor, Functor.comp_map, Functor.uncurry_obj_map,
      Functor.map_id, Category.comp_id] using h
  have : QuasiIso ((F.mapHomologicalComplex (.up ℤ)).map
      (((sections.{c, v, max c v r} R A φ).mapHomologicalComplex (.up ℤ)).map f)) := by
    apply (quasiIso_iff_comp_right _ (e.hom.app _)).mp
    rw [hn]
    infer_instance
  exact reflects_quasiIso F _

/-- Derived sections need no further resolution on a Hom complex with K-injective target.
Source: Stacks Project, Tags 0A96 and 08JA.
(blueprint: lem-sfb-global-rhom-section-unit).

Proof: take a K-flat resolution of the source. Its Hom into the target is
K-injective, so the derived unit there is invertible. Precomposition is a
quasi-isomorphism on both sheaf Hom and ordinary global Hom; forgetting the
coefficient action reflects quasi-isomorphisms. The naturality square for the
derived unit then makes its fourth side invertible. -/
theorem sections_unit_hom_isIso
    (L I : CochainComplex (Modules.{c, v, max c v r} R) ℤ) [I.IsKInjective] :
    letI : IsGrothendieckAbelian.{max c v r} (Modules.{c, v, max c v r} R) :=
      (SheafOfModules.grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses.{c, v, r}
        J R).1
    IsIso ((sections.{c, v, max c v r} R A φ).rightDerivedFunctorUnitQ
      (homComplex (R := R) L I)) := by
  let : IsGrothendieckAbelian.{max c v r} (Modules.{c, v, max c v r} R) :=
    (SheafOfModules.grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses.{c, v, r}
      J R).1
  obtain ⟨P, p, hP, _, hp, _⟩ :=
    CochainComplex.exists_isKFlatResolutionIndependentCoefficients L
  have : QuasiIso p := hp
  have : (homComplex (R := R) P I).IsKInjective :=
    CochainComplex.isKInjective_homComplex_of_isKFlatOfUniverses.{r, c, v} P I hP
  let f := ((homComplexFunctor (R := R)).map p.op).app I
  have : QuasiIso f := by
    simpa only [Functor.map_id, Category.comp_id] using
      quasiIso_homComplex_mapOfUniverses.{c, v, r} (𝟙 I) p
  have : QuasiIso (((sections.{c, v, max c v r} R A φ).mapHomologicalComplex (.up ℤ)).map f) :=
    section_precomp_quasiIso.{c, v, r, a, w} R A φ p
  have : IsIso ((sections.{c, v, max c v r} R A φ).rightDerivedFunctorUnitQ
      (homComplex (R := R) P I)) := by
    rw [Functor.rightDerivedFunctorUnitQ_eq]
    infer_instance
  have hn := (sections.{c, v, max c v r} R A φ).rightDerivedFunctorUnitQ_naturality f
  change DerivedCategory.Q.map _ ≫
      (sections.{c, v, max c v r} R A φ).rightDerivedFunctorUnitQ (homComplex (R := R) P I) =
    (sections.{c, v, max c v r} R A φ).rightDerivedFunctorUnitQ (homComplex (R := R) L I) ≫
      (sections.{c, v, max c v r} R A φ).rightDerivedFunctor.map (DerivedCategory.Q.map f) at hn
  have : IsIso ((sections.{c, v, max c v r} R A φ).rightDerivedFunctorUnitQ
      (homComplex (R := R) L I) ≫
      (sections.{c, v, max c v r} R A φ).rightDerivedFunctor.map (DerivedCategory.Q.map f)) := by
    rw [← hn]
    infer_instance
  exact IsIso.of_isIso_comp_right _
    ((sections.{c, v, max c v r} R A φ).rightDerivedFunctor.map (DerivedCategory.Q.map f))


end CategoryTheory.RingedSiteGlobalRHom
