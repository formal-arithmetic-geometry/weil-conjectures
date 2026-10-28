/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.FinitePerfectQuotientModelData
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import WeilConjectures.Algebra.Homology.ExtensionKFlatQuasiIso
import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
import WeilConjectures.CategoryTheory.Abelian.Flat.ModuleCat
import Mathlib.Algebra.Category.ModuleCat.Adjunctions
import Mathlib.Algebra.Category.ModuleCat.AB
import Sheaf.CategoryTheory.CommutativeSiteDerivedConstantModuleFunctor

/-! Transport of the algebraic representative through a coefficient equivalence.

Source: Stacks Project, sites-cohomology.tex, Tags 0D6D and 093J.
(blueprint: lem-weil-pbc-finite-model-derived-scalar-comparison-transport).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe t
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.ProEtale
namespace AlgebraicGeometry.Scheme
attribute [local instance] finitePerfectModelsAbLocallyBijective

/-- Exact constant realization transports derived isomorphisms.
Source: Stacks Tag 093J
(blueprint: lem-weil-pbc-finite-model-derived-scalar-comparison-transport). -/
theorem finiteModel_constantComplex_mapIso
    (X : Scheme.{t}) {D : Type t} [CommRing D]
    [(koszulConstantFunctor X D).PreservesZeroMorphisms]
    {A B : CochainComplex (ModuleCat.{t} D) ℤ}
    (e : DerivedCategory.Q.obj A ≅ DerivedCategory.Q.obj B) :
    Nonempty
      ((@DerivedCategory.Q (SheafOfModules.{t + 1} (adicModuleRing X D)) _ _).obj
          (finiteModelConstantComplex X D A) ≅
        (@DerivedCategory.Q (SheafOfModules.{t + 1} (adicModuleRing X D)) _ _).obj
          (finiteModelConstantComplex X D B)) := by
  have hconstant : (koszulConstantFunctor X D).Additive ∧
      PreservesFiniteLimits (koszulConstantFunctor X D) ∧
      PreservesFiniteColimits (koszulConstantFunctor X D) := by
    dsimp [koszulConstantFunctor]
    exact commutativeSiteConstantModuleFunctor_exact (ProEt.topology X) (ULift.{t + 1} D)
  have := hconstant.1
  have := hconstant.2.1
  have := hconstant.2.2
  have : (ModuleCat.restrictScalars.{t + 1}
      (ULift.ringEquiv : ULift.{t + 1} D ≃+* D).toRingHom).IsEquivalence :=
    (ModuleCat.restrictScalarsEquivalenceOfRingEquiv.{t + 1}
      (ULift.ringEquiv : ULift.{t + 1} D ≃+* D)).isEquivalence_functor
  have : PreservesLimits (ModuleCat.restrictScalars.{t + 1}
      (ULift.ringEquiv : ULift.{t + 1} D ≃+* D).toRingHom) :=
    Adjunction.isEquivalencePreservesLimits _
  have : PreservesColimits (ModuleCat.restrictScalars.{t + 1}
      (ULift.ringEquiv : ULift.{t + 1} D ≃+* D).toRingHom) :=
    Adjunction.isEquivalence_preservesColimits _
  let F := ModuleCat.uliftFunctor.{t + 1, t} D ⋙
    ModuleCat.restrictScalars.{t + 1}
      (ULift.ringEquiv : ULift.{t + 1} D ≃+* D).toRingHom ⋙
    koszulConstantFunctor X D
  exact ⟨(F.mapDerivedCategoryFactors.app A).symm ≪≫
    F.mapDerivedCategory.mapIso e ≪≫ F.mapDerivedCategoryFactors.app B⟩

private theorem finiteModel_hasFunctorialFlatResolution (R : Type t) [CommRing R] :
    Abelian.HasFunctorialFlatResolution (ModuleCat.{t} R) := by
  classical
  let F := ObjectProperty.lift ObjectProperty.flat
    (CategoryTheory.forget (ModuleCat.{t} R) ⋙ ModuleCat.free R) (fun M ↦ by
      apply (ModuleCat.flat_iff_flat _).2
      change Module.Flat R (M →₀ R)
      infer_instance)
  refine ⟨{ F := F, π := (ModuleCat.adj R).counit, epi_π_app := ?_ }⟩
  intro M
  apply (ModuleCat.epi_iff_surjective _).2
  intro x
  refine ⟨ModuleCat.freeMk x, ?_⟩
  change ModuleCat.freeDesc (𝟙 (CategoryTheory.forget (ModuleCat.{t} R)).obj M)
    (ModuleCat.freeMk x) = x
  simp only [ModuleCat.freeDesc_apply]
  rfl

/-- Every algebraic complex admits a K-flat representative in the same universe.
Source: Stacks Tag 06YF
(blueprint: lem-weil-pbc-finite-model-derived-scalar-comparison-transport).
Proof: the free-forgetful counit gives functorial flat resolutions, whose unbounded
complex resolution is K-flat and augmented by a quasi-isomorphism. -/
theorem finiteModel_exists_kFlat_representative (B : Type t) [CommRing B]
    (P : CochainComplex (ModuleCat.{t} B) ℤ) :
    ∃ R : CochainComplex (ModuleCat.{t} B) ℤ,
      (HomologicalComplex.quasiIso (ModuleCat.{t} B) (.up ℤ)).kFlat R ∧
        Nonempty (DerivedCategory.Q.obj R ≅ DerivedCategory.Q.obj P) := by
  classical
  have := finiteModel_hasFunctorialFlatResolution B
  have : AB5OfSize.{0, 0} (ModuleCat.{t} B) := AB5OfSize_of_univLE.{0, 0, t, t} _
  obtain ⟨R, f, hf, _, hR⟩ := P.exists_quasiIso_flat_kFlat
  have : QuasiIso f := hf
  exact ⟨R, hR, ⟨asIso (DerivedCategory.Q.map f)⟩⟩

/-- Coefficient equivalence transport identifies the scalar-extension model of a
K-flat complex with the canonical representative of its derived extension.
Source: Stacks Tags 0D6D, 06YY and 093J
(blueprint: lem-weil-pbc-finite-model-derived-scalar-comparison-transport).
Proof: the derived counit is invertible on a K-flat complex. Restriction along the
inverse equivalence is exact. Scalar-extension composition and uniqueness of left
adjoints identify it with extension along the composite. Finally apply exact
constant realization, which includes the prescribed universe lift. -/
theorem finiteModel_derivedRepresentative_transport
    (X : Scheme.{t}) {B C D : Type t} [CommRing B] [CommRing C] [CommRing D]
    (q : B →+* C) (ρ : C ≃+* D)
    [(koszulConstantFunctor X D).PreservesZeroMorphisms]
    (P : CochainComplex (ModuleCat.{t} B) ℤ)
    (hP : (HomologicalComplex.quasiIso (ModuleCat.{t} B) (.up ℤ)).kFlat P)
    (L : DerivedCategory (ModuleCat.{t} B) ⥤ DerivedCategory (ModuleCat.{t} C))
    (ε : DerivedCategory.Qh ⋙ L ⟶
      @Functor.mapHomotopyCategory _ _ _ _ _ _ _ (ModuleCat.extendScalars q)
        (ModuleCat.extendRestrictScalarsAdj q).left_adjoint_additive
        (.up ℤ) ⋙ DerivedCategory.Qh)
    (hL : L.IsLeftDerivedFunctor ε (HomotopyCategory.quasiIso _ (.up ℤ))) :
    let K := ((ModuleCat.restrictScalars.{t} ρ.symm.toRingHom).mapHomologicalComplex
      (.up ℤ)).obj (DerivedCategory.Q.objPreimage (L.obj (DerivedCategory.Q.obj P)))
    Nonempty
      ((@DerivedCategory.Q (SheafOfModules.{t + 1} (adicModuleRing X D)) _ _).obj
          (finiteModelConstantComplex X D
            (((ModuleCat.extendScalars (ρ.toRingHom.comp q)).mapHomologicalComplex
              (.up ℤ)).obj P)) ≅
        (@DerivedCategory.Q (SheafOfModules.{t + 1} (adicModuleRing X D)) _ _).obj
          (finiteModelConstantComplex X D K)) := by
  have : L.IsLeftDerivedFunctor ε (HomotopyCategory.quasiIso _ (.up ℤ)) := hL
  have := finiteModel_hasFunctorialFlatResolution B
  have : (ModuleCat.extendScalars q).Additive :=
    (ModuleCat.extendRestrictScalarsAdj q).left_adjoint_additive
  have := ModuleCat.extendScalars_preservesKFlatQuasiIso q
  have : AB5OfSize.{0, 0} (ModuleCat.{t} B) := AB5OfSize_of_univLE.{0, 0, t, t} _
  have hε := ((ModuleCat.extendScalars q).isLeftDerivedFunctor_iff_isIso_app_of_kFlat
    ε).1 hL P hP
  have : (ModuleCat.extendScalars (ρ.toRingHom.comp q)).Additive :=
    (ModuleCat.extendRestrictScalarsAdj (ρ.toRingHom.comp q)).left_adjoint_additive
  let F := ModuleCat.extendScalars q
  let G := ModuleCat.restrictScalars.{t} ρ.symm.toRingHom
  have : G.IsEquivalence := inferInstance
  have : PreservesLimits G := Adjunction.isEquivalencePreservesLimits _
  have : PreservesColimits G := Adjunction.isEquivalence_preservesColimits _
  let eρ : ModuleCat.extendScalars ρ.toRingHom ≅ G :=
    (ModuleCat.extendRestrictScalarsAdj ρ.toRingHom).leftAdjointUniq
      (ModuleCat.restrictScalarsEquivalenceOfRingEquiv ρ.symm).toAdjunction
  let ecomp : ModuleCat.extendScalars (ρ.toRingHom.comp q) ≅ F ⋙ G :=
    ModuleCat.extendScalarsComp q ρ.toRingHom ≪≫ Functor.isoWhiskerLeft F eρ
  let eε : L.obj (DerivedCategory.Q.obj P) ≅
      DerivedCategory.Q.obj ((F.mapHomologicalComplex (.up ℤ)).obj P) :=
    L.mapIso ((DerivedCategory.quotientCompQhIso _).app P).symm ≪≫
      asIso (ε.app ((HomotopyCategory.quotient _ _).obj P)) ≪≫
      DerivedCategory.Qh.mapIso ((F.mapHomotopyCategoryFactors (.up ℤ)).app P) ≪≫
      (DerivedCategory.quotientCompQhIso (ModuleCat.{t} C)).app
        ((F.mapHomologicalComplex (.up ℤ)).obj P)
  let T := DerivedCategory.Q.objPreimage (L.obj (DerivedCategory.Q.obj P))
  let eT : DerivedCategory.Q.obj T ≅
      DerivedCategory.Q.obj ((F.mapHomologicalComplex (.up ℤ)).obj P) :=
    DerivedCategory.Q.objObjPreimageIso _ ≪≫ eε
  apply finiteModel_constantComplex_mapIso X
  exact DerivedCategory.Q.mapIso
    ((Functor.mapHomologicalComplexCompIso ecomp.symm (.up ℤ)).symm.app P) ≪≫
    (G.mapDerivedCategoryFactors.app
      ((F.mapHomologicalComplex (.up ℤ)).obj P)).symm ≪≫
    G.mapDerivedCategory.mapIso eT.symm ≪≫ G.mapDerivedCategoryFactors.app T

end AlgebraicGeometry.Scheme
