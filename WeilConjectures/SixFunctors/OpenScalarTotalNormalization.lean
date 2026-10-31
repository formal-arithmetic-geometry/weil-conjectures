/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SixFunctors.OpenScalarOrdinaryMonoidal
import all WeilConjectures.AlgebraicGeometry.ProEtaleTotalTensorPullbackGenerators
public import WeilConjectures.Algebra.Homology.Monoidal.MapHomologicalComplex

/-! # Normalization of the ordinary pullback on total complexes

Source: Stacks Project, Tags 03EL, 06YN and 07A4.
(blueprint: lem-sp-open-scalar-total-normalization).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.Scheme SheafOfModules WeilConjectures
namespace AlgebraicGeometry.ProEtale.OpenScalarTensor
attribute [local instance 20000] instMonoidalCategoryHomologicalComplexIntUp_weilConjectures
  SheafOfModules.cochainModulesMonoidal
  SheafOfModules.cochainModulesSymmetric SheafOfModules.cochainModulesPreadditive

/-- The total tensorator induced by the ordinary monoidal pullback is the prescribed
signed total pullback comparison.
Source: Stacks Project, Tags 03EL, 06YN and 07A4
(blueprint: lem-sp-open-scalar-total-normalization).

Proof: compare the two chain maps degree by degree and precompose with every total
coproduct summand. The functorial total tensorator restricts on such a summand to
the ordinary oplax tensorator. Its assumed normalization identifies this with the
ordinary pullback comparison. The proved geometric total-summand formula identifies
the other chain map with exactly the same composite. Coproduct extensionality proves
equality, with no sign change since both maps preserve the bidegree. -/
theorem total_normalization {X Y : Scheme.{u}} (f : X ⟶ Y)
    (R : Sheaf (Scheme.ProEt.topology Y) CommRingCat.{u + 1})
    (S : Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1})
    (c : (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R ≅ S)
    (m : (proEtaleRingModulePullback f R S c).Monoidal)
    (hm : letI := m
      ∀ M N : proEtaleRingModules Y R,
        Functor.OplaxMonoidal.δ (proEtaleRingModulePullback f R S c) M N =
          (proEtaleOrdinaryTensorPullback f R S c M N).hom)
    (P Q : CochainComplex (proEtaleRingModules Y R) ℤ) :
    letI : (proEtaleRingModulePullback f R S c).IsLeftAdjoint :=
      (proEtaleRingModuleAdjunction f R S c).isLeftAdjoint
    letI := m
    (Functor.mapCochainComplexμIso (proEtaleRingModulePullback f R S c) P Q).inv =
      (proEtaleTensorPullbackTotalIso f R S c P Q).inv := by
  let := m
  let : (proEtaleRingModulePullback f R S c).IsLeftAdjoint :=
    (proEtaleRingModuleAdjunction f R S c).isLeftAdjoint
  let L := proEtaleRingModulePullback f R S c
  ext n : 1
  apply HomologicalComplex.mapBifunctor.hom_ext_of_map L
  intro p q hpq
  have h := geometric_total_ι f R S c P Q p q n hpq
  change L.map (HomologicalComplex.ιTensorObj P Q p q n hpq) ≫
      (proEtaleTensorPullbackTotalIso f R S c P Q).inv.f n =
    (proEtaleOrdinaryTensorPullback f R S c (P.X p) (Q.X q)).hom ≫
      HomologicalComplex.ιTensorObj
        ((L.mapHomologicalComplex (.up ℤ)).obj P)
        ((L.mapHomologicalComplex (.up ℤ)).obj Q) p q n hpq at h
  rw [← hm] at h
  simpa only [Functor.mapCochainComplexμIso_inv,
    Functor.OplaxMonoidal.mapHomologicalComplexδNatTrans_app_app,
    HomologicalComplex.mapBifunctorComparison_f,
    HomologicalComplex.map_ιMapBifunctor_mapBifunctorComparisonX,
    HomologicalComplex.mapBifunctorComparisonApp,
    Functor.OplaxMonoidal.δNatTrans_app_app] using h.symm

end AlgebraicGeometry.ProEtale.OpenScalarTensor
