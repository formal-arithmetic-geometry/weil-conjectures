/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralVerdier.FiniteIntrinsicTensorRealization
public import WeilConjectures.SixFunctors.Finite.Scalar.Tensor.FiniteScalarTensorResolution
public import WeilConjectures.SixFunctors.Supporting.Tensor.TotalTensorBraiding
import all WeilConjectures.SixFunctors.IntegralHom.Reduction.IntegralHomReductionModels
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import all WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
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
import all WeilConjectures.Mathlib.Algebra.Homology.Monoidal
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import all Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import all WeilConjectures.Algebra.Homology.Ringed.RingedTensorComplexConstraintsSupplement
import all WeilConjectures.SixFunctors.Finite.Scalar.Tensor.FiniteScalarTensorComplex
import all WeilConjectures.SixFunctors.RationalVerdier.RationalVerdierSignedKFlat

/-! # Resolving representative part of finite intrinsic tensor symmetry

This is the flat-term K-flat representative calculation used by the intrinsic
symmetry theorem.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme MonoidalCategory
open CategoryTheory.Functor
-- Share the already proved coefficient-instance shortcuts used by the canonical map.
attribute [local instance 2000] isNoetherian_of_finite
attribute [local instance 10000] finiteProjection_groupW finiteProjection_groupSheafify
  finiteProjection_moduleSheafify finiteProjection_sheafGroth finiteProjection_functorLimits
  finiteProjection_functorColimits finiteProjection_inverseAdditive finiteProjection_inverseLimits
  finiteProjection_inverseColimits finiteProjection_moduleGroth finiteProjection_modulePreadditive
  finiteProjection_moduleFlat

attribute [local instance 10000] WeilConjectures.finiteScalarCountableColimits
  WeilConjectures.finiteScalarTensorTotal
  WeilConjectures.finiteScalarIntrinsicCountableColimits
  WeilConjectures.finiteScalarFunctorAdditive WeilConjectures.finiteScalarFunctorEquivalence
  WeilConjectures.finiteScalarFixedTensorPreadditive

-- Use the same inherited data as the native derived tensor and exact-functor APIs.
attribute [local instance 2000] SymmetricCategory.toBraidedCategory Abelian.toPreadditive
attribute [local instance 4000] Preadditive.preadditiveHasZeroMorphisms

-- Match the native additive data in the published complex tensor models.
attribute [local instance 30000] SheafOfModules.instPreadditive
  HomologicalComplex.instPreadditive CategoryTheory.functorCategoryPreadditive
  Preadditive.preadditiveHasZeroMorphisms Functor.preservesZeroMorphisms_of_additive

attribute [local irreducible] SheafOfModules.monoidalCategory
  AlgebraicGeometry.Scheme.proEtaleCanonicalTensorComparison
  AlgebraicGeometry.Scheme.proEtaleTensorPullbackTotalIso
  AlgebraicGeometry.Scheme.proEtaleTensorPullbackTotal
  AlgebraicGeometry.Scheme.proEtaleOrdinaryTensorPullback
  AlgebraicGeometry.Scheme.proEtaleRingModulePullback
attribute [local implicit_reducible] CategoryTheory.Functor.map₂HomologicalComplex
  CategoryTheory.Functor.mapHomologicalComplex

namespace WeilConjectures.IntegralVerdier

attribute [local implicit_reducible] DerivedCategory DerivedMonoidal instCategoryDerivedCategory
  instCategoryDerivedMonoidal toDerivedMonoidal

attribute [local irreducible] DerivedCategory.Q DerivedCategory.Qh
  CategoryTheory.Functor.mapDerivedCategory
  AlgebraicGeometry.Scheme.sfIntrinsicModuleEquivalence
attribute [local implicit_reducible] AlgebraicGeometry.Scheme.sfIntrinsicDerivedEquivalence
  CategoryTheory.Equivalence.mapDerivedCategory

attribute [local instance high] SymmetricCategory.toBraidedCategory
attribute [local instance 20000] ProEtale.sheafBraidedCategory

private theorem representative_swap_square
    {D : Type*} [Category D] {A B C E : D}
    (a : A ≅ B) (a' : C ≅ E) (v : A ⟶ C) (s : B ⟶ E)
    (h : a.inv ≫ v ≫ a'.hom = s) : a.hom ≫ s = v ≫ a'.hom := by
  rw [← h, ← Category.assoc, Iso.hom_inv_id, Category.id_comp]

attribute [local semireducible] totalTensorBraiding

/-- The native signed swap, with the intrinsic total tensor as its source and target.
Source: Stacks 06YL and 0FPQ.
(blueprint: lem-sf-signed-symmetry-native-representative). -/
@[irreducible] def intrinsicKoszulSwap
    (X : Scheme.{u}) (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (P Q : CochainComplex (IntegralHom.Modules.{u, u} X R) ℤ) :
    DerivedCategory.Q.obj
        ((finiteScalarRepresentativeTotalTensor (IntegralHom.Modules.{u, u} X R)).obj (P, Q)) ⟶
      DerivedCategory.Q.obj
        ((finiteScalarRepresentativeTotalTensor (IntegralHom.Modules.{u, u} X R)).obj (Q, P)) :=
  DerivedCategory.Q.map (totalTensorBraiding P Q).hom

attribute [local semireducible] intrinsicKoszulSwap

/-- The supplied representative, with the shared signed-total object as its source.
This is the existing representative isomorphism, with unchanged data.
Source: Stacks 06YL and 0FPT.
(blueprint: lem-sf-signed-symmetry-native-representative). -/
@[irreducible] def intrinsicRepresentative
    (X : Scheme.{u}) (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (a : IntegralHom.TensorPresentation.{u, u} X R)
    (P Q : CochainComplex (IntegralHom.Modules.{u, u} X R) ℤ)
    (hP : IntegralHom.flat.{u, u} X R P) (hQ : IntegralHom.flat.{u, u} X R Q) :
    DerivedCategory.Q.obj
        ((finiteScalarRepresentativeTotalTensor (IntegralHom.Modules.{u, u} X R)).obj (P, Q)) ≅
      a.tensor.obj (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) :=
  a.representative.app (⟨P, hP⟩, ⟨Q, hQ⟩)

attribute [local semireducible] intrinsicRepresentative

/-- A tensor generator in degree `k` is the transported total pair in degree `i + j`. -/
private theorem generator_transport (X : Scheme.{u})
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (P Q : CochainComplex (IntegralHom.Modules.{u, u} X R) ℤ)
    (i j k : ℤ) (h : i + j = k) (U : X.ProEtᵒᵖ)
    (x : (P.X i).val.obj U) (y : (Q.X j).val.obj U) :
    coefficientTensorGenerator.{u, u + 1, u} (ProEt.topology X) R P Q i j k h U x y =
      (eqToHom (congrArg
        (fun n : ℤ ↦ (((IntegralHom.totalTensor.{u, u} X R).obj P).obj Q).X n)
          h)).val.app U (IntegralHom.totalPair.{u, u} X R P Q i j U x y) := by
  subst k
  rfl

/-- A chain swap with the homogeneous Koszul formula is the native braiding.
Source: Stacks 0FPQ (blueprint: lem-sf-signed-symmetry-native-representative). -/
private theorem integralHomSignedNative
    (X : Scheme.{u}) (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (P Q : CochainComplex (IntegralHom.Modules.{u, u} X R) ℤ)
    (v : ((IntegralHom.totalTensor.{u, u} X R).obj P).obj Q ⟶
      ((IntegralHom.totalTensor.{u, u} X R).obj Q).obj P)
    (hv : ∀ (i j : ℤ) (U : X.ProEtᵒᵖ)
      (x : (P.X i).val.obj U) (y : (Q.X j).val.obj U),
      (v.f (i + j)).val.app U (IntegralHom.totalPair.{u, u} X R P Q i j U x y) =
        (i * j).negOnePow •
          (eqToHom (congrArg
            (fun k : ℤ ↦ (((IntegralHom.totalTensor.{u, u} X R).obj Q).obj P).X k)
              (add_comm j i))).val.app U
                (IntegralHom.totalPair.{u, u} X R Q P j i U y x)) :
    v = (totalTensorBraiding P Q).hom := by
  apply RationalVerdier.signed_chain_unique X R P Q
  intro i j U x y
  rw [hv i j U x y]
  have h := (RingedDerivedNative.complexConstraints.{u + 1, u, u}
    (ProEt.topology X) R).symmetry P Q i j (i + j) rfl (add_comm j i) U x y
  rw [← generator_transport X R Q P j i (i + j) (add_comm j i) U y x]
  exact h.symm

/-- A supplied signed symmetry agrees on K-flat representatives with native braiding.
Source: Stacks 06YL and 0FPT.
Proof: choose the representative supplied by the symmetry, identify its chain map
by its homogeneous pure-section formula, and cancel the representative isomorphism.
(blueprint: lem-sf-signed-symmetry-native-representative). -/
theorem signed_representative_native
    (X : Scheme.{u}) (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (a : IntegralHom.TensorPresentation.{u, u} X R) (s : SignedSymmetry X R a)
    (P Q : CochainComplex (IntegralHom.Modules.{u, u} X R) ℤ)
    (hP : IntegralHom.flat.{u, u} X R P) (hQ : IntegralHom.flat.{u, u} X R Q) :
    (intrinsicRepresentative X R a P Q hP hQ).hom ≫
        (s.swap (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj Q)).hom =
      intrinsicKoszulSwap X R P Q ≫
        (intrinsicRepresentative X R a Q P hQ hP).hom := by
  obtain ⟨v, hv, hsv⟩ := s.representative P Q hP hQ
  have hn := integralHomSignedNative X R P Q v hv
  have hs := representative_swap_square
    (a.representative.app (⟨P, hP⟩, ⟨Q, hQ⟩))
    (a.representative.app (⟨Q, hQ⟩, ⟨P, hP⟩))
    (DerivedCategory.Q.map v) _ hsv
  exact hs.trans (congrArg (fun z ↦ DerivedCategory.Q.map z ≫
    a.representative.hom.app (⟨Q, hQ⟩, ⟨P, hP⟩)) hn)

/-- The intrinsic signed representative equation on realized scalar complexes.
Source: Stacks 06YL and 0FPT.
Proof: scalar realization preserves the specified flat representatives. Apply the
native signed representative equation to their two realized K-flat complexes.
(blueprint: lem-sf-signed-symmetry-native-representative). -/
theorem finiteScalarSignedRepresentativeNative
    (X : Scheme.{u}) (B : Type u) [CommRing B] [Finite B]
    (a : IntegralHom.TensorPresentation.{u, u} X (proEtaleConstantRing X B))
    (s : SignedSymmetry X (proEtaleConstantRing X B) a)
    (P Q : CochainComplex
      (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} (ULift.{u + 1} B))) ℤ)
    (hP : finiteScalarFlatRepresentatives X B P)
    (hQ : finiteScalarFlatRepresentatives X B Q) :
    let : HasDerivedCategory.{u + 2}
      (proEtaleRingModules X (proEtaleConstantRing X B)) := HasDerivedCategory.standard _
    let U := (sfIntrinsicModuleEquivalence X B).functor.mapHomologicalComplex (.up ℤ)
    let hUP := (CochainComplex.isKFlatIndependentCoefficients_iff_isKFlat _).mpr
      (finiteScalarPreservesRepresentatives X B P hP).1
    let hUQ := (CochainComplex.isKFlatIndependentCoefficients_iff_isKFlat _).mpr
      (finiteScalarPreservesRepresentatives X B Q hQ).1
    (intrinsicRepresentative.{u} X (proEtaleConstantRing X B) a
        (U.obj P) (U.obj Q) hUP hUQ).hom ≫
        (s.swap (DerivedCategory.Q.obj (U.obj P)) (DerivedCategory.Q.obj (U.obj Q))).hom =
      intrinsicKoszulSwap X (proEtaleConstantRing X B) (U.obj P) (U.obj Q) ≫
        (intrinsicRepresentative.{u} X (proEtaleConstantRing X B) a
          (U.obj Q) (U.obj P) hUQ hUP).hom := by
  let : HasDerivedCategory.{u + 2}
      (proEtaleRingModules X (proEtaleConstantRing X B)) := HasDerivedCategory.standard _
  let U := (sfIntrinsicModuleEquivalence X B).functor.mapHomologicalComplex (.up ℤ)
  exact signed_representative_native X (proEtaleConstantRing X B) a s (U.obj P) (U.obj Q)
    ((CochainComplex.isKFlatIndependentCoefficients_iff_isKFlat _).mpr
      (finiteScalarPreservesRepresentatives X B P hP).1)
    ((CochainComplex.isKFlatIndependentCoefficients_iff_isKFlat _).mpr
      (finiteScalarPreservesRepresentatives X B Q hQ).1)

end WeilConjectures.IntegralVerdier
