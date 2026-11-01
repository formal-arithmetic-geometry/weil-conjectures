/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Finite.Scalar.FiniteScalarRepresentativeTensorIso

/-! # Reindexing a tensor representative equation

Source: Stacks Tags 06YN and 07A4.
(blueprint: lem-sf-finite-scalar-shared-representative-equation).
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
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

namespace WeilConjectures

attribute [local implicit_reducible] finiteScalarRepresentativeTotalTensor

/-- Rewrite a representative equation on the shared total tensor. The coefficient
category stays abstract, so the concrete scalar specialization does not repeat
conversions between the two signed-total complex definitions.
Source: Stacks Tags 06YN and 07A4.
(blueprint: lem-sf-finite-scalar-shared-representative-equation).

Proof: substitute the representative component equation and unfold the shared
signed total, uncurry, and the two definitions of the total complex. The two
propositions then coincide. -/
theorem finiteScalarSharedRepresentativeEquation
    (B : Type*) [Category.{u + 1} B] [Abelian B] [IsGrothendieckAbelian.{u + 1} B]
    [MonoidalCategory B] [MonoidalPreadditive B] [SymmetricCategory B] [MonoidalClosed B]
    [Abelian.HasFunctorialFlatResolution B] (T : Scheme.{u})
    (S : ObjectProperty (CochainComplex (Sheaf (ProEt.topology T) B) ℤ))
    (hS : ∀ Z, S Z → (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat Z)
    {H D : Type*} [Category H] [Category D]
    (U : CochainComplex (Sheaf (ProEt.topology T) B) ℤ ⥤ H)
    (q : H ⥤ D) (E : DerivedCategory (Sheaf (ProEt.topology T) B) ⥤ D)
    (e : DerivedCategory.Q ⋙ E ≅ U ⋙ q)
    (t : H × H ⥤ H) (tensor' : D × D ⥤ D)
    (P Q : CochainComplex (Sheaf (ProEt.topology T) B) ℤ) (hp : S P) (hq : S Q)
    (tau : E.obj (((ProEtale.derivedTensor B T).obj (DerivedCategory.Q.obj P)).obj
      (DerivedCategory.Q.obj Q)) ⟶
        tensor'.obj (E.obj (DerivedCategory.Q.obj P), E.obj (DerivedCategory.Q.obj Q)))
    (b : U.obj (CochainComplex.mapBifunctor P Q
      (curriedTensor (Sheaf (ProEt.topology T) B))) ⟶ t.obj (U.obj P, U.obj Q))
    (v : q.obj (t.obj (U.obj P, U.obj Q)) ⟶
      tensor'.obj (q.obj (U.obj P), q.obj (U.obj Q)))
    (h : E.map ((finiteScalarFixedTensorRepresentativeForCoefficients B T S hS).hom.app
          (⟨P, hp⟩, ⟨Q, hq⟩)) ≫ tau ≫
        tensor'.map (Prod.mkHom (e.hom.app P) (e.hom.app Q)) =
      e.hom.app (CochainComplex.mapBifunctor P Q
        (curriedTensor (Sheaf (ProEt.topology T) B))) ≫ q.map b ≫ v) :
    E.map ((finiteScalarRepresentativeTensorIso B T S hS).hom.app
          (⟨P, hp⟩, ⟨Q, hq⟩)) ≫ tau ≫
        tensor'.map (Prod.mkHom (e.hom.app P) (e.hom.app Q)) =
      e.hom.app ((finiteScalarRepresentativeTotalTensor
        (Sheaf (ProEt.topology T) B)).obj (P, Q)) ≫ q.map b ≫ v := by
  simpa only [finiteScalarRepresentativeTensorIso_hom_app,
    finiteScalarRepresentativeTotalTensor, uncurry_obj_obj,
    Functor.map₂HomologicalComplex, CochainComplex.mapBifunctor] using h

end WeilConjectures
