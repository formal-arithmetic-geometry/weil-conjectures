/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.VectorTraceScalar.VectorTraceScalarDescent
import all WeilConjectures.AlgebraicGeometry.Etale.ProEtale.EtaleProEtaleScalarMate
import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula.Unit

/-! # Normalization of the transported scalar unit

Source: blueprint/latest, sec-smooth-purity/sk-prop-an,
cor-pur-vector-bundle-purity.proof.md, paragraph 2.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace AlgebraicGeometry.Etale.FiniteSmoothPurity
set_option linter.auxLemma false in
attribute [local instance 100000] DerivedCategoryModule._proof_1 DerivedCategoryModule._proof_2
set_option linter.auxLemma false in
attribute [local instance 100000]
  ordinaryFinitePullback._proof_1 ordinaryFinitePullback._proof_2
  ordinaryFinitePullback._proof_3 ordinaryFinitePullback._proof_4
  ordinaryFinitePullback._proof_5 ordinaryFinitePullback._proof_6
  ordinaryFinitePullback._proof_7 ordinaryFinitePullback._proof_8
  ordinaryFinitePullback._proof_9 ordinaryFinitePullback._proof_10
  ordinaryFinitePullback._proof_11 ordinaryFinitePullback._proof_12
  ordinaryFinitePullback._proof_13
attribute [local implicit_reducible] ordinaryFiniteSingleFunctor
attribute [local irreducible] HasDerivedCategory.ofIsGrothendieckAbelian
  HasDerivedCategory.ofHasKInjectiveResolutions
attribute [local instance] cachedEtaleGroth cachedEtaleSheafify
  cachedEtaleMonoidalPreadditive cachedEtaleCoproducts cachedEtaleColimits
  cachedEtaleFlatResolution cachedEtaleInjectiveResolution
  cachedEtaleExactColimits cachedEtaleTensor4 cachedEtaleTensor12
  cachedEtaleTensor23 cachedEtaleTensorColimits cachedEtaleTensorFlipColimits

open WeilConjectures.PurityFiniteSetting
open CategoryTheory.MonoidalCategory
attribute [local irreducible] Functor.leftAdjoint Functor.rightAdjoint
  Functor.leftDerivedFunctor Functor.rightDerivedFunctor Functor.mapDerivedCategory
  ProEtale.pbcFixedScalarExtension derivedTensor upperStar lowerStar

end AlgebraicGeometry.Etale.FiniteSmoothPurity

namespace AlgebraicGeometry.Etale.FiniteSmoothPurity

private theorem transport_unit_identity
    {C D : Type*} [Category C] [Category D] (Q : C ⥤ D)
    {U : C} {V : D} (e : U ≅ U) (f : V ≅ V) (m : Q.obj U ⟶ V)
    (he : e.inv = 𝟙 U) (hf : f.inv = 𝟙 V) :
    purityTransportUnitMap Q e.symm f.symm m = m := by
  have hh : e.hom = 𝟙 U := by
    have h := e.hom_inv_id
    rwa [he, Category.comp_id] at h
  dsimp only [purityTransportUnitMap, Iso.symm_inv, Iso.symm_hom]
  rw [hh, hf, Q.map_id, Category.id_comp, Category.comp_id]

private theorem unit_comparison_onSite
    (A B : Type*) [Category.{u + 1} A] [Category.{u + 1} B]
    [Abelian A] [Abelian B]
    [IsGrothendieckAbelian.{u + 1} A] [IsGrothendieckAbelian.{u + 1} B]
    [MonoidalCategory A] [MonoidalCategory B]
    [MonoidalPreadditive A] [MonoidalPreadditive B]
    [SymmetricCategory A] [SymmetricCategory B]
    [MonoidalClosed A] [MonoidalClosed B]
    [Abelian.HasFunctorialFlatResolution A] [Abelian.HasFunctorialFlatResolution B]
    (S : Scheme.{u})
    (Q : DerivedCategory (Sheaf S.smallEtaleTopology A) ⥤
      DerivedCategory (Sheaf S.smallEtaleTopology B))
    (m : Q.obj (𝟙_ _) ⟶ 𝟙_ _) :
    purityTransportUnitMap Q (singleFunctorObjUnitIso A S).symm
      (singleFunctorObjUnitIso B S).symm m = m := by
  exact transport_unit_identity Q (singleFunctorObjUnitIso A S)
    (singleFunctorObjUnitIso B S) m
    (singleFunctorObjUnitIso_inv A S) (singleFunctorObjUnitIso_inv B S)

/-- The single/unit identifications used in vector trace coefficients preserve the
multiplication-normalized scalar unit map.
Source: blueprint/latest, sec-smooth-purity/sk-prop-an/
cor-pur-vector-bundle-purity.proof.md, paragraph 2, the scalar unit at rank zero.
(blueprint: lem-sp-finite-scalar-unit-normalization).

Proof: each canonical single/unit isomorphism has identity inverse, by
singleFunctorObjUnitIso_inv. Its hom is therefore also the identity, by the inverse
identity. In purityTransportUnitMap the scalar image of this identity and the target
identity cancel, leaving ExceptionalCoefficients.unitIso.hom. The calculation is first
performed in arbitrary coefficient categories to avoid expanding the concrete derived
monoidal construction during kernel checking. It includes zero coefficient rings and
empty bases. -/
theorem finiteScalarUnit_normalization
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) (S : Scheme.{u}) :
    VectorTraceScalar.unit φ S = (ExceptionalCoefficients.unitIso φ S).hom := by
  exact unit_comparison_onSite (ModuleCat.{u + 1} A) (ModuleCat.{u + 1} B) S
    (scalarExtension φ S) (ExceptionalCoefficients.unitIso φ S).hom

end AlgebraicGeometry.Etale.FiniteSmoothPurity
