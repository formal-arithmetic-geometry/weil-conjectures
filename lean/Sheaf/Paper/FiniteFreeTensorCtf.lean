/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group B4
-/
module

public import Sheaf.Paper.WitnessCompatibility
public import Sheaf.Paper.FiniteFreeScalarCalculusData
import Sheaf.Paper.FiniteFreeScalarTensorCalculus
import Sheaf.Paper.FiniteFreeScalarDerivedTensorModels
import WeilConjectures.SixFunctors.ProEtale.ScalarExtensionConstructible

/-! # Finite-free tensor preserves the finite constructible Tor domain

The argument uses exact scalar descent, so the scheme need not be Noetherian.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 128
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace AlgebraicGeometry

/-- Finite-free coefficient extension preserves bounded constructibility and finite
Tor amplitude on an arbitrary scheme.
Source: current blueprint det-prop-scalar-six-ctf, parts (2)--(3);
Stacks 03CZ, 06YY, 06YU and 05RT
(blueprint: lem-coef-finite-free-tensor-ctf).
Proof: exact scalar extension commutes with homology. Extending each finite constant
model on the same strata proves constructibility; exactness preserves both bounds.
The ordinary scalar/site square localizes, so an etale-origin witness extends to an
etale-origin witness. For a degree-zero B-module sheaf F, the tensor cancellation
isomorphism identifies the restriction of (K tensor_A B) tensor_B F with
K tensor_A Res(F). The original Tor interval kills its homology outside that
interval, and exact faithful restriction reflects this vanishing. Finally uniqueness
of left adjoints identifies exact descent with the specified derived tensor functor. -/
theorem finiteFreeTensorCtf (W : Scheme.{u})
    (A B : Type (u + 1)) [CommRing A] [CommRing B] [Finite A] [Finite B] [Algebra A B]
    (r : ℕ) (basis : Module.Basis (Fin r) A B)
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology W) (ModuleCat.{u + 1} A)))
    (hK : ProEtale.DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} A) W K) :
    ProEtale.DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} B) W
      ((ProEtale.pbcFixedScalarExtension (Scheme.ProEt.topology W)
        (algebraMap A B)).obj K) := by
  obtain ⟨s⟩ := finiteFreeScalarTensorCalculus W.smallEtaleTopology r basis
  obtain ⟨p⟩ := finiteFreeScalarTensorCalculus (Scheme.ProEt.topology W) r basis
  let := s.extension_limits
  let := s.extension_colimits
  let := p.extension_limits
  let := p.extension_colimits
  let := p.restriction_limits
  let := p.restriction_colimits
  obtain ⟨t⟩ := finiteFreeScalarDerivedTensorModels (Scheme.ProEt.topology W) r basis p
  let EA := finiteScalarExtension W.smallEtaleTopology (algebraMap A B)
  let EP := finiteScalarExtension (Scheme.ProEt.topology W) (algebraMap A B)
  let NA := ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) W
  let NB := ProEtale.comparisonUpperStar (ModuleCat.{u + 1} B) W
  have : PreservesFiniteLimits (EA ⋙ NB) := comp_preservesFiniteLimits _ _
  have : PreservesFiniteColimits (EA ⋙ NB) := comp_preservesFiniteColimits _ _
  have : PreservesFiniteLimits (NA ⋙ EP) := comp_preservesFiniteLimits _ _
  have : PreservesFiniteColimits (NA ⋙ EP) := comp_preservesFiniteColimits _ _
  let e₀ : EA ⋙ NB ≅ NA ⋙ EP :=
    ProEtale.etaleSheafExtendScalarsCompComparisonUpperStarIso (algebraMap A B) W
  let e : EA.mapDerivedCategory ⋙ NB.mapDerivedCategory ≅
      NA.mapDerivedCategory ⋙ EP.mapDerivedCategory :=
    (Functor.mapDerivedCategoryCompIso EA NB).symm ≪≫
      Functor.mapDerivedCategoryNatIso e₀ ≪≫ Functor.mapDerivedCategoryCompIso NA EP
  have hbc : ProEtale.DerivedCategory.boundedConstructible
      (ModuleCat.{u + 1} B) W (EP.mapDerivedCategory.obj K) := by
    obtain ⟨L, hL, ⟨i⟩⟩ := hK.1
    refine ⟨EA.mapDerivedCategory.obj L, ⟨EA.bounded_mapDerivedCategory_obj hL.1, ?_⟩,
      ⟨e.app L ≪≫ EP.mapDerivedCategory.mapIso i⟩⟩
    intro q
    have := hL.2 q
    have : Scheme.IsConstructibleSheaf
        ((DerivedCategory.homologyFunctor _ q ⋙ EA).obj L) :=
      ProEtale.isConstructibleSheaf_etaleSheafExtendScalars_obj (algebraMap A B)
        ((DerivedCategory.homologyFunctor _ q).obj L)
    exact Scheme.IsConstructibleSheaf.of_iso ((EA.mapDerivedCategoryHomologyFunctorIso q).app L)
  have hctf : ProEtale.DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} B) W
      (EP.mapDerivedCategory.obj K) := by
    refine ⟨hbc, ?_⟩
    obtain ⟨a, b, hab⟩ := hK.2
    refine ⟨a, b, ?_⟩
    intro F
    let U := Sheaf.restrictScalars (Scheme.ProEt.topology W) (algebraMap A B)
    apply U.homologyConcentratedIn_of_homologyConcentratedIn_mapDerivedCategory_obj
    let v := t.tensor_iso K ((DerivedCategory.singleFunctor _ 0).obj F) ≪≫
      whiskerLeftIso K ((U.mapDerivedCategorySingleFunctor 0).app F)
    exact (DerivedCategory.homologyConcentratedIn a b).prop_of_iso v.symm (hab (U.obj F))
  let ad := Adjunction.ofIsRightAdjoint
    (Sheaf.derivedRestrictScalars (Scheme.ProEt.topology W) (algebraMap A B))
  exact (ProEtale.DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} B) W).prop_of_iso
    ((p.adjunction.leftAdjointUniq ad).app K) hctf

end AlgebraicGeometry
