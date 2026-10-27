/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q1
-/
module

public import Sheaf.AlgebraicGeometry.OrdinarySupportedKummerScalar
import all Sheaf.AlgebraicGeometry.FiniteEtaleTateLinePullback
import Sheaf.AlgebraicGeometry.FiniteEtaleTateTensorFamily
import all Sheaf.AlgebraicGeometry.EtaleSupportedIntegralDerivedUnit
import Sheaf.CategoryTheory.FlatScalarUnit

/-! # The normalized derived coefficient unit on the ordinary Tate root line -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u uC vC wC uB vB wB
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale
set_option linter.auxLemma false in
attribute [local instance 100000] DerivedCategoryModule._proof_1 DerivedCategoryModule._proof_2
attribute [local instance 10000] SheafExactDegreeZero.scalarWeakSheafify
attribute [local instance 10000] cachedAbSheafify cachedModSheafify
open Scheme
attribute [local irreducible] HasDerivedCategory.ofIsGrothendieckAbelian
  DerivedCategory.singleFunctors Ext.homEquiv Ext.comp Ext.mk₀ Ext.mapExactFunctor

private noncomputable def boundaryScalarLineMap
    {R S : Type (u + 1)} [CommRing R] [CommRing S]
    (φ : R →+* S) (T : Scheme.{u}) (N : ℕ) (hR : (N : R) = 0) (hS : (N : S) = 0) :
    finiteEtaleTateLine T N R hR ⟶
      (Sheaf.restrictScalars T.smallEtaleTopology φ).obj (finiteEtaleTateLine T N S hS) :=
  (lineHomEquiv T N R hR _).symm (lineHomEquiv T N S hS _ (𝟙 _))

private theorem boundaryScalarLineMap_one
    {R S : Type (u + 1)} [CommRing R] [CommRing S]
    (φ : R →+* S) (T : Scheme.{u}) (N : ℕ) (hR : (N : R) = 0) (hS : (N : S) = 0)
    (W : T.Etaleᵒᵖ) (z : (T.rootsOfUnitySheaf N).obj.obj W) :
    (boundaryScalarLineMap φ T N hR hS).hom.app W
        (finiteEtaleTateOneGenerator R N T hR W 1 z) =
      finiteEtaleTateOneGenerator S N T hS W 1 z := by
  have h := Equiv.apply_symm_apply (lineHomEquiv T N R hR
    ((Sheaf.restrictScalars T.smallEtaleTopology φ).obj (finiteEtaleTateLine T N S hS)))
      (lineHomEquiv T N S hS _ (𝟙 _))
  have hh := congrArg (fun f ↦ f.hom.app W z) h
  exact (lineHomEquiv_generator T N R hR _
    (boundaryScalarLineMap φ T N hR hS) W z).symm.trans
      (hh.trans (lineHomEquiv_generator T N S hS _ (𝟙 _) W z))

private theorem boundaryScalarLineMap_apply
    {R S : Type (u + 1)} [CommRing R] [CommRing S]
    (φ : R →+* S) (T : Scheme.{u}) (N : ℕ) (hR : (N : R) = 0) (hS : (N : S) = 0)
    (W : T.Etaleᵒᵖ) (a : R) (z : (T.rootsOfUnitySheaf N).obj.obj W) :
    (boundaryScalarLineMap φ T N hR hS).hom.app W
        (finiteEtaleTateOneGenerator R N T hR W a z) =
      finiteEtaleTateOneGenerator S N T hS W (φ a) z := by
  rw [finiteEtaleGenerator_smul T N R hR W a z, map_smul,
    boundaryScalarLineMap_one]
  exact (finiteEtaleGenerator_smul T N S hS W (φ a) z).symm

private theorem boundaryScalarLineMap_universal
    {R S : Type (u + 1)} [CommRing R] [CommRing S]
    (φ : R →+* S) (T : Scheme.{u}) (N : ℕ) (hR : (N : R) = 0) (hS : (N : S) = 0)
    (H : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} S)) :
    Function.Bijective (fun f : finiteEtaleTateLine T N S hS ⟶ H ↦
      boundaryScalarLineMap φ T N hR hS ≫
        (Sheaf.restrictScalars T.smallEtaleTopology φ).map f) := by
  let eR := lineHomEquiv T N R hR
    ((Sheaf.restrictScalars T.smallEtaleTopology φ).obj H)
  let eS := lineHomEquiv T N S hS H
  have he (f : finiteEtaleTateLine T N S hS ⟶ H) :
      eR (boundaryScalarLineMap φ T N hR hS ≫
        (Sheaf.restrictScalars T.smallEtaleTopology φ).map f) = eS f := by
    ext W z
    have ha := lineHomEquiv_generator T N R hR _
      (boundaryScalarLineMap φ T N hR hS ≫
        (Sheaf.restrictScalars T.smallEtaleTopology φ).map f) W z
    have hb := lineHomEquiv_generator T N S hS H f W z
    exact ha.trans ((congrArg (fun x ↦ f.hom.app W x)
      (boundaryScalarLineMap_one φ T N hR hS W z)).trans hb.symm)
  constructor
  · intro f g h
    apply eS.injective
    exact (he f).symm.trans ((congrArg eR h).trans (he g))
  · intro f
    obtain ⟨g, hg⟩ := eS.surjective (eR f)
    exact ⟨g, eR.injective ((he g).trans hg)⟩

private theorem boundaryScalarLineMap_unit
    {R S : Type (u + 1)} [CommRing R] [CommRing S]
    (φ : R →+* S) (T : Scheme.{u}) (N : ℕ) (hN : 0 < N)
    (hR : (N : R) = 0) (hS : (N : S) = 0) (hT : IsUnit (N : Γ(T, ⊤))) :
    SupportedDerivedScalarUnit φ T (finiteEtaleTateLine T N R hR)
      (finiteEtaleTateLine T N S hS) (boundaryScalarLineMap φ T N hR hS) := by
  unfold SupportedDerivedScalarUnit
  exact SheafExactDegreeZero.scalarUniversal_of_flat T.smallEtaleTopology φ _ _ _
    (ObjectProperty.flat_of_tensorIso (finiteEtaleTateLineInverse T N hN R hR hT).rightIso)
    (boundaryScalarLineMap_universal φ T N hR hS)

/-- The coefficient map on the ordinary Tate root line, normalized on pure roots,
is an unbounded derived scalar unit, without flatness of the target coefficient ring.
Source: blueprint lem-amb-cartier-kummer-map, final scalar-extension paragraph;
Stacks 03PK and 07A6 (blueprint: lem-asd-supported-kummer-root-scalar-unit).

Proof: the root-line Hom equivalence constructs the coefficient map from the target
root generator. Its value at one and linearity give the displayed generator formula.
The same Hom equivalences give its ordinary scalar universal property. The source
line has a tensor inverse, hence is flat; the flat scalar-unit theorem upgrades the
ordinary universal property to the full unbounded derived one. -/
theorem supported_kummer_root_scalar_unit
    {R S : Type (u + 1)} [CommRing R] [CommRing S]
    (φ : R →+* S) (T : Scheme.{u}) (N : ℕ) (hN : 0 < N)
    (hR : (N : R) = 0) (hS : (N : S) = 0) (hT : IsUnit (N : Γ(T, ⊤))) :
    ∃ θ : finiteEtaleTateLine T N R hR ⟶
        (Sheaf.restrictScalars T.smallEtaleTopology φ).obj (finiteEtaleTateLine T N S hS),
      (∀ (W : T.Etaleᵒᵖ) (a : R) (z : (T.rootsOfUnitySheaf N).obj.obj W),
        θ.hom.app W (finiteEtaleTateOneGenerator R N T hR W a z) =
          finiteEtaleTateOneGenerator S N T hS W (φ a) z) ∧
      SupportedDerivedScalarUnit φ T (finiteEtaleTateLine T N R hR)
        (finiteEtaleTateLine T N S hS) θ := by
  exact ⟨boundaryScalarLineMap φ T N hR hS, boundaryScalarLineMap_apply φ T N hR hS,
    boundaryScalarLineMap_unit φ T N hN hR hS hT⟩

end AlgebraicGeometry.Etale
