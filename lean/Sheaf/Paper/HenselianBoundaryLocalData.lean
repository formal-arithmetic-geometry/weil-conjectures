/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q29
-/
module

public import WeilConjectures.EtaleCohomology.Purity.RealSheaves.Boundary
public import Sheaf.Paper.RealBoundaryDecompositionLanding

/-! # Henselian local fields and the boundary decomposition path

Source: blueprint main-20261015, sec-purity-real-sheaves/sk-d-real-boundary,
d-real-boundary, displayed inertia kernel and decomposition homomorphism;
Stacks Project, Tag 0BSW (blueprint: d-real-boundary).

This supplements the recorded BoundaryDatum interface with the actual henselization,
residue action and geometric path. No kernel-generation property is assumed.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.FiniteEtale

namespace AlgebraicGeometry.Scheme.FiniteEtale

/-- Local presentation of the objects in the boundary inertia definition.
Source: d-real-boundary, the henselization, residue kernel and arbitrary path clauses;
Stacks Project, Tag 0BSW (blueprint: d-real-boundary).

All rings, fields and maps are supplied with their defining properties. In particular,
`residueAction` is specified by reduction on every integral element, and `decomposition`
is specified on every finite etale fibre after transport along `path`. Thus neither
homomorphism is arbitrary. The residue closure is the residue of the integral closure
of the henselization in the chosen algebraic closure, as in the recorded landing theorem.
The residue field of the henselization is identified with the stalk residue by its
universal property; no independent residue embedding is selected here.
-/
structure HenselianBoundaryLocalData {C U : Scheme.{u}} (j : U ⟶ C)
    {Ωb : Type u} [Field Ωb] [IsSepClosed Ωb] (b : Spec (.of Ωb) ⟶ U) (x : C) where
  H : Type u
  [commRingH : CommRing H]
  [henselianH : HenselianLocalRing H]
  [domainH : IsDomain H]
  [localizationAlgebra :
    Algebra (Localization.AtPrime (IsLocalRing.maximalIdeal (C.presheaf.stalk x))) H]
  [stalkAlgebraH : Algebra (C.presheaf.stalk x) H]
  [localizationTower : IsScalarTower (C.presheaf.stalk x)
    (Localization.AtPrime (IsLocalRing.maximalIdeal (C.presheaf.stalk x))) H]
  isHenselization : Algebra.IsHenselizationAtPrime' (C.presheaf.stalk x)
    (IsLocalRing.maximalIdeal (C.presheaf.stalk x)) H
  K : Type u
  [fieldK : Field K]
  [algebraHK : Algebra H K]
  [fractionK : IsFractionRing H K]
  [stalkAlgebraK : Algebra (C.presheaf.stalk x) K]
  [stalkTower : IsScalarTower (C.presheaf.stalk x) H K]
  Ω : Type u
  [fieldΩ : Field Ω]
  [algebraKΩ : Algebra K Ω]
  [closureΩ : IsAlgClosure K Ω]
  [algClosedΩ : IsAlgClosed Ω]
  [algebraHΩ : Algebra H Ω]
  [closureTower : IsScalarTower H K Ω]
  [localClosure : IsLocalRing (integralClosure H Ω)]
  [localInclusion : IsLocalHom (algebraMap H (integralClosure H Ω))]
  [residueClosure : IsAlgClosure (IsLocalRing.ResidueField H)
    (IsLocalRing.ResidueField (integralClosure H Ω))]
  integralAction : (Ω ≃ₐ[K] Ω) →* (integralClosure H Ω ≃ₐ[H] integralClosure H Ω)
  integralAction_spec : ∀ (σ : Ω ≃ₐ[K] Ω) (z : integralClosure H Ω),
    (integralAction σ z : Ω) = σ (z : Ω)
  residueAction : (Ω ≃ₐ[K] Ω) →*
    (IsLocalRing.ResidueField (integralClosure H Ω) ≃ₐ[IsLocalRing.ResidueField H]
      IsLocalRing.ResidueField (integralClosure H Ω))
  residueAction_spec : ∀ (σ : Ω ≃ₐ[K] Ω) (z : integralClosure H Ω),
    residueAction σ (IsLocalRing.residue (integralClosure H Ω) z) =
      IsLocalRing.residue (integralClosure H Ω) (integralAction σ z)
  localGenericPoint : Spec (.of K) ⟶ U
  localGenericPoint_spec : localGenericPoint ≫ j =
    Spec.map (CommRingCat.ofHom (algebraMap (C.presheaf.stalk x) K)) ≫ C.fromSpecStalk x
  path : fiber (Spec.map (CommRingCat.ofHom (algebraMap K Ω)) ≫ localGenericPoint) ≅ fiber b
  decomposition : (Ω ≃ₐ[K] Ω) →* Aut (fiber b)
  decomposition_spec : ∀ (σ : Ω ≃ₐ[K] Ω) (P : U.FiniteEtale)
      (z : (fiber (Spec.map (CommRingCat.ofHom (algebraMap K Ω)) ≫ localGenericPoint)).obj P),
    (path.inv.app P ((decomposition σ).hom.app P (path.hom.app P z))).left =
      Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ z.left

attribute [instance] HenselianBoundaryLocalData.commRingH HenselianBoundaryLocalData.henselianH
  HenselianBoundaryLocalData.domainH HenselianBoundaryLocalData.localizationAlgebra
  HenselianBoundaryLocalData.stalkAlgebraH HenselianBoundaryLocalData.localizationTower
  HenselianBoundaryLocalData.fieldK HenselianBoundaryLocalData.algebraHK
  HenselianBoundaryLocalData.fractionK HenselianBoundaryLocalData.stalkAlgebraK
  HenselianBoundaryLocalData.stalkTower HenselianBoundaryLocalData.fieldΩ
  HenselianBoundaryLocalData.algebraKΩ HenselianBoundaryLocalData.closureΩ
  HenselianBoundaryLocalData.algClosedΩ
  HenselianBoundaryLocalData.algebraHΩ HenselianBoundaryLocalData.closureTower
  HenselianBoundaryLocalData.localClosure HenselianBoundaryLocalData.localInclusion
  HenselianBoundaryLocalData.residueClosure

end AlgebraicGeometry.Scheme.FiniteEtale
