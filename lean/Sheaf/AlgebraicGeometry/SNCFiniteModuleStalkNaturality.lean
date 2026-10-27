/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q4
-/
module

public import Sheaf.AlgebraicGeometry.SNCFiniteFibreData
public import Mathlib.Algebra.Category.ModuleCat.AB

/-!
# Semilinear naturality of normalized finite module stalk actions

Source: ILO IX Proposition 2.1 and Bhatt--Scholze Section 5.1, finite-operation consequence
(blueprint: lem-sfb-snc-finite-module-stalk-naturality).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped FintypeCatDiscrete
namespace AlgebraicGeometry.ProEtale

/-- Normalized finite-label monodromy is linear and natural for semilinear sheaf maps.
The map on stalks is specified on every neighbourhood coprojection. No scalar-extension
functor or scalar comparison is assumed.
Source: ILO IX 2.1; Bhatt--Scholze Section 5.1, finite-module consequence
(blueprint: lem-sfb-snc-finite-module-stalk-naturality).

Proof: Forgetting module structure preserves the filtered stalk colimit. The normalized
finite labels therefore biject with the underlying module stalk. Addition and the zero,
negation and scalar maps are sheaf maps between finite tame objects: the binary product
is the underlying product because the inclusion preserves finite products. Naturality
of d.splitting for these maps identifies their fibre maps with the actual stalk operations.
The equivariance of d.fibre.map makes each root permutation additive and R-linear.
Transport along the label bijection to obtain the action on the actual stalk; its group
laws follow from those of d.fibre and its normalized formula is the definition of
SNCFiniteModuleStalkAction. Apply the same construction to N. The underlying set map of f
is a morphism between the two finite tame objects (restriction of scalars does not change
sets). Its fibre map is equivariant. The coprojection formula for t and normalization of
the two splittings identify this fibre map with t on every finite label. All elements of
the source stalk have such a label, so equality on labels proves the displayed equality.
This argument allows the zero ring and the zero module and uses no freeness assumption. -/
theorem sncFiniteModuleStalkAction_natural
    {p : ℕ} {Y : Scheme.{u}} {a : ℕ}
    {C : Fin a → Y.IdealSheafData} {I : Finset (Fin a)} (Q : SNCResidualChart p C I)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (z : Spec (.of Ω) ⟶ Q.puncturedTower)
    (d : SNCFiniteFibreClassification Q z)
    (R S : Type (u + 1)) [Ring R] [Ring S] (φ : R →+* S)
    (M : Sheaf (Scheme.ProEt.topology Q.puncturedResidual) (ModuleCat.{u + 1} R))
    (N : Sheaf (Scheme.ProEt.topology Q.puncturedResidual) (ModuleCat.{u + 1} S))
    (hM : Q.finiteTame ((sheafCompose (Scheme.ProEt.topology Q.puncturedResidual)
      (forget (ModuleCat.{u + 1} R))).obj M))
    (hN : Q.finiteTame ((sheafCompose (Scheme.ProEt.topology Q.puncturedResidual)
      (forget (ModuleCat.{u + 1} S))).obj N))
    (f : M ⟶ (sheafCompose (Scheme.ProEt.topology Q.puncturedResidual)
      (ModuleCat.restrictScalars.{u + 1} φ)).obj N)
    (t : Scheme.proEtaleGeometricStalk (z ≫ Q.towerMap) M ⟶
      (ModuleCat.restrictScalars.{u + 1} φ).obj (Scheme.proEtaleGeometricStalk (z ≫ Q.towerMap) N))
    (ht : ∀ V : Scheme.ProEtaleGeometricNeighbourhood (z ≫ Q.towerMap),
      colimit.ι (Scheme.proEtaleGeometricStalkDiagram (z ≫ Q.towerMap) M) (op V) ≫ t =
        f.hom.app (op V.right) ≫ (ModuleCat.restrictScalars.{u + 1} φ).map
          (colimit.ι (Scheme.proEtaleGeometricStalkDiagram (z ≫ Q.towerMap) N) (op V))) :
    ∃ (A : SNCFiniteModuleStalkAction d M hM) (B : SNCFiniteModuleStalkAction d N hN),
      ∀ g : SNCInertia.{u} p (Fintype.card I),
        A.action g ≫ t = t ≫ (ModuleCat.restrictScalars.{u + 1} φ).map (B.action g) := by
  sorry

end AlgebraicGeometry.ProEtale
