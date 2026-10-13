/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Y2
-/
module

public import Sheaf.AlgebraicGeometry.PseudoCoherentComplex
public import Sheaf.RingTheory.RingPseudoCoherent
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.RingTheory.Localization.Away.Basic

import Sheaf.AlgebraicGeometry.AffinePseudoCoherentPrincipalModel
import Sheaf.AlgebraicGeometry.SchemeIsoDerivedEquivalence

/-! # Pointwise pseudo-coherent localization on an affine open

Source: Stacks Project, Tags 08EE and 08E7
(blueprint: lem-sc-affine-open-pseudo-coherent-localization-point).
-/

@[expose] public section

set_option autoImplicit false

universe u w wL

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry.Scheme

attribute [local instance] Functor.additive_of_preserves_binary_products
  comp_preservesFiniteLimits comp_preservesFiniteColimits

set_option backward.isDefEq.respectTransparency false in
/-- Pseudo-coherence of a fixed associated-sheaf complex on an open supplies a
pseudo-coherent localization near each point of that open.
Source: Stacks Project, Tags 08EE and 08E7, local-model step
(blueprint: lem-sc-affine-open-pseudo-coherent-localization-point).

Proof: At x use the finite-free neighbourhood model in the definition of
pseudo-coherence on U. Its image in X is an open neighbourhood W contained in U.
The affine principal-open basis gives f with x in D(f) contained in W.
Transport X and W along X.isoSpec, and transport the finite-free model along
this isomorphism and the equivalence of the open scheme with its localized site.
Exact restriction preserves the upper bound and every finite free term: its
comparison with the unit sheaf and preservation of coproducts give the same ranks.
The derived restriction composition comparison transports the model isomorphism.
Use hT to identify the transported complex with termwise tilde of M on Spec A.
Apply affine_pseudoCoherent_principal_model to W and D(f). This gives the
pseudo-coherence of Q(M_f). No compactness or global finite cover is used.
For empty U there is no point to consider; empty principal opens cause no issue,
since their rings are zero and the principal-model theorem includes the zero ring.
-/
theorem affine_open_pseudoCoherent_localization_point
    (X : Scheme.{u}) [IsAffine X] (U : X.Opens)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))]
    [∀ V : U.toScheme.Opens, HasDerivedCategory.{w}
      (SheafOfModules.{u} ((moduleRings U.toScheme.toRingedSpace).over V))]
    [∀ f : X.presheaf.obj (.op ⊤), HasDerivedCategory.{wL}
      (ModuleCat.{u} (Localization.Away f))]
    (T : ModuleCat.{u} (X.presheaf.obj (.op ⊤)) ⥤
      SheafOfModules.{u} (moduleRings X.toRingedSpace)) [T.PreservesZeroMorphisms]
    (hT : Nonempty (T ≅ tilde.functor (X.presheaf.obj (.op ⊤)) ⋙
      Modules.restrictFunctor X.isoSpec.hom))
    (M : CochainComplex (ModuleCat.{u} (X.presheaf.obj (.op ⊤))) ℤ)
    (hM : IsPseudoCoherent U.toScheme
      (((SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U) ⋙
        Equivalence.functor
          (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))
          (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
          (Modules.overEquiv U)).mapDerivedCategory.obj (DerivedCategory.Q.obj
        ((T.mapHomologicalComplex (ComplexShape.up ℤ)).obj M))))
    (x : X) (hx : x ∈ U) :
    ∃ f : X.presheaf.obj (.op ⊤), x ∈ X.basicOpen f ∧ X.basicOpen f ≤ U ∧
      DerivedCategory.IsPseudoCoherent
        (DerivedCategory.Q.obj ((Functor.mapHomologicalComplex
          (ModuleCat.extendScalars
            (algebraMap (X.presheaf.obj (.op ⊤)) (Localization.Away f)))
          (ComplexShape.up ℤ)).obj M)) := by sorry

end AlgebraicGeometry.Scheme
