/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.BaseChangeConventions
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.RingTheory.Localization.FractionRing

/-!
# Néron locally finite type models of group schemes

Source: Bosch--Lütkebohmert--Raynaud, Néron Models, 10.1 Definition 1, printed p.289,
and 1.2 Definition 1, printed p.12 (blueprint: def-sfb-neron-lft-model).

The generic-fibre identification is an isomorphism of group schemes. The mapping
property concerns all morphisms of smooth test schemes, with no group structure
on the test scheme and no quasi-compactness restriction. Smoothness implies
locally of finite type; the model need not be quasi-compact.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- A smooth separated group model with the full Néron mapping property.
Source: BLR, 10.1 Definition 1 and 1.2 Definition 1
(blueprint: def-sfb-neron-lft-model).
Restriction first applies the canonical scheme base-change functor and then
composes with the specified generic group isomorphism. Smoothness includes the
locally finite type condition. No finite type condition is imposed on the model. -/
def IsNeronLftModel {D E : Type u} [CommRing D] [IsDomain D] [Field E]
    [Algebra D E] [IsFractionRing D E]
    (N : Grp (Over (Spec (.of D)))) (V : Grp (Over (Spec (.of E))))
    (e : (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap D E)))).mapGrp.obj N ≅ V) :
    Prop :=
  Smooth N.X.hom ∧ IsClosedImmersion (pullback.diagonal N.X.hom) ∧
    ∀ (X : Over (Spec (.of D))), Smooth X.hom →
      Function.Bijective (fun f : X ⟶ N.X ↦
        (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap D E)))).map f ≫ e.hom.hom.hom)

end AlgebraicGeometry
