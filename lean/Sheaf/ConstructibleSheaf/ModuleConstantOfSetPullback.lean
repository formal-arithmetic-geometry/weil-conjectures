/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group U2
-/
module

public import Sheaf.AlgebraicGeometry.EtaleSheaves
public import Mathlib.CategoryTheory.Sites.Adjunction

/-!
# Recovering constant modules from a constant underlying inverse image

Source: Stacks Project, Tag 0DV5 (2)--(3), Tag 0DV6, and sites-modules Tag 093S.
(blueprint: lem-weil-pbc-module-constant-of-set-pullback)
-/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme

/-- On a connected scheme, a module inverse image is constant when its underlying set
inverse image is constant. No finiteness or local constancy hypothesis is required.
Source: Stacks Project, Tag 0DV5 (2)--(3), Tag 0DV6, and sites-modules Tag 093S.
(blueprint: lem-weil-pbc-module-constant-of-set-pullback)

Proof: inverse image of module sheaves commutes with the underlying-set functor:
construct inverse image by sheafifying the filtered neighbourhood colimits, whose
module structures are the colimit module structures. The underlying-set functor
preserves these filtered colimits and sheafification. Thus the hypothesis makes the
underlying sheaf of the module inverse image constant. On a connected nonempty scheme,
global sections of a constant set sheaf are exactly its value: sections are locally
constant functions and hence constant. Consequently the constant-sheaf functor is
fully faithful and preserves finite products. Transport addition, zero, negation and
each scalar multiplication through the underlying constant-sheaf identification;
full faithfulness makes them operations on its value. Faithfulness gives the module
axioms. The identification then lifts to a module-sheaf isomorphism from the constant
sheaf of this module to the inverse image. Equivalently, the constant/global-sections
counit is an isomorphism after forgetting modules, hence is an isomorphism of module
sheaves. This also covers the zero module and arbitrary coefficient rings. -/
theorem module_pullback_isConstant_of_set_pullback
    {U X : Scheme.{u}} [ConnectedSpace X]
    (R : Type (u + 1)) [CommRing R] (f : X ⟶ U)
    (F : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} R))
    (hF : ((etaleSetPullback f).obj
      ((sheafForget U.smallEtaleTopology).obj F)).IsConstant X.smallEtaleTopology) :
    ((Etale.upperStar (ModuleCat.{u + 1} R) f).obj F).IsConstant
      X.smallEtaleTopology := by sorry

end AlgebraicGeometry.Scheme
