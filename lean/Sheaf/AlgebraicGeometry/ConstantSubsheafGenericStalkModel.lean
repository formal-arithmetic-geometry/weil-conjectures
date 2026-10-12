/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J1
-/
module

public import WeilConjectures.ConstructibleSheaf.Defs

/-! # The constant model of the generic stalk image

Source: Stacks Project, Tag 09BH, Proposition 59.74.1 (3), generic submodule paragraph.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- A subobject of a constant module sheaf has a constant model of its generic stalk,
with the same inclusion into the ambient constant sheaf at every geometric generic point.
Source: Stacks Project, Tag 09BH, Proposition 59.74.1 (3), the submodule M' of M.
(blueprint: lem-weil-pbc-constant-subsheaf-generic-stalk-model).

Proof: Choose G isomorphic to the constant sheaf M and a geometric point above eta.
Under the constant-stalk identification with M, take N to be the range of the stalk
map of phi. Exactness of the stalk functor makes this map injective. The inclusion
N into M induces a monomorphism alpha from the constant N sheaf into G, because
constant presheaves and sheafification preserve monomorphisms. The range factorization
is an isomorphism from N to the stalk of F at the chosen point. To compare any other
geometric point over eta, compare the two separably closed residue-field extensions
through compatible separable closures. Base extension does not change an etale stalk;
these identifications are natural in F and G, and on constant M they identify the same
elements of M. Thus the range is N at every such point, giving the asserted compatible
isomorphisms. No finiteness, Noetherianity, or open-neighbourhood extension is used here.
If the range is zero, take N to be the zero module and the same range factorization. -/
theorem exists_constant_generic_stalk_model_of_mono_constant
    {X : Scheme.{u}} [IrreducibleSpace X]
    {Λ : Type (u + 1)} [CommRing Λ]
    {F G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)}
    (φ : F ⟶ G) [Mono φ] (hG : G.IsConstant X.smallEtaleTopology)
    (η : X) (hη : IsGenericPoint η Set.univ) :
    ∃ (N : ModuleCat.{u + 1} Λ)
      (α : (constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj N ⟶ G),
      Mono α ∧
      ∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ X),
        s (IsLocalRing.closedPoint Ω) = η →
        ∃ e : (pointSmallEtale s).sheafFiber.obj
            ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj N) ≅
            (pointSmallEtale s).sheafFiber.obj F,
          e.hom ≫ (pointSmallEtale s).sheafFiber.map φ =
            (pointSmallEtale s).sheafFiber.map α := by sorry

end AlgebraicGeometry.Scheme
