/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F2
-/
module

public import Sheaf.ConstructibleSheaf.TorsorSectionRepresentation
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs

/-! # Ordinary locally constant evaluation on a torsor

Source: Stacks Project, Tags 0DV5 (3), 0DV6 and 0A3R; sites.tex, Example
constant-sheaf and Tags 04TR and 04TS. Fixed-cover adaptation to arbitrary modules.
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory Limits Opposite
namespace AlgebraicGeometry
open Etale
/-- Ordinary evaluation exists without imposing deck equivariance.
Source: Stacks Project, Tags 0DV5 (3), 0DV6 and 0A3R; sites.tex, Example
constant-sheaf and Tags 04TR and 04TS. Fixed-cover adaptation to arbitrary modules.
(blueprint: lem-weil-pbc-torsor-ordinary-evaluation)

Proof: For the etale map Y to V, inverse image identifies with restriction to
Y's small etale site. Under the supplied trivialization, a section over an etale
Y-object U is a locally constant A-valued function on U: constant presheaf sections
are locally constant sections, and sheafification glues these on etale covers.
Etale maps are open, so the glued constant labels give locally constant functions
on the underlying space. Conversely their open fibres give the required gluing.
These identifications preserve addition, scalars, and restriction. Since Y is
nonempty and connected, evaluation identifies the global sections of this constant
sheaf with A. Invert this isomorphism to identify A with F(Y); under this identification
a global section x restricts to the constant function with value x. For each W,
restrict s to U=W times_V Y, considered over Y, and read it as a locally constant
F(Y)-valued function. This defines the linear map beta_W. Restriction along W' to W
commutes with this construction, giving the naturality equation. For W=Y, restriction
along the diagonal is the original section s, giving the diagonal equation. The
empty object has the unique zero function; the construction also covers zero
coefficients and the identity torsor. No equivariance is imposed at this step. -/
theorem Scheme.GaloisCover.exists_ordinarySectionEvaluation
    {V : Scheme.{u}} [ConnectedSpace V] (ℓ : ℕ) [Fact ℓ.Prime]
    (P : Type u) [Group P] [Finite P]
    (c : Scheme.GaloisCover (ULift.{u + 1} P) V) [ConnectedSpace c.P]
    (F : Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))))
    (A : ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ)))
    (h : Nonempty ((c.π)^*[ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))].obj F ≅
      (constantSheaf c.P.smallEtaleTopology
        (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ)))).obj A)) :
    ∃ β : ∀ W : V.Etaleᵒᵖ, F.obj.obj W →ₗ[ULift.{u + 1} (ZMod ℓ)]
      LocallyConstant (c.sectionSpace W.unop) (F.obj.obj (op c.sectionObject)),
      (∀ (W W' : V.Etaleᵒᵖ) (f : W ⟶ W') (s : F.obj.obj W)
        (x : c.sectionSpace W'.unop),
      β W' (F.obj.map f s) x = β W s (c.sectionRestriction f.unop x)) ∧
      (∀ (s : F.obj.obj (op c.sectionObject)) (y : c.P),
      β (op c.sectionObject) s
        (pullback.lift (f := c.π) (g := c.π) (𝟙 c.P) (𝟙 c.P) (by simp) y) = s) := by sorry

end AlgebraicGeometry
