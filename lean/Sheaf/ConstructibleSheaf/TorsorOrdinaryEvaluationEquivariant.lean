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
/-- A natural ordinary evaluation normalized on the diagonal is deck-equivariant.
Source: Stacks Project, Tags 0DV5 (3), 0DV6 and 0A3R; sites.tex, Example
constant-sheaf and Tags 04TR and 04TS. Fixed-cover adaptation to arbitrary modules.
(blueprint: lem-weil-pbc-torsor-ordinary-evaluation-equivariant)

Proof: The constant trivialization and connectedness of Y identify the restricted
sheaf with the locally constant function sheaf valued in F(Y), with restriction of
a global section a corresponding to the constant function a. Put U=W times_V Y,
with projections p to W and q to Y, and restrict s to t=p*s. Around any point x of
U choose an etale neighbourhood T on which t=q*a for some a in F(Y). On the graph
of q:T to Y, naturality of beta along q and diagonal normalization give value a;
naturality along p then gives beta_W(s)(x)=a. Etale covers are surjective on points,
so such neighbourhoods determine all the values of beta. At the translated point
g*x, use the same T with its Y-map changed from q to g*q. The same section t is now
the restriction of b=F(g inverse)(a), since (g*q)*b=q*a. Naturality and diagonal
normalization therefore give beta_W(s)(g*x)=b. This is exactly the action in
sectionRepresentation, whose scalar restriction does not change underlying values.
This argument uses only local constant presentations of sections, not uniqueness of
a chosen trivialization or any equivariance assumption on beta. Empty objects give
a vacuous assertion; zero coefficients and the identity torsor obey the same formula. -/
theorem Scheme.GaloisCover.ordinarySectionEvaluation_equivariant
    {V : Scheme.{u}} [ConnectedSpace V] (ℓ : ℕ) [Fact ℓ.Prime]
    (P : Type u) [Group P] [Finite P]
    (c : Scheme.GaloisCover (ULift.{u + 1} P) V) [ConnectedSpace c.P]
    (F : Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))))
    (A : ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ)))
    (h : Nonempty ((c.π)^*[ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))].obj F ≅
      (constantSheaf c.P.smallEtaleTopology
        (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ)))).obj A))
    (β : ∀ W : V.Etaleᵒᵖ, F.obj.obj W →ₗ[ULift.{u + 1} (ZMod ℓ)]
      LocallyConstant (c.sectionSpace W.unop) (F.obj.obj (op c.sectionObject)))
    (hβ : ∀ (W W' : V.Etaleᵒᵖ) (f : W ⟶ W') (s : F.obj.obj W)
        (x : c.sectionSpace W'.unop),
      β W' (F.obj.map f s) x = β W s (c.sectionRestriction f.unop x))
    (hΔ : ∀ (s : F.obj.obj (op c.sectionObject)) (y : c.P),
      β (op c.sectionObject) s
        (pullback.lift (f := c.π) (g := c.π) (𝟙 c.P) (𝟙 c.P) (by simp) y) = s) :
    ∀ (W : V.Etaleᵒᵖ) (s : F.obj.obj W) (g : P) (x : c.sectionSpace W.unop),
      β W s (c.sectionAction W.unop g x) =
        (c.sectionRepresentation ℓ F).ρ g (β W s x) := by sorry

end AlgebraicGeometry
