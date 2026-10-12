/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H2
-/
module

public import Sheaf.ConstructibleSheaf.TorsorSectionRepresentation
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
import Sheaf.ConstructibleSheaf.TorsorAssociatedModule

/-!
# Normalized evaluation as the constant-sheaf coordinates upstairs

Source: Stacks Project, Tags 0DV5 (3), 0DV6, 0A3R, 04TR and 04TS;
lem-weil-pbc-torsor-section-evaluation-local, steps 1 and 3.
(blueprint: lem-weil-pbc-torsor-normalized-graph-evaluation)
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory Limits
namespace AlgebraicGeometry
open Etale

/-- The value of an ordinary normalized evaluation on the graph of f gives the
constant-sheaf coordinates on W. No equivariance of the evaluation is assumed.
Source: Stacks Project, Tags 0DV5 (3), 0DV6, 0A3R, 04TR and 04TS;
lem-weil-pbc-torsor-section-evaluation-local, steps 1 and 3.
(blueprint: lem-weil-pbc-torsor-normalized-graph-evaluation)

Proof:
Use the etale inverse-image/localization comparison to identify the restriction of F
to c.P with the given constant sheaf A. A morphism between etale V-objects is etale,
so f makes W an object of the small etale site of c.P. Its sections on an etale object T are locally
constant functions on T with value A. Since c.P is connected and nonempty, constant
functions identify A with F(c.P); restriction of a global section x is the constant
function x. This gives a canonical bijection gamma between F(W) and locally constant
functions on W with value F(c.P), where W is regarded as etale over c.P using f.
For a point of W and a section s, take an open neighborhood on which gamma(s) is the
constant value x. On that neighborhood s is the restriction of x along f. Naturality
of beta then identifies its value on the graph with beta at c.P evaluated on the
diagonal at f(w), which equals x by normalization. Thus graph evaluation after beta
is gamma, pointwise, and is bijective. On an empty W both the sheaf sections and locally
constant functions have a unique element by the empty covering. No torsor splitting
or extension of equivariant functions is used in this argument. -/
theorem Scheme.GaloisCover.ordinaryGraphEvaluation_bijective
    {V : Scheme.{u}} [ConnectedSpace V] (ℓ : ℕ) [Fact ℓ.Prime]
    (P : Type u) [Group P] [Finite P]
    (c : Scheme.GaloisCover (ULift.{u + 1} P) V) [ConnectedSpace c.P]
    (F : Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))))
    (A : ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ)))
    (h : Nonempty ((c.π)^*[ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))].obj F ≅
      (constantSheaf c.P.smallEtaleTopology
        (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ)))).obj A))
    (β : ∀ T : V.Etaleᵒᵖ, F.obj.obj T →ₗ[ULift.{u + 1} (ZMod ℓ)]
      LocallyConstant (c.sectionSpace T.unop) (F.obj.obj (Opposite.op c.sectionObject)))
    (hβ : ∀ (T T' : V.Etaleᵒᵖ) (g : T ⟶ T') (s : F.obj.obj T)
        (x : c.sectionSpace T'.unop),
      β T' (F.obj.map g s) x = β T s (c.sectionRestriction g.unop x))
    (hΔ : ∀ (s : F.obj.obj (Opposite.op c.sectionObject)) (y : c.P),
      β (Opposite.op c.sectionObject) s
        (pullback.lift (f := c.π) (g := c.π) (𝟙 c.P) (𝟙 c.P) (by simp) y) = s) (W : V.Etaleᵒᵖ)
    (f : W.unop ⟶ c.sectionObject) :
    Function.Bijective (fun s : F.obj.obj W ↦
      LocallyConstant.comap
        (pullback.lift (f := W.unop.hom) (g := c.π) (𝟙 W.unop.left) f.left
          (by simpa using (MorphismProperty.Over.w f).symm)).base.hom
        (β W s)) := by sorry

end AlgebraicGeometry
