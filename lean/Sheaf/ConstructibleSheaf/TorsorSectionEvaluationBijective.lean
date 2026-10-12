/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group B2
-/
module

public import Sheaf.ConstructibleSheaf.TorsorSectionRepresentation
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs

/-!
# Bijectivity of normalized evaluation on a connected torsor

Source: Stacks Project, Tags 0DV5 (3), 0DV6, 0A3R, 04TR and 04TS.
(blueprint: lem-weil-pbc-torsor-section-evaluation-bijective)
-/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory Limits
namespace AlgebraicGeometry
open Etale

/-- Every normalized natural evaluation map is bijective on each etale object.
This is the descent and gluing step, for a supplied map and a fixed representation.
Source: Stacks Project, Tags 0DV5 (3), 0DV6, 0A3R, 04TR and 04TS.
(blueprint: lem-weil-pbc-torsor-section-evaluation-bijective)

Proof:
Again c*F is the function sheaf with value F(Y), because the connected nonempty scheme Y
has only constant global locally constant functions. On an etale object T over Y, every
section is locally the restriction of some x in F(Y). For such a section, naturality of
alpha along T to Y, together with diagonal normalization at Y, determines its value at
all points of the graph of T to Y. Consequently the map alpha on W, after restriction
to W times_V Y, is exactly evaluation in this function sheaf. It is injective: if alpha
kills s, its restriction to W times_V Y is zero, and separatedness of F for the surjective
etale covering W times_V Y to W gives s=0. For surjectivity, start with an equivariant
locally constant function t on W times_V Y with values in F(Y). View it as a section of
the restriction of F, using the constant function sheaf identification above. The two
pullbacks of this section to the double overlap agree: the torsor isomorphism decomposes
the overlap into the components indexed by g in P, and agreement on the g component
is exactly t(g y)=F(g inverse)(t(y)). Sheaf gluing produces a unique section s over W.
The already determined local formula for alpha gives alpha(s)=t; equality can be checked
on the surjective covering. No finite generation is used. For an empty W both modules
have only the zero section, and for the identity torsor this is the ordinary constant
function description. This proof applies to every normalized alpha, not to an arbitrary
unconstrained comparison functor or map. -/
theorem Scheme.GaloisCover.sectionEvaluation_bijective
    {V : Scheme.{u}} [ConnectedSpace V] (ℓ : ℕ) [Fact ℓ.Prime]
    (P : Type u) [Group P] [Finite P]
    (c : Scheme.GaloisCover (ULift.{u + 1} P) V) [ConnectedSpace c.P]
    (F : Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))))
    (A : ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ)))
    (h : Nonempty ((c.π)^*[ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))].obj F ≅
      (constantSheaf c.P.smallEtaleTopology
        (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ)))).obj A))
    (α : F.obj ⟶ c.sectionRepresentationPresheaf ℓ F)
    (hα : c.SectionEvaluationNormalized ℓ F α) (W : V.Etaleᵒᵖ) :
    Function.Bijective (α.app W) := by sorry

end AlgebraicGeometry
