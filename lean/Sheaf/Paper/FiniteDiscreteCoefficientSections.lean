/- Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group D2 -/
module

public import Sheaf.Paper.FiniteDiscreteSchemeRing

/-! # The coefficient maps on sections under direct image -/

@[expose] public section

universe u

open CategoryTheory Limits
open scoped CategoryTheory.Obj

local instance : EssentiallySmall.{u + 1} Profinite.{u} := essentiallySmallSelf.{0} _

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (B : Type) [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]

/-- The constant coefficients give the same map before and after direct image.
Source: Bhatt--Scholze, Proposition 5.3.2; the canonical constant-ring pullback
identification used in the common coefficient encoding.
(blueprint: lem-weil-pbc-finite-discrete-coefficient-sections)

Proof in words. Write q_T for the sheafification unit on the constant abelian
presheaf, followed by constantSchemeIso and the pullback of eR. The isomorphism
constantSchemeIso is the conjugate of pushforwardSectionsIso under the constant
sheaf and inverse-image adjunctions. The unit identity for conjugate natural
transformations (unit_conjugateEquiv_symm) identifies q_T with the map induced
by the constant coefficients
at the terminal pro-etale object. For j:U→T, condensedPushforwardHom is the mate
of the inverse-image composition isomorphism. The unit identity for composition
of the inverse-image adjunctions, implemented by
unit_comp_lowerStar_map_unit_comp_upperStarComp, identifies q_T followed by
this mate
with q_U evaluated at the base change of each object V. The pushforward
composition isomorphism here is the pullback associativity isomorphism on sites;
the two maps to the terminal object agree by terminal uniqueness. Finally the
naturality of upperStarFromPointComp in the condensed abelian sheaf moves the
fixed eR through this equality. This proves the displayed equality for every V.
The argument uses only the fixed coefficient identification and the adjunction
units; no discreteness, finiteness, nonempty-scheme or nonzero-ring assumption
is needed. -/
theorem finiteDiscreteCoefficient_coefficientUnit_pushforward
    (eR : Sheaf.sheafifyRingPresheaf.{u + 1, u, u + 1}
      (coherentTopology Profinite.{u}) ((Functor.const Profinite.{u}ᵒᵖ).obj
        (RingCat.of (ULift.{u + 1} B))) ≅ Profinite.continuousMapRingObj.{u} B)
    (T U : Scheme.{u}) (j : U ⟶ T) (V : T.ProEtᵒᵖ) :
    ((sheafificationAdjunction (ProEt.topology T) Ab.{u + 1}).unit.app
        ((Functor.const T.ProEtᵒᵖ).obj (AddCommGrpCat.of (ULift.{u + 1} B))) ≫
      (finiteDiscreteSchemeRingIso B T eR).hom.hom).app V ≫
        (condensedPushforwardHom (Profinite.continuousMapRingObj.{u} B) j).hom.app V =
    ((sheafificationAdjunction (ProEt.topology U) Ab.{u + 1}).unit.app
        ((Functor.const U.ProEtᵒᵖ).obj (AddCommGrpCat.of (ULift.{u + 1} B))) ≫
      (finiteDiscreteSchemeRingIso B U eR).hom.hom).app
        ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ j).op.obj V) := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
