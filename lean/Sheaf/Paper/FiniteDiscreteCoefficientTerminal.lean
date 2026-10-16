/- Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group D3 -/
module

public import Sheaf.Paper.FiniteDiscreteSchemeRing

/-! # The coefficient comparison at the base-changed terminal object -/

@[expose] public section

universe u

open CategoryTheory Limits
open scoped CategoryTheory.Obj

local instance : EssentiallySmall.{u + 1} Profinite.{u} := essentiallySmallSelf.{0} _

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (B : Type) [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]

/-- The coefficient comparison commutes with direct image at the base change of the
terminal object of the pro-etale site of Spec Z.
Source: Bhatt--Scholze, Proposition 5.3.2; the inverse-image composition adjunction.
(blueprint: lem-weil-pbc-finite-discrete-coefficient-terminal)

Proof in words. Put W = proEtTerminal Spec Z and W_X = pi_X^* W. The conjugation
unit law for constantPullbackMonoidalIso identifies the sheafification unit followed
by finiteDiscreteSchemeRingIso on W_X with q0 followed by the unit of pi_X^*.
Here q0 is the constant sheafification unit on Spec Z followed by constantPointIso
and pointUpperStar applied to eR. This formula follows from unit_conjugateEquiv_symm
and naturality of the inverse-image adjunction unit in eR. Apply
unit_comp_map_condensedPushforwardHom at W and precompose with q0. Its right-hand
side is the coefficient map on W_U followed by the restrictions for pullbackCongr
(comp_toSpecZ j) and pullbackComp j (toSpecZ T). Each restriction disappears by
naturality of a map from a constant presheaf: q(Y) = q(X) followed by restriction
along X to Y. Applying this twice gives the displayed equality at j^* W_T.
This uses no nonemptiness, finiteness, discreteness or nonzero-ring hypothesis. -/
theorem finiteDiscreteCoefficient_coefficientUnit_pushforward_terminal
    (eR : Sheaf.sheafifyRingPresheaf.{u + 1, u, u + 1}
      (coherentTopology Profinite.{u}) ((Functor.const Profinite.{u}ᵒᵖ).obj
        (RingCat.of (ULift.{u + 1} B))) ≅ Profinite.continuousMapRingObj.{u} B)
    (T U : Scheme.{u}) (j : U ⟶ T) :
    ((sheafificationAdjunction (ProEt.topology T) Ab.{u + 1}).unit.app
        ((Functor.const T.ProEtᵒᵖ).obj (AddCommGrpCat.of (ULift.{u + 1} B))) ≫
      (finiteDiscreteSchemeRingIso B T eR).hom.hom).app
        (Opposite.op ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ (toSpecZ T)).obj
          (proEtTerminal specZ.{u}))) ≫
        (condensedPushforwardHom (Profinite.continuousMapRingObj.{u} B) j).hom.app
        (Opposite.op ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ (toSpecZ T)).obj
          (proEtTerminal specZ.{u}))) =
    ((sheafificationAdjunction (ProEt.topology U) Ab.{u + 1}).unit.app
        ((Functor.const U.ProEtᵒᵖ).obj (AddCommGrpCat.of (ULift.{u + 1} B))) ≫
      (finiteDiscreteSchemeRingIso B U eR).hom.hom).app
        ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ j).op.obj
          (Opposite.op ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ (toSpecZ T)).obj
          (proEtTerminal specZ.{u})))) := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
