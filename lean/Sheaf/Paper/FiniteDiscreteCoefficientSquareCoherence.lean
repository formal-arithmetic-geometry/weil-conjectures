/- Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A4 -/
module

public import Sheaf.Paper.FiniteDiscreteCoefficientPullbackIso

/-! # Square coherence for the finite discrete coefficient realization -/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory MonObj
open scoped CategoryTheory.Obj CategoryTheory.Functor

attribute [local instance] coefficientProfiniteEssentiallySmall

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (B : Type) [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]

variable
  (eR : Sheaf.sheafifyRingPresheaf.{u + 1, u, u + 1}
      (coherentTopology Profinite.{u}) ((Functor.const Profinite.{u}ᵒᵖ).obj
        (RingCat.of (ULift.{u + 1} B))) ≅ Profinite.continuousMapRingObj.{u} B)
  [IsMonHom eR.hom]
  (G : Mod Ab.{u + 1} (AddCommGrpCat.of (ULift.{u + 1} B)) ⥤
    ModuleCat.{u + 1} (ULift.{u + 1} B)) [G.IsEquivalence]
  (hG : G ⋙ forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} B)) Ab.{u + 1} =
    Mod.forget (AddCommGrpCat.of (ULift.{u + 1} B)))

/-- The canonical derived coefficient pullback comparison commutes with square transport.
Source: Bhatt--Scholze, Lemma 5.4.1; Proposition 5.3.2
(blueprint: lem-weil-pbc-finite-discrete-coefficient-square-coherence).

Proof in words. Use finiteDiscreteCoefficientRestrictionIso_comp from
Sheaf.Paper.FiniteDiscreteCoefficientRestrictionCoherence for the specified restriction
comparison. Its proof cancels the intermediate encoding isomorphism after forgetting
module actions and uses naturality of restriction composition.
Conjugate this identity through the adjunctions used
in finiteDiscreteCoefficientProEtalePullbackIso. The composition law for conjugation gives
the corresponding identity for the ordinary pullback comparison, including the ordinary
etale/pro-etale comparison. Apply exact functors termwise to complexes and then localize;
mapDerivedCategorySquareIso_paste from Sheaf.Paper.DerivedSquarePasting gives
the pasting compatibility, while naturality of the derived composition comparisons
transports the ordinary composition maps. Restrict the etale source to D+ using
mapDerivedCategoryPlusCompatibility.
Finally replace the exact internal pullbacks by their total left derived functors.
Their composition isomorphism is defined by the same replacement, so the replacement
isomorphisms cancel. Transporting along sq.w yields exactly coefficientAmbientSquare.
Thus the resulting equation is the displayed equation for the specified comparison.
-/
theorem finiteDiscreteCoefficientPullbackIso_square
    : CoefficientPullbackSquare B (Profinite.continuousMapRingObj B)
      (fun T ↦ finiteDiscreteRealization B T
        (finiteDiscreteCoefficientEquivalence B eR G hG T))
      (finiteDiscreteCoefficientPullbackIso B eR G hG) := by sorry

end AlgebraicGeometry.ProEtale.CondensedRing
