/- Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group D2 -/
module

public import Sheaf.Paper.FiniteDiscreteSchemeRing
import Sheaf.Paper.FiniteDiscreteCoefficientTerminal

/-! # The coefficient maps on sections under direct image -/

@[expose] public section

universe u

open CategoryTheory Limits
open scoped CategoryTheory.Obj

local instance : EssentiallySmall.{u + 1} Profinite.{u} := essentiallySmallSelf.{0} _

private theorem constant_naturality {C A : Type*} [Category C] [Category A]
    {a : A} {P : C ⥤ A} (q : (Functor.const C).obj a ⟶ P)
    {X Y : C} (f : X ⟶ Y) : q.app Y = q.app X ≫ P.map f := by
  have h := q.naturality f
  change 𝟙 a ≫ q.app Y = q.app X ≫ P.map f at h
  exact (Category.id_comp _).symm.trans h

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (B : Type) [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]

attribute [local irreducible] upperStar upperStarLowerStarAdjunction

set_option backward.isDefEq.respectTransparency.types false in
/-- The constant coefficients give the same map before and after direct image.
Source: Bhatt--Scholze, Proposition 5.3.2; the canonical constant-ring comparison.
(blueprint: lem-weil-pbc-finite-discrete-coefficient-sections)

Proof in words. Use the coefficient comparison at the pullback of the terminal
object over Spec Z. For an arbitrary V, the unique map from V to this terminal
object gives an arrow in the opposite site. Naturality of the two coefficient
maps from constant presheaves and of condensedPushforwardHom propagates the
terminal comparison along that arrow. -/
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
  let a := AddCommGrpCat.of (ULift.{u + 1} B)
  let R := Profinite.continuousMapRingObj.{u} B
  let q (X : Scheme.{u}) : (Functor.const X.ProEtᵒᵖ).obj a ⟶
      ((upperStarFromPoint X).obj R).obj :=
    (sheafificationAdjunction (ProEt.topology X) Ab.{u + 1}).unit.app
      ((Functor.const X.ProEtᵒᵖ).obj a) ≫ (finiteDiscreteSchemeRingIso B X eR).hom.hom
  let F := MorphismProperty.Over.pullback @WeaklyEtale ⊤ j
  let W := proEtTerminal specZ.{u}
  let WT : T.ProEt := (MorphismProperty.Over.pullback @WeaklyEtale ⊤ (toSpecZ T)).obj W
  let eta := condensedPushforwardHom R j
  change (q T).app V ≫ eta.hom.app V = (q U).app (F.op.obj V)
  have ht := finiteDiscreteCoefficient_coefficientUnit_pushforward_terminal B eR T U j
  have : IsIso WT.hom := inferInstanceAs
    (IsIso ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ (toSpecZ T)).obj
      (proEtTerminal specZ.{u})).hom)
  let m : Opposite.op WT ⟶ V := ((proEtIsTerminal WT).from V.unop).op
  have hn := eta.hom.naturality m
  simp only [lowerStar_obj_obj_map'] at hn
  calc
    (q T).app V ≫ eta.hom.app V =
        ((q T).app (Opposite.op WT) ≫ ((upperStarFromPoint T).obj R).obj.map m) ≫
          eta.hom.app V := by rw [← constant_naturality (q T) m]
    _ = ((q T).app (Opposite.op WT) ≫ eta.hom.app (Opposite.op WT)) ≫
        ((upperStarFromPoint U).obj R).obj.map (F.op.map m) := by
      simpa only [Category.assoc, F, Functor.op_map] using
        congrArg (fun f ↦ (q T).app (Opposite.op WT) ≫ f) hn
    _ = (q U).app (F.op.obj (Opposite.op WT)) ≫
        ((upperStarFromPoint U).obj R).obj.map (F.op.map m) := by rw [ht]
    _ = (q U).app (F.op.obj V) := (constant_naturality (q U) (F.op.map m)).symm

end AlgebraicGeometry.ProEtale.CondensedRing
