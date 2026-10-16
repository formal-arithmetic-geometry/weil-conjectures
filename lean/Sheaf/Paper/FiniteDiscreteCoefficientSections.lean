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
  let WT : T.ProEt :=
    (MorphismProperty.Over.pullback @WeaklyEtale ⊤ (toSpecZ T)).obj
      (proEtTerminal specZ)
  let f : V.unop ⟶ WT := (proEtIsTerminal WT).from V.unop
  let fop : Opposite.op WT ⟶ V := f.op
  let pb := (MorphismProperty.Over.pullback @WeaklyEtale ⊤ j).op
  let pfp : pb.obj (Opposite.op WT) ⟶ pb.obj V := pb.map fop
  have hT := ((sheafificationAdjunction (ProEt.topology T) Ab.{u + 1}).unit.app
      ((Functor.const T.ProEtᵒᵖ).obj (AddCommGrpCat.of (ULift.{u + 1} B))) ≫
    (finiteDiscreteSchemeRingIso B T eR).hom.hom).naturality fop
  have hU := ((sheafificationAdjunction (ProEt.topology U) Ab.{u + 1}).unit.app
      ((Functor.const U.ProEtᵒᵖ).obj (AddCommGrpCat.of (ULift.{u + 1} B))) ≫
    (finiteDiscreteSchemeRingIso B U eR).hom.hom).naturality pfp
  have hp := (condensedPushforwardHom (Profinite.continuousMapRingObj.{u} B) j).hom.naturality fop
  have ht := finiteDiscreteCoefficient_coefficientUnit_pushforward_terminal B eR T U j
  have hT' := hT
  have hU' := hU
  change 𝟙 _ ≫ _ = _ at hT'
  change 𝟙 _ ≫ _ = _ at hU'
  simp only [Category.id_comp] at hT' hU'
  rw [hT']
  rw [Category.assoc, hp]
  rw [← Category.assoc, ht]
  rw [hU']
  rfl

end AlgebraicGeometry.ProEtale.CondensedRing
