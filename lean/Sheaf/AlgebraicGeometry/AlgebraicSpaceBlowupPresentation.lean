/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q28
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentIdeal
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceSchemeRestriction
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceArtinRees
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceOpenSubspace
public import WeilConjectures.Blowup.Gluing

/-! # Algebraic-space blowups specified on affine etale charts

Source: Stacks Project, Spaces Divisors, definition-blow-up, Tags 085Q and 085R
(blueprint: def-sfb-space-blowup-presentation).

A presentation retains an actual algebraic space and its projection, requiring every
base change to an affine etale chart to be the ordinary scheme blowup. This describes
the descended relative Proj up to isomorphism over the base, without selecting an
object from an uncharacterized existence theorem.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.AlgebraicSpace

/-- The quasi-coherent ideal on a scheme chart, formed from its ideals of sections on
all affine opens using Mathlib's canonical ideal-sheaf construction.
Source: Stacks Project, Spaces Divisors, Tags 085Q and 085R
(blueprint: def-sfb-space-blowup-presentation). -/
def blowupChartIdeal {S : Scheme.{u}} {X : AlgebraicSpace S}
    (I : QuasiCoherentIdeal X) (V : X.EtaleSite) :
    Scheme.IdealSheafData (X.etaleForget.obj V) :=
  Scheme.IdealSheafData.ofIdeals fun W ↦
    (idealSectionImage I.val.arrow ((X.schemeOpens V).obj W.1)).comap
      ((X.schemeOpensRingHom V).app (op W.1)).hom

/-- A model of the descended Rees Proj: every affine etale chart pulls its projection
back to the ordinary scheme blowup of the restricted ideal. The actual projection
provides compatibility on overlaps, so no atlas or transition maps are chosen.
Source: Stacks Project, Spaces Divisors, Tags 085Q and 085R
(blueprint: def-sfb-space-blowup-presentation). -/
structure BlowupPresentation {S : Scheme.{u}} {X : AlgebraicSpace S}
    (I : QuasiCoherentIdeal X) where
  space : AlgebraicSpace S
  projection : space ⟶ X
  charts : ∀ (V : X.EtaleSite), IsAffine (X.etaleForget.obj V) →
    ∃ q : yoneda.obj (Over.mk
        ((blowupChartIdeal I V).blowupMap ≫ V.obj.left.hom)) ⟶ space.obj.obj,
      IsPullback q
        (yoneda.map (Over.homMk (blowupChartIdeal I V).blowupMap))
        projection.hom.hom V.obj.hom

/-- The ideal is the unit ideal over the inverse image of the specified open. Its
sections on every etale chart mapping into that inverse image are the whole ring.
Taking p to be the identity gives restriction to the open itself.
Source: Stacks Project, Spaces Divisors, Tag 086B
(blueprint: def-sfb-space-blowup-presentation). -/
def IdealIsUnitAbove {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (I : QuasiCoherentIdeal Y) (p : Y ⟶ X) (U : OpenSubspace X) : Prop :=
  ∀ V : Y.EtaleSite,
    (∃ a : yoneda.obj V.obj.left ⟶ U.val.toFunctor,
      a ≫ U.val.ι = V.obj.hom ≫ p.hom.hom) →
    idealSectionImage I.val.arrow V = ⊤

end AlgebraicGeometry.AlgebraicSpace
