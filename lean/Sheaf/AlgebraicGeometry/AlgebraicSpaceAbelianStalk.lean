/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q107
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpace
public import Mathlib.Algebra.Category.Grp.Colimits
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic

/-! # Abelian stalks on the small étale site of an algebraic space

Source: Stacks Project, Properties of Spaces, geometric points and stalks, Tags 0486,
04JV and 04JY (blueprint: def-sfb-space-pointed-etale-abelian-stalk).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} (X : AlgebraicSpace S) {P : Over S}

/-- Pointed étale scheme neighbourhoods of a scheme-valued point `x`. An object is a
scheme chart and a map from `P` to its underlying scheme, over `x`; arrows preserve it.
For geometric stalks take `P = Spec Ω` over `S`, with `Ω` algebraically closed.
Source: Stacks, Properties of Spaces, Tags 0486, 04JV and 04JY
(blueprint: def-sfb-space-pointed-etale-abelian-stalk). -/
abbrev PointedEtale (x : yoneda.obj P ⟶ X.obj.obj) :=
  StructuredArrow (CostructuredArrow.mk x)
    (ObjectProperty.ι (fun T : CostructuredArrow yoneda X.obj.obj ↦ IsEtale T.hom))

/-- Forget the lift of the point, retaining the étale scheme chart.
Source: Stacks, Tags 0486, 04JV and 04JY
(blueprint: def-sfb-space-pointed-etale-abelian-stalk). -/
def pointedEtaleForget (x : yoneda.obj P ⟶ X.obj.obj) : X.PointedEtale x ⥤ X.EtaleSite :=
  StructuredArrow.proj _ _

/-- Abelian stalk: the colimit of sections over the opposite of the actual category
of pointed étale scheme neighbourhoods. Coefficients live in the larger universe;
the site and its pointed neighbourhood category have objects in `Type (u+1)`.
Source: Stacks, Tags 0486, 04JV and 04JY
(blueprint: def-sfb-space-pointed-etale-abelian-stalk). -/
def abelianStalk (x : yoneda.obj P ⟶ X.obj.obj) :
    Sheaf X.etaleTopology AddCommGrpCat.{u + 1} ⥤ AddCommGrpCat.{u + 1} :=
  sheafToPresheaf _ _ ⋙
    (Functor.whiskeringLeft _ _ _).obj (X.pointedEtaleForget x).op ⋙ colim

/-- The germ homomorphism is the colimit cocone at the specified pointed chart.
Source: Stacks, Tags 0486, 04JV and 04JY
(blueprint: def-sfb-space-pointed-etale-abelian-stalk). -/
def abelianGerm (x : yoneda.obj P ⟶ X.obj.obj) (N : X.PointedEtale x)
    (A : Sheaf X.etaleTopology AddCommGrpCat.{u + 1}) :
    A.obj.obj (op N.right) ⟶ (X.abelianStalk x).obj A :=
  colimit.ι ((X.pointedEtaleForget x).op ⋙ A.obj) (op N)

end AlgebraicGeometry.AlgebraicSpace
