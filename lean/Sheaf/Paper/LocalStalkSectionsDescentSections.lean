/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group D2
-/
module

public import Sheaf.Paper.LocalStalkSectionsComparisonMap

/-! # Descent of sections from the local scheme

Source: Stacks Project, Tag 03Q6, degree zero of Lemma 59.51.5.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry TopologicalSpace

/-- Descent of sections from the local scheme.
Source: Stacks Project, Tag 03Q6, degree zero and proof steps (1)-(3).
(blueprint: new-local-stalk-sections-descent-sections)

Proof: Choose an affine neighbourhood V of x. Principal opens of V containing x
are cofinal among neighbourhoods of x: intersect any neighbourhood with V and use
the principal-open basis of V. The colimit of their coordinate rings is O_X,x.
Apply the degree-zero section assertion of Tag 03Q6 to the identity of V, which is
quasi-compact and quasi-separated, and to the restriction of F to V. Every section
of the inverse-image sheaf on Spec(O_X,x) descends to a section on one of these
principal opens. This gives the required neighbourhood U and section t. The maps
are the pullback maps given by the inverse-image unit and the local-scheme maps to
the neighbourhoods. Identify the standard inverse image with the displayed H by
uniqueness of left adjoints to the same direct image. This identification respects
the units and therefore identifies its pullback maps with LocalStalkSections.comparison.
Transport the descended section through that isomorphism to obtain the requested
representative. The zero sheaf is included; no henselian or global qcqs hypothesis is needed.
Small affine presentations keep the coefficient universe fixed; empty X has no x. -/
theorem localStalkSections_descent_sections
    {X : Scheme.{u + 1}} (i : X.Opens ⥤ X.Etale)
    (hi : i ⋙ Scheme.Etale.forget X = X.restrictFunctor) (x : X)
    (H : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} ⥤
      Sheaf (Spec (X.presheaf.stalk x)).smallEtaleTopology AddCommGrpCat.{u + 1})
    (hH : H ⊣ (X.fromSpecStalk x).Etale.sheafPushforwardContinuous
      AddCommGrpCat.{u + 1} X.smallEtaleTopology
      (Spec (X.presheaf.stalk x)).smallEtaleTopology)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (s : (H.obj F).obj.obj (op (Scheme.Etale.mk (𝟙 _)))) :
    ∃ (U : (OpenNhds x)ᵒᵖ) (t : (LocalStalkSections.neighbourhoodDiagram i x F).obj U),
      (LocalStalkSections.cocone i hi x H hH F).ι.app U t = s := by sorry
