/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C8
-/
module

public import Sheaf.AlgebraicGeometry.LogFanChartBlowup

/-!
# Section-normalized characteristic pullback for strict morphisms

Source: ILO VI 1.1--1.2 and VIII, proof of 3.3.15, p.109.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory Opposite TopologicalSpace

namespace AlgebraicGeometry

/-- Strict pullback gives the characteristic map on all relative log sections and
bijections on its actual Zariski stalks. This assertion involves no fan charts.

Source: ILO VI 1.1--1.2, VIII 3.3.12 and proof of 3.3.15, printed p.109
(blueprint: lem-trf-strict-sharp-space-sections).

Proof: Start with the canonical characteristic map of the first clause of
`lem-trf-strict-log-blowup-cartesian`, whose stalk maps are bijective. Its underlying
continuous map is the specified map of schemes. Transport its section maps along this
base equality. For a relative log section on W and a factorization V -> W, the stalk
normalization in that clause identifies, at every point of V, the restriction of its
image with the characteristic class of the actual image log section. The naturality
of germs identifies the left side with the germ of the restricted pulled-back section.
Sheaf separation gives equality of these two sections on V. This also applies to the
empty V. Transport preserves the stalk bijections. Equivalently construct the maps by
quotienting the log section maps by units and sheafifying; the associated-log pullback
of a strict morphism has unchanged characteristic stalks, since local ring maps reflect
units. Thus the normalization is on every section, not just on chosen chart generators. -/
theorem strict_sharp_space_sections
    {Y X : FineSaturatedLogScheme.{u}} (f : EtaleLogHom Y X)
    (hf : f.IsStrict) (hX : X.logStructure.IsZariski) :
    ∃ sections : X.logStructure.sharpSpace.presheaf ⟶
        (Opens.map f.base.base).op ⋙ Y.logStructure.sharpSpace.presheaf,
      (∀ (W : X.scheme.Opens) (V : Y.scheme.Opens)
        (k : V.toScheme ⟶ W.toScheme) (hk : k ≫ W.ι = V.ι ≫ f.base)
        (h : V ≤ f.base ⁻¹ᵁ W)
        (s : X.logStructure.monoidSheaf.obj.obj (op ((logOpenEtale X.scheme).obj W))),
        Y.logStructure.sharpSpace.presheaf.map (homOfLE h).op
            (sections.app (op W) (X.logStructure.sharpSection W s)) =
          Y.logStructure.sharpSection V
            (f.sectionMap ((logOpenEtale X.scheme).obj W)
              ((logOpenEtale Y.scheme).obj V) k hk s)) ∧
      ∀ y : Y.scheme, Function.Bijective (FineFan.stalkMap
        (InducedCategory.homMk { base := f.base.base, c := sections } :
          Y.logStructure.sharpSpace ⟶ X.logStructure.sharpSpace) y) := by sorry

end AlgebraicGeometry
