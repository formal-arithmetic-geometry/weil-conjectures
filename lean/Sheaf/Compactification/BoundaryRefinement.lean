/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q56
-/
module

public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.CategoryTheory.Widesubcategory
public import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
public import WeilConjectures.Compactification.Refinement
public import WeilConjectures.Compactification.RefinementCategory

/-!
# Boundary-preserving refinements of compactifications

Source: blueprint main-20261015, sec-nagata-compactification,
sk-def-nagata-sketch-data, det-nagata-definition-refinement
(blueprint: det-nagata-definition-refinement).

The upstream `Compactification.Refinement` records the two commuting triangles only.
Here morphisms additionally preserve the inverse image of the distinguished open.
Objects have quasi-compact open immersions, as required in this node. Equality in
`Scheme.Opens` is equality of open subschemes, each with its restricted structure sheaf.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Compactification

/-- Compactifications with quasi-compact open immersion, using the existing compactification
structure. Source: blueprint main-20261015, det-nagata-definition-refinement, opening sentence
(blueprint: det-nagata-definition-refinement). -/
abbrev QuasiCompactObjects {X S : Scheme.{u}} (f : X ⟶ S) : Type (u + 1) :=
  ObjectProperty.FullSubcategory (fun c : Compactification f ↦ QuasiCompact c.i)

/-- The third refinement condition: the inverse image of the target's distinguished open is
exactly the source's distinguished open. The underlying upstream refinement already gives
`r.hom.hom ≫ d.obj.g = c.obj.g` and `c.obj.i ≫ r.hom.hom = d.obj.i`.
The latter identifies the restriction with `j ∘ (j')⁻¹`; the additional equality says that
boundary points map to boundary points.
Source: blueprint main-20261015, det-nagata-definition-refinement, conditions 1--3
(blueprint: det-nagata-definition-refinement). -/
def boundaryRefinementProperty {X S : Scheme.{u}} (f : X ⟶ S) :
    MorphismProperty (QuasiCompactObjects f) :=
  fun c d r ↦ r.hom.hom ⁻¹ᵁ d.obj.i.opensRange = c.obj.i.opensRange

/-- Identity refinements preserve the open, and boundary-preserving refinements compose.
Source: blueprint main-20261015, det-nagata-definition-refinement, final paragraph
(blueprint: det-nagata-definition-refinement).

Proof: the identity has inverse image equal to the same open. For consecutive refinements
`r : c ⟶ d` and `s : d ⟶ e`, inverse image under their ambient composite is the iterated
inverse image. Substitute `s⁻¹(e.i(X)) = d.i(X)` and then
`r⁻¹(d.i(X)) = c.i(X)`. The upstream identity and composition already satisfy both triangle
equalities, with ambient maps the scheme identity and composite, respectively. -/
theorem boundaryRefinementProperty_isMultiplicative {X S : Scheme.{u}} (f : X ⟶ S) :
    (boundaryRefinementProperty f).IsMultiplicative := by
  refine { id_mem := fun c ↦ ?_, comp_mem := fun r s hr hs ↦ ?_ }
  · change (𝟙 c.obj.Z) ⁻¹ᵁ c.obj.i.opensRange = c.obj.i.opensRange
    exact Scheme.Hom.id_preimage _
  · change r.hom.hom ⁻¹ᵁ _ = _ at hr
    change s.hom.hom ⁻¹ᵁ _ = _ at hs
    change (r.hom.hom ≫ s.hom.hom) ⁻¹ᵁ _ = _
    rw [Scheme.Hom.comp_preimage, hs, hr]

attribute [instance] boundaryRefinementProperty_isMultiplicative

/-- The category of compactifications with quasi-compact open immersions and refinements
satisfying all three conditions: the two commuting triangles and equality of inverse-image
open subschemes. Identities and composition are induced by those of the ambient schemes.
Source: blueprint main-20261015, det-nagata-definition-refinement, final paragraph
(blueprint: det-nagata-definition-refinement). -/
abbrev BoundaryCompactification {X S : Scheme.{u}} (f : X ⟶ S) : Type (u + 1) :=
  WideSubcategory (boundaryRefinementProperty f)

/-- The full subcategory on the scheme-theoretically dense compactifications.
Density is precisely the dependency's `IsSchemeTheoreticallyDominant` on the open immersion;
quasi-compactness is already part of the ambient category's objects.
Source: blueprint main-20261015, det-nagata-definition-refinement, last sentence, and
def-nagata-dense-compactification
(blueprint: det-nagata-definition-refinement). -/
abbrev DenseBoundaryCompactification {X S : Scheme.{u}} (f : X ⟶ S) : Type (u + 1) :=
  ObjectProperty.FullSubcategory
    (fun c : BoundaryCompactification f ↦ IsSchemeTheoreticallyDominant c.obj.obj.i)

/-- The canonical fully faithful inclusion of dense compactifications into the category
with boundary-preserving refinements. Fullness and faithfulness are the standard instances
for an `ObjectProperty.FullSubcategory` inclusion.
Source: blueprint main-20261015, det-nagata-definition-refinement, last sentence
(blueprint: det-nagata-definition-refinement). -/
abbrev denseBoundaryInclusion {X S : Scheme.{u}} (f : X ⟶ S) :
    DenseBoundaryCompactification f ⥤ BoundaryCompactification f :=
  ObjectProperty.ι _

end AlgebraicGeometry.Compactification
