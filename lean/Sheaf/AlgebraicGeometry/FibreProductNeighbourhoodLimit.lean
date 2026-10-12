/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.StrictHenselization
public import Mathlib.CategoryTheory.Comma.Over.Pullback
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Sheaf.AlgebraicGeometry.AffinePointedNeighbourhoodCofinal

/-!
# Base change and the neighbourhood limit

Source: Weil conjectures blueprint, `sec-curve-estimates/sk-prop-h2`,
(blueprint: lemma-weil-pbc-fibre-product-limit).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- The canonical base-change cone over all pointed étale neighbourhoods is limiting.
The existential structure map and cone legs are specified by their restrictions to the
chosen affine representatives: these are the spectra of the coordinate-ring colimit maps.
This states the canonical isomorphism with the inverse limit without assuming that limit
exists beforehand. The order of the two factors is immaterial: `Over.pullback f` uses
`V ×_S X` with its projection to `X`.

Source: blueprint `sec-curve-estimates/sk-prop-h2`,
(blueprint: lemma-weil-pbc-fibre-product-limit).

Proof:
1. The strict-henselization cone is limiting on the small affine representatives by
   `lem-weil-pbc-spec-small-colimit-limit`. Transport through the affine spectrum
   equivalence, and then along the initial affine inclusion
   (`lemma-weil-pbc-affine-neighbourhood-cofinal` and
   `lem-weil-pbc-colimit-initial-full-subcategory`), to get the full neighbourhood cone.
   Its leg at `(S,s)` is the structure map `p`; all its legs are over `S`.
2. A compatible cone to the fibre products gives a compatible cone to the neighbourhoods
   and hence a unique map to the strict henselization. Its components to `X` agree:
   cofilteredness (`lem-weil-pbc-pointed-etale-neighbourhoods-cofiltered`) supplies common
   refinements. The component at `(S,s)` ensures that the two maps agree over `S`.
3. The fibre-product universal property (`def-pc-fibre-product`) gives the unique map to
   the vertex of the displayed cone. Equality of its two components proves uniqueness,
   so this cone is limiting and gives the canonical comparison isomorphism. -/
theorem fibre_product_neighbourhood_limit
    {X S : Scheme.{u}} (f : X ⟶ S) [QuasiCompact f] [QuasiSeparated f]
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S) :
    ∃ (p : Scheme.strictHenselizationScheme s ⟶ S)
      (q : (Functor.const (Scheme.pointSmallEtale s).fiber.Elements).obj (Over.mk p) ⟶
        CategoryOfElements.π (Scheme.pointSmallEtale s).fiber ⋙ Scheme.Etale.forget S),
      (∀ j : SmallModel.{u} (Scheme.strictHenselizationNeighbourhoods s),
        (q.app ((Scheme.strictHenselizationAffineInclusion s ⋙ ObjectProperty.ι
          (fun n : (Scheme.pointSmallEtale s).fiber.Elements ↦ IsAffine n.1.left)).obj
            ((equivSmallModel.{u} (Scheme.strictHenselizationNeighbourhoods s)).inverse.obj
              j))).left =
          (Scheme.strictHenselizationCone s).π.app (op (op j)) ≫
            (Spec (unop
              ((equivSmallModel.{u} (Scheme.strictHenselizationNeighbourhoods s)).inverse.obj
                j).1.left)).isoSpec.inv) ∧
      Nonempty (IsLimit ((Over.pullback f ⋙ Over.forget X).mapCone
        { pt := Over.mk p, π := q })) := by
  sorry

end AlgebraicGeometry
