/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NP
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCompactFppfLocal
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
public import Sheaf.TraceFormula.SpaceQCSeparatedEtaleLocal
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.Topology.Defs.Filter
import Sheaf.AlgebraicGeometry.SchemeEtaleSourceTargetProperties
import Sheaf.AlgebraicGeometry.SpaceEtalePresentationPropertyCriterion
import Mathlib.AlgebraicGeometry.Sites.MorphismProperty

/-! # Composition of separated and finitely presented algebraic-space morphisms

Source: Stacks Project, Morphisms of Spaces, Tags 03KL, 03KQ and 03XQ;
definitions in Tags 03HL and 03XP
(blueprint: lem-sfb-space-separated-fp-composition).

Finite presentation is expanded as local finite presentation, quasi-compactness,
and quasi-compactness of the diagonal, using the existing scheme-test predicates.
The four implications are independent and do not assume representability of the maps.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace

/-- Separated, finitely presented, and locally finitely presented space morphisms compose;
separatedness is preserved by arbitrary algebraic-space base change.
Source: Stacks, Morphisms of Spaces, Tags 03KL, 03KQ and 03XQ
(blueprint: lem-sfb-space-separated-fp-composition).

Proof:
1. Set D = X ×_Y X and E = X ×_Z X. The diagonal of the composite factors as
   X → D → E, where D → E is the pullback of the diagonal of g along (f,f).
   On sections, its data are pairs (x₁,x₂) with f(x₁) = f(x₂). The same calculation
   identifies the base-changed diagonal with a pullback of the original diagonal.
   These natural identifications use [lem-trf-space-fibre-products-etale-covers].
2. A scheme test of a pullback of a representable closed immersion is already a
   scheme test of that immersion. For a composite, first test the second map,
   then the first; their scheme projections compose by
   [lem-weil-pbc-closed-immersion-comp]. Apply these facts to the diagonal
   factorizations in step 1, proving both separatedness clauses. Uses
   [def-trf-algebraic-space] and [def-weil-closed-immersion].
3. Quasi-compact maps compose: for a quasi-compact test T of the composite,
   Y ×_Z T is quasi-compact, and then X ×_Y (Y ×_Z T) = X ×_Z T is quasi-compact.
   Base change preserves quasi-compactness by [lem-sfb-space-quasicompact-fppf-local].
   Thus the factorization in step 1 proves composition of quasi-separated maps.
4. For g choose compatible scheme charts V → Y and W → Z with V → Y surjective,
   using [lem-sfb-space-etale-presentation-property-criterion]. Take an atlas
   U → X ×_Y V and compose to obtain a surjective étale U → X. Scheme tests,
   [lem-trf-space-fibre-products-etale-covers] and
   [lem-weil-pbc-etale-covering-composition] verify this atlas condition.
   By [lem-sfb-scheme-etale-source-target-properties] and the presentation criterion,
   local finite presentation of f and g gives it for U → V and V → W.
5. By [lem-sbc-locally-finite-presentation-composition], U → W is locally finitely
   presented. It presents gf, so the same presentation criterion gives local finite
   presentation of gf. No representability of f or g was used.
6. For finitely presented f and g, step 5 gives the local clause and step 3 gives
   quasi-compactness of the composite and its diagonal. Together these are exactly
   finite presentation as in Tag 03XP. -/
theorem separated_finitePresentation_composition_and_separated_baseChange
    {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (IsSeparatedPresheafMap f.hom.hom → IsSeparatedPresheafMap g.hom.hom →
      IsSeparatedPresheafMap (f ≫ g).hom.hom) ∧
    ((MapIsLocallyOfFinitePresentation f ∧ IsQuasiCompactPresheafMap f.hom.hom ∧
        IsQuasiCompactPresheafMap (diagonalPresheafMap f.hom.hom)) →
      (MapIsLocallyOfFinitePresentation g ∧ IsQuasiCompactPresheafMap g.hom.hom ∧
        IsQuasiCompactPresheafMap (diagonalPresheafMap g.hom.hom)) →
      (MapIsLocallyOfFinitePresentation (f ≫ g) ∧
        IsQuasiCompactPresheafMap (f ≫ g).hom.hom ∧
        IsQuasiCompactPresheafMap (diagonalPresheafMap (f ≫ g).hom.hom))) ∧
    (MapIsLocallyOfFinitePresentation f → MapIsLocallyOfFinitePresentation g →
      MapIsLocallyOfFinitePresentation (f ≫ g)) ∧
    (∀ (Y' : AlgebraicSpace S) (h : Y' ⟶ Y), IsSeparatedPresheafMap f.hom.hom →
      IsSeparatedPresheafMap (Limits.pullback.snd f.hom.hom h.hom.hom)) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
