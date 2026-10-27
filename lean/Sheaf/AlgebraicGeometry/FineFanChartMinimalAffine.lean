/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P2
-/
module

public import Sheaf.AlgebraicGeometry.AffineFanHomUniversal

/-!
# The affine model of a smallest neighborhood inside one fine chart

Source: ILO VIII 3.1.1--3.1.4, 3.1.8(ii), and 3.1.10(ii), pp.98--100
(blueprint: lem-trf-fine-fan-chart-minimal-affine).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory TopologicalSpace Opposite

namespace AlgebraicGeometry.FineFan

/-- A smallest neighborhood inside a specified fine chart has a normalized affine
stalk model. The chart inclusion is the full localization-and-sharpening morphism,
including its structure-sheaf maps. This asserts existence in one chart; it asserts
neither uniqueness nor compatibility between different charts.

Source: ILO VIII 3.1.1--3.1.4, 3.1.8(ii), and 3.1.10(ii), pp.98--100
(blueprint: lem-trf-fine-fan-chart-minimal-affine).

Proof: Write A for the chart monoid, p for its prime, Q for the localization at
A minus p, and B for Q modulo units. The smallest neighborhood is D(s), where s
is the product of generators outside p (`monoidPrime_minimal_neighborhood`).
Extension and contraction identify primes of Q with primes of A contained in p:
a numerator belongs to an extended prime exactly when it belongs to the original
prime, since denominators are units. Quotient by units bijects primes of Q with
primes of B, because ideals are stable under multiplication by units in both
directions. Both bijections carry basic opens to basic opens. The sharpened
localizations of B and Q at corresponding numerators are canonically isomorphic:
send each numerator to its unit class, extend over the inverted elements, then
kill units. The two composites fix every numerator; denominators disappear in
the sharpening. These isomorphisms commute with restriction for the same reason.
Use `affineFan_localization_sections` and `TopCat.Sheaf.restrictHomEquivHom` to
extend them to inverse sheaf maps. Their stalk maps are isomorphisms, hence local.
Identify B with the actual stalk by the canonical chart-stalk equivalence. On
global numerator sections this is exactly the germ map, proving normalization.
The maps back to the A chart send canonical sections to their numerator germs
and contract primes along that homomorphism. They therefore satisfy IsAffineMap;
restriction compatibility proves the displayed equality of sheafed-space maps.
The argument works for the empty prime, the closed prime and the trivial monoid. -/
theorem fineFan_chart_minimal_affine (X : SheafedSpace CommMonCat.{u})
    (hX : ∀ x : X, IsSharp (stalk X.presheaf x))
    (c : Chart X) (z : X) (hc : z ∈ c.openSet)
    (U : Opens X) (hz : z ∈ U)
    (hU : ∀ V : Opens X, z ∈ V → U ≤ V)
    (hP : IsFine (stalk X.presheaf z)) :
    ∃ ι : X.restrict U.isOpenEmbedding ≅ affine (stalk X.presheaf z),
      IsLocalMorphism ι.hom ∧ IsLocalMorphism ι.inv ∧
      (∀ p : stalk X.presheaf z,
        germ X.presheaf U z hz
          ((X.presheaf.map (eqToHom (Opens.isOpenEmbedding_obj_top U).symm).op)
            (affinePullback ι.hom p)) = p) ∧
      ∃ k : affine (stalk X.presheaf z) ⟶ affine c.monoid,
        IsAffineMap
          ((germ X.presheaf c.openSet z hc).hom.comp
            ((X.presheaf.map
              (eqToHom (Opens.isOpenEmbedding_obj_top c.openSet).symm).op).hom.comp
                (affinePullback c.iso.hom))) k ∧
        k ≫ c.iso.inv ≫ X.ofRestrict c.openSet.isOpenEmbedding =
          ι.inv ≫ X.ofRestrict U.isOpenEmbedding := by sorry

end AlgebraicGeometry.FineFan
