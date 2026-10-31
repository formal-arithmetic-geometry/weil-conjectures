/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Noetherian
public import WeilConjectures.AlgebraicGeometry.ReducedNormalization
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.Integral
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.ResidueField
import Mathlib.RingTheory.Ideal.GoingDown
import WeilConjectures.AlgebraicGeometry.EtaleSmoothZeroDimensionalFibres

/-!
# Componentwise normalization and smooth pullback

Source: Stacks Project, More on Morphisms, Tag 07TD, lemma-normalization-and-smooth
(blueprint: lem-sfb-componentwise-normalization-smooth-pullback).

The locally Noetherian specialization includes nonreduced and empty schemes, and assumes
neither excellence nor finiteness of normalization.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- Componentwise normalization commutes uniquely with smooth pullback, over the source.
Source: Stacks Project, More on Morphisms, Tag 07TD, lemma-normalization-and-smooth
(blueprint: lem-sfb-componentwise-normalization-smooth-pullback).

Proof:
1. Set P = X ×_Y Y^ν, with projections p to X and q to Y^ν. By
   lem-sfb-componentwise-normalization-generic-properties, Y^ν is normal, its map to Y
   is integral, bijective on generic points, and has the residue-field spectrum as fibre
   at each generic point of Y. The hypothesis holds because Y is locally Noetherian.
   By lem-sbc-integral-morphism-base-change, p is integral.
2. By lem-pc-proper-base-change, q is smooth. Apply lem-sfb-smooth-normal-ascent to
   conclude P is normal. By lem-pc-smooth-flat, f and q are flat. These results require
   no local Noetherianity of P or Y^ν.
3. Generic points map to generic points under f and q: def-weil-flat-morphism gives
   flat local-ring maps, and lem-sc-flat-going-down lifts any hypothetical strictly
   smaller prime below the maximal ideal to below the unique prime of the local ring
   at a generic source point, a contradiction.
4. For generic η of Y, the generic-fibre identification in step 1 gives P_η ≅ X_η.
   For generic ξ of X, f(ξ) is such an η, and further base change gives
   P ×_X Spec κ(ξ) ≅ Spec κ(ξ). Thus there is exactly one point over ξ, with the same
   residue field (def-weil-residue-field), and that point is generic because every
   generalization lies in the same singleton fibre. Conversely, a generic point of P
   maps to a generic η of Y; the isomorphism P_η ≅ X_η makes its image generic in X_η.
   Every generalization in X still lies over η, so its image is generic in X. The
   generalization assertions follow on affines from localization at a minimal prime.
   Hence p is bijective on generic points and induces residue-field isomorphisms.
5. Apply lem-sfb-integral-normal-generic-recognition to p, using local Noetherianity
   of X, integrality of p, normality of P, and step 4. This gives the unique isomorphism
   P ≅ X^ν over X. Inversion gives the asserted unique isomorphism in the other
   direction. Empty schemes have vacuous generic-point conditions; residue fields
   keep the argument valid without reducedness. No finite-normalization assumption
   has been used. -/
theorem reducedNormalization_smooth_pullback {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsLocallyNoetherian X] [IsLocallyNoetherian Y] [Smooth f] :
    ∃! e : X.reducedNormalization ≅ pullback f Y.fromReducedNormalization,
      e.hom ≫ pullback.fst f Y.fromReducedNormalization = X.fromReducedNormalization := by
  sorry

/-- The same unique normalization isomorphism for an étale morphism.
Source: Stacks Project, More on Morphisms, Tag 07TD, lemma-normalization-and-smooth
(blueprint: lem-sfb-componentwise-normalization-smooth-pullback).

Proof (step 6 of the node): lem-weil-pbc-etale-smooth-zero-dimensional-fibres says
that an étale morphism is smooth of relative dimension zero, hence smooth in the sense
of def-sbc-smooth-morphisms. Apply reducedNormalization_smooth_pullback. Its uniqueness
and compatibility with the first projection give exactly the same conclusion. -/
theorem reducedNormalization_etale_pullback {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsLocallyNoetherian X] [IsLocallyNoetherian Y] [Etale f] :
    ∃! e : X.reducedNormalization ≅ pullback f Y.fromReducedNormalization,
      e.hom ≫ pullback.fst f Y.fromReducedNormalization = X.fromReducedNormalization := by
  sorry

end AlgebraicGeometry.Scheme
