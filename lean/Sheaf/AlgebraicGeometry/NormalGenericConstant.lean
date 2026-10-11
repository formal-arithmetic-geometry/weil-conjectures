/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E1
-/
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.ResidueField
import Sheaf.AlgebraicGeometry.NormalScheme
import WeilConjectures.ConstructibleSheaf.Defs

/-!
# Constant abelian sheaves at the generic point of a normal scheme

Source: smooth purity blueprint, unit `sk-prop-sf-cbc`, node
`lem-fin-normal-generic-constant`, order 1606 (blueprint: lem-fin-normal-generic-constant).
-/

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- On a normal integral Noetherian scheme, the natural map from a finite constant abelian
sheaf to its direct image from the generic point is an isomorphism.
Source: smooth purity blueprint, `sk-prop-sf-cbc`, order 1606
(blueprint: lem-fin-normal-generic-constant).

Proof: Evaluate on affine etale objects over affine opens of the base; these form a basis.
Such objects are Noetherian. By `lem-fin-etale-normal-components`, each is a finite disjoint
union of normal integral open-and-closed affine components. Each nonempty component dominates
the base because an etale morphism is open (`lem-weil-pbc-flat-lfp-open`). Flatness embeds the
nonzero elements of the base domain into each component domain. By
`lem-weil-pbc-generic-fibre-localization-domain-irreducible`, its generic fibre is nonempty
and connected. Thus base change to the generic point preserves the finite set of components.
By `lem-weil-pbc-constant-sheaf-sections-connected`, both section groups are the product of
one copy of the coefficient group per component, and restriction is the identity on each
factor. The direct image evaluates on these generic fibres (`def-weil-pbc-direct-image`).
Consequently the natural map is an isomorphism on the basis, hence an isomorphism of sheaves.
The displayed map is the adjunction unit followed by pushforward of the canonical
identification of the pullback of a constant sheaf with the constant sheaf. -/
theorem Etale.isIso_constantSheaf_to_generic_lowerStar
    (V : Scheme.{u}) [IsNoetherian V] [IsIntegral V] (hV : IsNormalScheme V)
    (M : AddCommGrpCat.{u + 1}) [Finite M] :
    IsIso
      (((Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1}
          (V.fromSpecResidueField (genericPoint V))).unit.app
          ((constantSheaf V.smallEtaleTopology AddCommGrpCat.{u + 1}).obj M)) ≫
        (Etale.lowerStar AddCommGrpCat.{u + 1}
          (V.fromSpecResidueField (genericPoint V))).map
          ((Scheme.upperStarConstantSheafIso AddCommGrpCat.{u + 1}
            (V.fromSpecResidueField (genericPoint V))).app M).hom) := by
  sorry

end AlgebraicGeometry
