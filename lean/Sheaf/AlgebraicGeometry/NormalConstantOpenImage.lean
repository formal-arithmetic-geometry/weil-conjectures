/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NR
-/
module

public import WeilConjectures.AlgebraicGeometry.NormalScheme
public import WeilConjectures.ConstructibleSheaf.Defs
import WeilConjectures.AlgebraicGeometry.NormalConstantOpenUnit

/-!
# A constant module sheaf across a nonempty normal open

Source: the blueprint, `sec-smooth-purity/sk-prop-a1-kummer`, order 1906;
Stacks Project, Tag 09Z5, assertion (2) (blueprint: lem-fin-normal-constant-open-image).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Etale

/-- The canonical map from a finite constant module sheaf on a Noetherian normal integral
scheme to the direct image of the same constant sheaf on a nonempty open is an isomorphism.
The displayed map is the inverse-image/direct-image unit followed by direct image of the
canonical pullback-of-constants comparison; it sends each constant section to the section
with the same value.

Source: the blueprint, `sec-smooth-purity/sk-prop-a1-kummer`, order 1906;
Stacks Project, Tag 09Z5, assertion (2) (blueprint: lem-fin-normal-constant-open-image).

Proof: write F for the constant sheaf with value M. By `def-sbc-normal-dominant-galois`,
normality gives integrally closed stalk rings, and integrality is the hypothesis of
`lem-weil-pbc-normal-constant-generic-open-unit`. Apply that theorem to the nonempty open
immersion v: its adjunction unit at F is an isomorphism. This theorem holds for arbitrary
modules and does not need Noetherianity, so it applies to the finite module here.
By `lemma-constructible-pullback-constant`, the canonical comparison v^* F to the constant
sheaf with value M on V is an isomorphism. It is defined by the uniqueness of left adjoints
to global sections: the adjunction bijections identify its adjoint with the map sending
m to the constant section m. Thus the displayed composite is exactly the canonical map
of the statement. By `def-weil-pbc-direct-image`, direct image is a functor and carries
the comparison and its inverse to inverse morphisms. The inverse of the composite is
the inverse direct-image comparison followed by the inverse adjunction unit. -/
theorem isIso_constantSheaf_to_open_lowerStar
    (Λ : Type (u + 1)) [CommRing Λ] {Y V : Scheme.{u}} [IsNoetherian Y]
    [IsIntegral Y] (hY : IsNormalScheme Y) (v : V ⟶ Y) [IsOpenImmersion v]
    [Nonempty V] (M : ModuleCat.{u + 1} Λ) [Finite M] :
    IsIso
      (((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) v).unit.app
          ((constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M)) ≫
        (lowerStar (ModuleCat.{u + 1} Λ) v).map
          ((Scheme.upperStarConstantSheafIso (ModuleCat.{u + 1} Λ) v).app M).hom) := by
  have hY' : ∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y) := by
    intro y
    exact (hY.2 y).2
  have : IsIso ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) v).unit.app
      ((constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M)) :=
    isIso_unit_constantSheaf_open_unit Λ hY' M v
  infer_instance

end AlgebraicGeometry.Etale
