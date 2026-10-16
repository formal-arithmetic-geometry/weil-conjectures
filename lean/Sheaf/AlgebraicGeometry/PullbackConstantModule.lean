/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NM
-/
module

public import Mathlib.Algebra.Homology.Additive
public import WeilConjectures.ConstructibleSheaf.Defs
import Mathlib.CategoryTheory.Sites.Sheafification
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Stalk
import WeilConjectures.AlgebraicGeometry.ConstantSheafGeometricStalk
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs

/-!
# Inverse image of constant modules and complexes

Source: Weil conjectures blueprint, `sec-smooth-purity`, `sk-prop-sf-kunneth-ordinary`,
lemma `lem-kun-pullback-constant` (blueprint: lem-kun-pullback-constant).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- The canonical inverse-image comparison is an isomorphism for constant module sheaves
and for their termwise constant complexes, without a boundedness assumption.
Source: Weil conjectures blueprint, `sec-smooth-purity`, `sk-prop-sf-kunneth-ordinary`,
lemma `lem-kun-pullback-constant` (blueprint: lem-kun-pullback-constant).

Proof:
1. Send each coefficient to its constant section after base change. The direct-image
   formula (def-weil-pbc-direct-image) and sheafification universal property
   (def-weil-pbc-sheafification) give a map to the pushforward of the constant sheaf.
   Its adjoint (def-weil-pbc-inverse-image) is the canonical comparison, natural in the
   module. This is the hom of the existing `upperStarConstantSheafIso`.
2. At a geometric point, the pullback-stalk comparison (lemma-openclosed-stalk-upperstar)
   identifies the source stalk with the constant stalk at the image point. The constant
   germ isomorphisms (lem-weil-pbc-constant-sheaf-geometric-stalk) identify both stalks
   with the coefficient module. The comparison sends each constant germ to itself.
3. Geometric stalk conservativity (lemma-weil-pbc-geometric-stalk-conservative) makes
   the comparison invertible. Naturality in scalar multiplication makes it and its
   inverse linear, including for local scalars by the sheaf axiom.
4. Apply the comparison in every degree (def-kun-constant-sheaf). Naturality for the
   differentials makes it a chain map; the degreewise inverses also commute with the
   differentials and give its inverse. This applies to arbitrary unbounded complexes.
-/
theorem pullback_constantModule_isIso {X Y : Scheme.{u}} (f : X ⟶ Y)
    (Λ : Type (u + 1)) [CommRing Λ] :
    (∀ M : ModuleCat.{u + 1} Λ,
      IsIso ((upperStarConstantSheafIso (ModuleCat.{u + 1} Λ) f).hom.app M)) ∧
    (∀ M : CochainComplex (ModuleCat.{u + 1} Λ) ℤ,
      IsIso (((upperStarConstantSheafIso (ModuleCat.{u + 1} Λ) f).hom.mapHomologicalComplex
        (ComplexShape.up ℤ)).app M)) := by
  sorry

end AlgebraicGeometry.Scheme
