/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group T1
-/
module

public import Sheaf.AlgebraicGeometry.SpecLocalRingCanonicalMorphism
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Sheaf.Topology.PresheafModuleStalkFunctor

/-!
# The spectrum of a stalk as a limit of affine neighbourhoods

Source: Stacks Project, Limits of Schemes, proof of Tag 0GWT and Tag 01YW
(blueprint: lem-weil-pbc-local-ring-spec-limit-affine-neighbourhoods).

The inverse system is written with its objects and inclusion maps. Its limit property
is the unique-factorization property for every compatible family, in the category of schemes.
-/

@[expose] public section

universe u

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry.Scheme

set_option autoImplicit false

/-- Affine neighbourhoods are cofinal and directed, their inclusion maps form an inverse
system with affine transitions and qcqs objects, and `Spec O_{X,x}` is its limit.
Source: Stacks Project, proof of Tag 0GWT and Tag 01YW
(blueprint: lem-weil-pbc-local-ring-spec-limit-affine-neighbourhoods).

Proof, following the seven steps of the node:
1. The affine-open basis (`lem-weil-pbc-affine-opens-basis`) gives an affine neighbourhood
inside any open containing `x`. Apply it to the whole space and to intersections for
nonemptiness and directedness. The inclusion maps are open immersions and preserve
identities and compositions (`def-weil-open-immersion`).
2. Affine schemes are qcqs (`lem-weil-pbc-affine-scheme-qcqs`); morphisms between affine
schemes are affine (`lem-weil-pbc-morphism-affine-schemes-affine`).
3. The canonical map has image the generalizations of `x`
(`lem-weil-pbc-spec-local-ring-canonical-morphism`), so it factors uniquely through every
neighbourhood (`lem-weil-pbc-morphism-factors-through-open-subscheme`). Uniqueness gives
compatibility of these factorizations with inclusions.
4. The stalk is the colimit of sections over affine neighbourhoods: every stalk element
is a germ on one of these opens, and equality of germs is equality on a smaller affine
neighbourhood (`lem-weil-pbc-stalk-germs-on-basis`, `lem-weil-pbc-affine-opens-basis`).
Define a map from the stalk to any ring cocone on germs; equality on smaller opens makes
it well-defined. Common smaller opens show it preserves ring operations, and germs
exhaust the stalk, giving uniqueness (`def-weil-pbc-category-colimit`).
5. Taking spectra gives a scheme limit (`lem-weil-pbc-spec-colimit-limit`, Tag 01YW).
6. Identify each affine open with the spectrum of its sections
(`lem-weil-pbc-affine-open-spec-points`). These identifications commute with inclusions
(`lem-weil-pbc-affine-open-inclusion-spec-map`); cancel the open immersions, which are
monomorphisms (`lem-weil-pbc-open-immersion-monomorphism`). Transport the limit property.
7. The germ map is the localization map under the affine stalk identification
(`lem-weil-pbc-affine-open-stalk-localization`). The canonical map's affine description
(`lem-weil-pbc-spec-local-ring-canonical-morphism`) identifies the resulting projections
with the unique factorizations from step 3. This gives exactly the stated universal property. -/
theorem fromSpecStalk_limit_affine_neighbourhoods (X : Scheme.{u}) (x : X) :
    (∀ (U : X.Opens), x ∈ U →
      ∃ W : X.Opens, IsAffineOpen W ∧ x ∈ W ∧ W ≤ U) ∧
    Nonempty {W : X.Opens // IsAffineOpen W ∧ x ∈ W} ∧
    (∀ (W V : {W : X.Opens // IsAffineOpen W ∧ x ∈ W}),
      ∃ Z : {W : X.Opens // IsAffineOpen W ∧ x ∈ W}, Z.1 ≤ W.1 ⊓ V.1) ∧
    (∀ W : {W : X.Opens // IsAffineOpen W ∧ x ∈ W},
      X.homOfLE (le_refl W.1) = 𝟙 W.1.toScheme) ∧
    (∀ (W V Z : {W : X.Opens // IsAffineOpen W ∧ x ∈ W})
      (hZV : Z.1 ≤ V.1) (hVW : V.1 ≤ W.1),
      X.homOfLE hZV ≫ X.homOfLE hVW = X.homOfLE (hZV.trans hVW)) ∧
    (∀ W : {W : X.Opens // IsAffineOpen W ∧ x ∈ W},
      CompactSpace W.1.toScheme ∧ QuasiSeparatedSpace W.1.toScheme) ∧
    (∀ (W V : {W : X.Opens // IsAffineOpen W ∧ x ∈ W}) (hVW : V.1 ≤ W.1),
      IsOpenImmersion (X.homOfLE hVW) ∧ IsAffineHom (X.homOfLE hVW)) ∧
    (∀ (U : X.Opens) (hxU : x ∈ U),
      ∃! g : Spec (X.presheaf.stalk x) ⟶ U.toScheme, g ≫ U.ι = X.fromSpecStalk x) ∧
    (∀ (W V : {W : X.Opens // IsAffineOpen W ∧ x ∈ W}) (hVW : V.1 ≤ W.1),
      V.1.fromSpecStalkOfMem x V.2.2 ≫ X.homOfLE hVW =
        W.1.fromSpecStalkOfMem x W.2.2) ∧
    (∀ (T : Scheme.{u})
      (tW : ∀ W : {W : X.Opens // IsAffineOpen W ∧ x ∈ W}, T ⟶ W.1.toScheme),
      (∀ (W V : {W : X.Opens // IsAffineOpen W ∧ x ∈ W}) (hVW : V.1 ≤ W.1),
        tW V ≫ X.homOfLE hVW = tW W) →
      ∃! t : T ⟶ Spec (X.presheaf.stalk x),
        ∀ W : {W : X.Opens // IsAffineOpen W ∧ x ∈ W},
          t ≫ W.1.fromSpecStalkOfMem x W.2.2 = tW W) := by
  sorry

end AlgebraicGeometry.Scheme
