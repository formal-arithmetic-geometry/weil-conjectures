/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q06
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties
public import Sheaf.AlgebraicGeometry.RelativeFiniteHilbertGroupoids
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceOpenSubspace
public import Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
import Sheaf.AlgebraicGeometry.SpaceEtalePresentationPropertyCriterion
import Sheaf.AlgebraicGeometry.AlgebraicSpaceEtaleOpenImage
import Sheaf.AlgebraicGeometry.AlgebraicSpaceOpenFactorSchemeTests
import Sheaf.AlgebraicGeometry.AlgebraicSpacePointOpenCalculus
import Sheaf.AlgebraicGeometry.SchemeEtaleSourceTargetProperties
import Mathlib.AlgebraicGeometry.Morphisms.Etale

/-! # The relative local-complete-intersection locus in the source

Source: Stacks Project, More on Morphisms of Spaces, Tags 06C4 and 06CA
(blueprint: lem-sfb-space-relative-lci-source-locus).

The existing `RelativeFiniteHilbert.SchemeLci` uses finite Koszul-regular sequences,
including the empty sequence. Its existing `SpaceProperty` applies that property on
compatible surjective étale scheme charts. Restriction to an open subspace is composition
with its subfunctor inclusion. Base changes are expressed by arbitrary representing
pullback squares; the two compatibility equations uniquely characterize the induced map.
Equality of open subspaces is equality of their underlying subfunctors.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace

/-- The source lci locus of a relative map of flat locally finitely presented families
is an open subspace, is itself an lci restriction, detects global lci, and commutes with
every algebraic-space base change. The base-changed lci criterion is also expressed as
containment of the point image of `A' → A` in the original locus. Pullback squares and their
compatibility equations specify precisely the base-changed map, without choosing atlases.

Source: Stacks Project, More on Morphisms of Spaces, Tag 06CA
(lemma-base-change-lci-fibres), with the pointwise convention of Tag 06C4
(definition-lci) (blueprint: lem-sfb-space-relative-lci-source-locus).

Proof:
1. The scheme lci property is étale local on source-and-target by
   lem-sfb-scheme-lci-etale-locality. The presentation criterion
   lem-sfb-space-etale-presentation-property-criterion therefore identifies lci at a
   scheme-chart point with lci at its image. In the reverse direction use the open image
   of a good source neighbourhood (lem-a1-space-etale-open-image), factor through it
   (lem-a1-space-open-factor-scheme-tests), and descend along the surjective étale chart.
   Open-immersion composition is lem-weil-pbc-etale-composition-cancellation.
2. Take the union of all source opens on which the map is lci. The point/open calculus
   lem-a1-space-point-open-calculus and open-subspace correspondence of
   lem-a1-space-etale-open-image give its unique open subspace. Source-locality of scheme
   lci and the presentation criterion glue the lci restrictions over this union. Thus its
   restriction is lci, and the whole map is lci exactly when the union is the whole source.
3. Choose an atlas W of B, an atlas V of C times_B W, and an atlas D of A times_C V.
   The fibre-product and cover theorem lem-trf-space-fibre-products-etale-covers and
   étale composition give compatible surjective charts. The structural scheme maps
   D to W and V to W are flat and locally finitely presented, by
   lem-sfb-scheme-etale-source-target-properties and the presentation criterion.
4. For arbitrary B' to B, choose an atlas W' of W times_B B'. The pullbacks D' and V'
   give surjective étale charts of A' and C'. Apply
   lem-sfb-scheme-relative-lci-base-change-points to D to V over W: lci at d' is equivalent
   to lci at its image d. No flatness of the relative map or of B' to B is used.
5. Lift a point of A' to D'. Step 1, then step 4, then step 1 identify its lci condition
   with that of its image in A. Open-subspace pullback and uniqueness give the subfunctor
   equality (lem-a1-space-open-factor-scheme-tests and lem-a1-space-etale-open-image).
   Step 2 and the full-point-image criterion of lem-a1-space-point-open-calculus give
   both final equivalences. All these arguments allow empty sources and empty fibres. -/
theorem relative_lci_source_locus {S : Scheme.{u}} (A C B : AlgebraicSpace S)
    (p : A ⟶ B) (q : C ⟶ B) (u : A ⟶ C) (hu : u ≫ q = p)
    (hp : MapIsFlat p) (hpLfp : MapIsLocallyOfFinitePresentation p)
    (hq : MapIsFlat q) (hqLfp : MapIsLocallyOfFinitePresentation q) :
    ∃ U : OpenSubspace A,
      (∀ x : Point A.obj.obj, x ∈ pointImage U.val.ι ↔
        ∃ N : OpenSubspace A, x ∈ pointImage N.val.ι ∧
          RelativeFiniteHilbert.SpaceProperty
            (fun _ _ f ↦ RelativeFiniteHilbert.SchemeLci f) (N.val.ι ≫ u.hom.hom)) ∧
      RelativeFiniteHilbert.SpaceProperty
        (fun _ _ f ↦ RelativeFiniteHilbert.SchemeLci f) (U.val.ι ≫ u.hom.hom) ∧
      (RelativeFiniteHilbert.SpaceProperty
        (fun _ _ f ↦ RelativeFiniteHilbert.SchemeLci f) u.hom.hom ↔ U.val = ⊤) ∧
      ∀ (B' A' C' : AlgebraicSpace S) (g : B' ⟶ B)
        (a : A' ⟶ A) (c : C' ⟶ C) (p' : A' ⟶ B') (q' : C' ⟶ B') (u' : A' ⟶ C'),
        IsPullback a.hom p'.hom p.hom g.hom →
        IsPullback c.hom q'.hom q.hom g.hom →
        u' ≫ c = a ≫ u → u' ≫ q' = p' →
        ∃ U' : OpenSubspace A',
          (∀ x : Point A'.obj.obj, x ∈ pointImage U'.val.ι ↔
            ∃ N : OpenSubspace A', x ∈ pointImage N.val.ι ∧
              RelativeFiniteHilbert.SpaceProperty
                (fun _ _ f ↦ RelativeFiniteHilbert.SchemeLci f) (N.val.ι ≫ u'.hom.hom)) ∧
          RelativeFiniteHilbert.SpaceProperty
            (fun _ _ f ↦ RelativeFiniteHilbert.SchemeLci f) (U'.val.ι ≫ u'.hom.hom) ∧
          U'.val = U.val.preimage a.hom.hom ∧
          (RelativeFiniteHilbert.SpaceProperty
            (fun _ _ f ↦ RelativeFiniteHilbert.SchemeLci f) u'.hom.hom ↔
              U.val.preimage a.hom.hom = ⊤) ∧
          (RelativeFiniteHilbert.SpaceProperty
            (fun _ _ f ↦ RelativeFiniteHilbert.SchemeLci f) u'.hom.hom ↔
              pointImage a.hom.hom ⊆ pointImage U.val.ι) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
