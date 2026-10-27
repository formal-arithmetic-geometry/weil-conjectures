/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q110
-/
module

public import Sheaf.AlgebraicGeometry.SpaceUniversalRelativePurity
public import Sheaf.AlgebraicGeometry.SpaceDimensionFlatCondition
import Sheaf.AlgebraicGeometry.EtaleSheafSpaceAtlasBootstrap
import Sheaf.AlgebraicGeometry.AlgebraicSpaceFlatProperFpLocality
import Sheaf.AlgebraicGeometry.EtaleSchemeMapOpenImage
import Sheaf.AlgebraicGeometry.AffineCompleteDevissageDimensionFlattening

/-! # Representability of dimension-filtered flatness for a universally pure module

Source: Stacks Project, spaces-flat.tex, Tag 0CX1, specialized to a scheme base
and universal relative purity; Tags 0CWS and 0CWT for the chart criterion
(blueprint: lem-sfb-space-pure-dimension-flatness-representability).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.AlgebraicSpace

/-- The dimension-n flatness subfunctor of the scheme base is an algebraic space
whose map to the base is a monomorphism of finite presentation. Here `hf`, `hlfp`
and `hqs` together express finite presentation: finite type includes quasi-compactness,
local finite presentation implies local finite type, and `hqs` is the quasi-compact
relative diagonal. The finite-type witness also supplies the recorded purity interface.
The finite-presentation module instance supplies its finite-type witness.
Injectivity and the section-lift equivalence express the bijection onto precisely P_n.

Source: Stacks Project, spaces-flat.tex, Tag 0CX1; Tags 0CWS and 0CWT
(blueprint: lem-sfb-space-pure-dimension-flatness-representability).

Proof:
1. By lem-sfb-space-dimension-flatness-base-change-sheaf, each P_r defines an
   fpqc, hence etale, subfunctor F_r of h_Y. The inequalities give F_r ⊆ F_(r+1).
   Iterated tensor pullback and sheaf fibre products identify its restrictions.
2. Glue local scheme representatives of an etale subfunctor H of a space A:
   their disjoint union is an etale surjective atlas, since its pullback by a
   section of H is the pullback of the chosen covering of A. Apply
   lem-sfb-etale-sheaf-space-atlas-bootstrap and
   lem-trf-space-fibre-products-etale-covers. Finite presentation descends by
   lem-sfb-space-flat-proper-fp-locality; injectivity is that of the subfunctor.
3. Work on affine opens of Y. The universal bound D from
   lem-sfb-space-universal-fibre-transcendence-bound gives F_(D+1) = h_Y.
   Descend on r. If F_(r+1) is represented by A, represent F_r over A and compose
   using lem-sfb-space-separated-fp-composition.
4. On affine etale charts of A the pulled-back family remains finitely presented
   and universally pure, and satisfies P_(r+1) universally, by purity's definition,
   finite-presentation locality and the base-change theorem of step 1.
5. At t choose the finite complete-devissage etale fibre neighbourhood supplied
   by lem-sfb-space-complete-devissage-fibre-neighbourhood. Its charts W_j cover
   the whole fibre; their open image W is quasi-compact by
   lem-a1-etale-scheme-map-open-image. Apply
   lem-sfb-affine-complete-devissage-dimension-flattening to these original charts,
   obtaining representatives near t for each P_r before any further shrinking.
6. Universal purity specializes every associated point above a generalization of
   t into that fibre, hence into W. By
   lem-sfb-space-assassin-containment-constructible there is an open neighbourhood
   of t where W contains the relative assassin. Shrink inside it and all the
   finitely many neighbourhoods of step 5; restrict their representatives.
7. By lem-sfb-space-dimension-flatness-assassin-localization, P_r on every test
   is the conjunction of P_r for the W_j. A point of the finite disjoint union
   lies in one component with the same stalk and residue fields.
8. The finite fibre product of the representatives from step 5 represents that
   conjunction. Base change and composition preserve finite presentation, and
   unique lifts preserve monicity. An empty family is represented by the base.
9. Glue by step 2 and compose to complete the descending induction; larger r
   have vacuous criteria by D. Glue over the affine opens of Y. Set r = n.
   Its sections are exactly the maps satisfying P_n, with a unique lift. -/
theorem exists_pure_dimension_flatness_representative
    {X : AlgebraicSpace (Spec (CommRingCat.of (ULift.{u} ℤ)))}
    (Y : Over (Spec (CommRingCat.of (ULift.{u} ℤ)))) (f : X ⟶ schemeSpace Y)
    (hf : MapIsFiniteType f) (hlfp : MapIsLocallyOfFinitePresentation f)
    (hqs : MapIsQuasiCompact (pullback.diagonal f.hom.hom))
    (M : X.QCoh) [hM : SheafOfModules.IsFinitePresentation M.obj]
    (hpure : IsUniversallyPureRelativeToScheme Y f hf hqs M inferInstance) (n : ℕ) :
    ∃ (E : AlgebraicSpace (Spec (CommRingCat.of (ULift.{u} ℤ))))
      (j : E ⟶ schemeSpace Y),
      (MapIsLocallyOfFinitePresentation j ∧ MapIsQuasiCompact j.hom.hom ∧
        MapIsQuasiCompact (pullback.diagonal j.hom.hom)) ∧
      (∀ B : Over (Spec (CommRingCat.of (ULift.{u} ℤ))),
        Function.Injective (j.hom.hom.app (op B))) ∧
      ∀ (B : Over (Spec (CommRingCat.of (ULift.{u} ℤ)))) (b : B ⟶ Y),
        (∃ e : E.obj.obj.obj (op B), j.hom.hom.app (op B) e = b) ↔
          dimensionFlatCondition f M.obj n b := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
