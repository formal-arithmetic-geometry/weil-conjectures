/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q38
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties
public import Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
public import Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace

import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.AffineImmersion
import WeilConjectures.AlgebraicGeometry.ChowLemma.ClosedModel
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Sheaf.AlgebraicGeometry.FlatValuationLifting
import Mathlib.AlgebraicGeometry.ValuativeCriterion
import Sheaf.AlgebraicGeometry.ReducedClosedSubspaceSupport

/-! # Weak Chow lemma for algebraic spaces

Source: Stacks Project, Cohomology of Spaces, Tag 089J (lemma-weak-chow);
Morphisms, Tag 01VW; Morphisms of Spaces, Tag 03MH
(blueprint: lem-sfb-space-weak-chow).

All spaces are over the terminal scheme `Spec (ULift ℤ)`. The scheme source is retained
by its actual Yoneda algebraic space. Projective space uses `n + 1` homogeneous coordinates.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace

/-- A separated finite-type algebraic space over an affine scheme admits a proper,
universally surjective cover by a quasi-compact separated scheme with a quasi-compact
immersion into finite-dimensional projective space over that affine scheme.
Source: Stacks Project, Tag 089J; Tag 01VW(2); Tag 03MH
(blueprint: lem-sfb-space-weak-chow).

Proof:
1. Choose an affine surjective etale atlas W -> X by lem-sfb-qc-space-affine-etale-atlas.
   Finite type over the affine base gives quasi-compactness. By
   lem-sfb-space-etale-maximum-degree the atlas is finite type over the base and its
   geometric fibres have a finite bound. Induct strongly on that bound. Bound zero
   forces X empty; use the empty closed subscheme of projective zero-space. Otherwise
   choose the least positive bound d and its nonempty maximum-degree open U.
2. Embed W in projective space by lem-chow-affine-immersion. The immersion is
   quasi-compact since its affine-chart factor is closed and the standard chart is
   quasi-compact in separated projective space. By lem-chow-closed-model take its
   schematic closure Y, with W open in Y. Apply lem-sfb-space-chow-configuration:
   it gives V contained in H contained in Z, proper projections g_i : Z -> Y and
   p : H -> X, with V quasi-compact dense open in H, p separated finite type,
   H quasi-compact with a quasi-compact projective-space immersion, and p(V) = U.
3. In a valuation square Spec K -> V over Spec R -> X, the pullback of W is a scheme
   etale and surjective over Spec R by lem-trf-space-fibre-products-etale-covers.
   It is flat by def-weil-etale-morphism. Apply lem-a1-flat-valuation-lifting at the
   closed point to lift to W after an injective local valuation-ring extension R -> R'.
   Coordinate completeness in lem-sfb-space-chow-configuration identifies the generic
   lift with one of the d coordinates, say i, over the fraction field of R'.
4. Properness of g_i and lemma-nagata-proper-valuative-criterion-existence-api extend
   that coordinate to Spec R' -> Z. Its image lies in g_i^{-1}(W), hence in H, where
   p = f g_i. This solves the original valuation square after extension. To apply
   lem-sfb-space-dense-open-valuative-proper, check affine-test quasi-compactness of
   p and V -> H using lem-sfb-space-qcqs-permanence: H and V are quasi-compact,
   H is a separated scheme, and X is absolutely quasi-separated since its closed
   relative diagonal over the affine base factors its absolute diagonal through the
   pullback of the base's closed diagonal. Thus p is proper.
5. By lem-sfb-space-reduced-closed-support let T be the reduced closed complement of U.
   Its inclusion is proper by lem-sfb-space-closed-subspace-proper. Its map to the
   affine base is separated finite type: diagonals restrict and affine algebras are
   quotients of finite-type algebras; its support is closed in quasi-compact X.
   The affine atlas of T has fibre bound d - 1 by lem-sfb-space-etale-maximum-degree.
   Induction gives a proper surjective quasi-projective scheme cover T' -> T;
   its composite to X is proper by lem-sfb-space-proper-composition.
6. Take X' = H disjoint union T'. The union map is proper: its diagonal is closed
   on matching components and empty on cross components; finite type follows from
   its two finite-type open pieces; every base change is closed since images of
   closed sets are finite unions of closed images. X' is quasi-compact separated.
   Its image contains U from H and the complement from T', so it is surjective.
7. Embed the ambient projective spaces of H and T' as complementary coordinate
   linear subspaces in projective (r+s+1)-space. They are closed and disjoint since
   all coordinates cannot vanish at a projective point. Their union is their scheme
   disjoint union. The two quasi-compact immersions therefore combine to the required
   quasi-compact immersion j over the base, giving a pi = q j. Empty components
   are omitted.
8. For any W -> X and any point of W, surjectivity chooses a point of X' over its
   image. The field-valued point equivalence of lem-trf-space-fibre-products-etale-covers
   gives representatives over a common field with equal maps to X. They determine
   a point of the sheaf pullback over the original point of W. Thus every pullback
   projection is surjective on point classes, without representability of W -> X. -/
theorem exists_proper_surjective_quasiProjective_scheme_cover
    (A : Type u) [CommRing A]
    (X : AlgebraicSpace (Spec (CommRingCat.of (ULift.{u} ℤ))))
    (a : X ⟶ schemeSpace (Over.mk (specULiftZIsTerminal.from (Spec (.of A)))))
    (ha_sep : MapIsSeparated a) (ha_ft : MapIsFiniteType a) :
    ∃ (n : ℕ) (X' : Over (Spec (CommRingCat.of (ULift.{u} ℤ))))
      (π : schemeSpace X' ⟶ X)
      (j : X'.left ⟶ ProjectiveSpace (ULift.{u} (Fin (n + 1))) (Spec (.of A))),
      CompactSpace X'.left ∧ X'.left.IsSeparated ∧ MapIsProper π ∧
      IsImmersion j ∧ QuasiCompact j ∧
      π.hom.hom ≫ a.hom.hom =
        yoneda.map (Over.homMk
          (j ≫ (ProjectiveSpace (ULift.{u} (Fin (n + 1))) (Spec (.of A)) ↘ Spec (.of A)))
          (specULiftZIsTerminal.hom_ext _ _)) ∧
      ∀ (W : AlgebraicSpace (Spec (CommRingCat.of (ULift.{u} ℤ)))) (w : W ⟶ X),
        pointImage (Limits.pullback.snd π.hom w.hom).hom = Set.univ := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
