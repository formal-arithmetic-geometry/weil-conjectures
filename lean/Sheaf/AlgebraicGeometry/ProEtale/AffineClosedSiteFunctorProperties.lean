/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NA
-/
module

public import Sheaf.AlgebraicGeometry.ProEtale.ClosedSiteLift
public import Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory
public import Sheaf.CategoryTheory.SpecialCocontinuousCoverings
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Sheaf.RingTheory.ProEtale.ClosedLiftMap
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Sheaf.RingTheory.IndPrincipalZariski
import WeilConjectures.AlgebraicGeometry.ProEtale.Comparison.Affine
import Sheaf.RingTheory.ProEtale.ClosedLiftAdjunction
import WeilConjectures.RingTheory.ProEtale.ClosedLift
import Sheaf.RingTheory.ProEtale.ClosedLiftUnits
import Mathlib.CategoryTheory.Sites.Precoverage
import Mathlib.RingTheory.Ideal.GoingDown
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Sheaf.RingTheory.IndEtaleStability
import Mathlib.RingTheory.Ideal.Maximal
import Sheaf.CategoryTheory.SiteCoveringAxioms
import WeilConjectures.CategoryTheory.SpecialCocontinuousCoverings

/-! # Affine closed-immersion site functor properties

Source: Stacks Project, Tag 09BK, lemma-closed-immersion-affines
(blueprint: lem-weil-pbc-affine-closed-site-functor-properties).

The functors are the recorded `closedSiteBaseChange` and `closedSiteLift`.
The geometric inclusion below is the spectrum of the retained algebra map.
-/

@[expose] public noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.AffineProEt

/-- The canonical map from an affine object of the closed site to its lift.
Source: Stacks Project, Tag 09BK, the map V → v(V)
(blueprint: lem-weil-pbc-affine-closed-site-functor-properties). -/
def closedSiteLiftInclusion (A : Type u) [CommRing A] (I : Ideal A)
    (V : (Spec (.of (A ⧸ I))).AffineProEt) :
    V.left ⟶ ((closedSiteLift A I).obj V).left :=
  V.left.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom
    (Algebra.ClosedLift.toAlgHom A (closedSiteCoordinates A I V)).toRingHom)

/-- The affine closed-site lift is a fully faithful cocontinuous left adjoint,
preserves covering families, and contains its input as its closed fibre, with every
point specializing to that fibre.
Source: Stacks Project, Tag 09BK, lemma-closed-immersion-affines
(blueprint: lem-weil-pbc-affine-closed-site-functor-properties).

Proof plan:
1. Base change preserves ind-etale algebras by lem-weil-pbc-ind-etale-stability.
   The indexing category for H_A(C) is filtered by lem-exc-closed-lift-filtered;
   its etale terms give an ind-etale colimit. Postcomposition gives the lift's
   functor laws; pullback functoriality gives those of base change.
2. The natural Hom bijections of lem-exc-closed-lift-adjunction, reversed by Spec,
   give the adjunction. By lem-exc-closed-lift-reduction its unit is invertible;
   this gives full faithfulness. The retained algebra map is surjective with
   quotient H_A(C)/I H_A(C) = C, giving the asserted closed pullback square.
3. An affine fpqc covering has a finite jointly surjective subfamily. Conversely,
   finite jointly surjective weakly etale affine families are fpqc: refine affine
   target opens by principal opens and use the unit-ideal finite subcover argument
   (lem-weil-pbc-proper-ideal-contained-in-maximal). This includes empty covers.
4. Fpqc coverings survive base change by lem-galois-fpqc-covering-base-change.
   Canonical associativity of fibre products gives preservation of pullbacks of
   covering arrows, so u is continuous in the sense of Stacks 00WV.
5. A prime of H_A(C) is contained in a maximal ideal. By lem-exc-closed-lift-units,
   every 1-b for b in I H_A(C) is a unit. Thus every maximal ideal contains this
   ideal, giving a specialization in the closed fibre; the zero ring is vacuous.
6. Lift a finite jointly surjective subfamily. Its maps are weakly etale and flat
   by ind-etale stability and lem-weil-pbc-flat-ring-map-iff-flat-affine. Every
   target point specializes into the closed fibre. A lift there generalizes to
   a point above the original point by lem-sc-flat-going-down. Hence the lifted
   family is jointly surjective, and step 3 shows it is a covering.
7. For a cover of v(V), apply u and identify uv(V) with V using the unit. This
   gives a covering of V. The counit maps from the lifted covering into the
   original cover commute over v(V) by naturality and the triangle identity.
   This is the refinement required for cocontinuity (Stacks 00XJ). -/
theorem affine_closed_site_functor_properties (A : Type u) [CommRing A] (I : Ideal A) :
    (∀ (U : (Spec (.of A)).AffineProEt) (R : Presieve U),
      R ∈ precoverage U →
      R.map (closedSiteBaseChange A I) ∈ precoverage ((closedSiteBaseChange A I).obj U)) ∧
    (∀ (U T W : (Spec (.of A)).AffineProEt) (R : Presieve U),
      R ∈ precoverage U →
      ∀ (f : T ⟶ U) (g : W ⟶ U), R f →
        PreservesLimit (cospan f g) (closedSiteBaseChange A I)) ∧
    (closedSiteLift A I).Full ∧
    (closedSiteLift A I).Faithful ∧
    (closedSiteLift A I).IsCocontinuous
      (topology (Spec (.of (A ⧸ I)))) (topology (Spec (.of A))) ∧
    Nonempty (closedSiteLift A I ⊣ closedSiteBaseChange A I) ∧
    (∀ (V : (Spec (.of (A ⧸ I))).AffineProEt) (R : Presieve V),
      R ∈ precoverage V →
      R.map (closedSiteLift A I) ∈ precoverage ((closedSiteLift A I).obj V)) ∧
    (∀ V : (Spec (.of (A ⧸ I))).AffineProEt,
      IsClosedImmersion (closedSiteLiftInclusion A I V) ∧
      IsPullback (closedSiteLiftInclusion A I V) V.hom
        ((closedSiteLift A I).obj V).hom
        (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) ∧
      ∀ x : ((closedSiteLift A I).obj V).left,
        ∃ z : V.left, x ⤳ (closedSiteLiftInclusion A I V) z) := sorry

end AlgebraicGeometry.Scheme.AffineProEt
