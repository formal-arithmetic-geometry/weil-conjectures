/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicGeometry.Geometrically.Reduced
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Sheaf.AlgebraicGeometry.MultipointedCurveModification

import WeilConjectures.AlgebraicGeometry.Morphisms.DepthTwoHartogsRestriction
import WeilConjectures.AlgebraicGeometry.Morphisms.NormalDenseOpenIntegralSection
import WeilConjectures.AlgebraicGeometry.FlatInvertibleSectionsTorsionFree
import Sheaf.AlgebraicGeometry.EtaleSmoothZeroDimensionalFibres
import WeilConjectures.RingTheory.FlatLocalDepthFormula
import WeilConjectures.RingTheory.SerreCriterionReduced
import WeilConjectures.RingTheory.SmoothNormalRing
import WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Reduced
import Sheaf.AlgebraicGeometry.Morphisms.NormalApproximationFiniteEtaModification
import Sheaf.TraceFormula.GenericFibrePointsSmooth

/-!
# Geometrically reduced families are eta-normal

Source: Temkin, Stable modification of relative curves, Proposition 3.5.2,
printed pp. 20--21 (blueprint: lem-trf-geometrically-reduced-eta-normal).

## Main definitions and statements

* `IsEtaModification`: a proper modification inducing an isomorphism on the generic fibre.
* `IsEtaNormal`: every finite eta-modification is an isomorphism.
* `geometricallyReduced_etaNormal`: reducedness and eta-normality, including the curve and
  marking of every semistable multipointed curve. Semistability and stable pair modifications
  reuse `MultipointedCurve.IsSemistable` and `MultipointedCurve.Hom.IsStable`.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- An eta-modification is a proper morphism which is an isomorphism on a
schematically dense open and on the generic fibre.  The generic-fibre clause is
expressed by explicit cartesian presentations over the function field.
The two cartesian squares are the generic fibres of the target and source, respectively;
the isomorphism commutes with both their projections, so it is the base change of `f`.
Source: Temkin, §1.2, §3.1 and Proposition 3.5.2
(blueprint: lem-trf-geometrically-reduced-eta-normal). -/
def IsEtaModification {S X X' : Scheme.{u}} [IsIntegral S]
    (p : X ⟶ S) (f : X' ⟶ X) : Prop :=
  IsProper f ∧
    (∃ (U : X.Opens) (V : X'.Opens) (e : V.toScheme ≅ U.toScheme),
      (∀ W : X.Opens, Function.Injective (U.ι.app W)) ∧
        (∀ W : X'.Opens, Function.Injective (V.ι.app W)) ∧
        e.hom ≫ U.ι = V.ι ≫ f) ∧
    (∃ (Xη X'η : Scheme.{u})
      (q : Xη ⟶ Spec S.functionField) (q' : X'η ⟶ Spec S.functionField)
      (i : Xη ⟶ X) (j' : X'η ⟶ X'),
      IsPullback q i (S.fromSpecStalk (genericPoint S)) p ∧
      IsPullback q' j' (S.fromSpecStalk (genericPoint S)) (f ≫ p) ∧
        ∃ e : X'η ≅ Xη, e.hom ≫ i = j' ≫ f ∧ e.hom ≫ q = q')

/-- Eta-normality: every finite eta-modification is an isomorphism.
Source: Temkin, §3.5, Proposition 3.5.2
(blueprint: lem-trf-geometrically-reduced-eta-normal). -/
def IsEtaNormal {S X : Scheme.{u}} [IsIntegral S]
    (p : X ⟶ S) : Prop :=
  ∀ (X' : Scheme.{u}) (f : X' ⟶ X), IsFinite f → IsEtaModification p f → IsIso f

/-- A flat finitely presented family with reduced geometric fibres over a
normal integral qcqs base is reduced and eta-normal.  The same conclusions
apply to both members of every semistable multipointed curve over the base.
Source: Temkin, Stable modification of relative curves, Proposition 3.5.2,
printed pp. 20--21 (blueprint: lem-trf-geometrically-reduced-eta-normal).

Proof plan (the ten steps of the DAG node):
1. Work over an affine base with domain R. For an affine source chart with ring B, the kernel
   of B → B tensor_R Frac(R) is R-torsion, hence zero by flatness. This is
   lem-sc-flat-invertible-sections-torsion-free applied to the structure sheaf. The generic
   fibre embeds in its algebraic-closure scalar extension, which is reduced by the geometric
   fibre hypothesis. Nilpotents therefore vanish in B. Applying this on an affine cover of
   every open also gives injectivity of restriction of functions to the generic fibre.
2. Given a finite eta-modification f, localize on affine opens of the base. Apply
   lem-trf-normal-approximation-finite-eta-modification to descend the finite diagram to a
   normal integral Noetherian affine base with the same flatness, finite presentation,
   geometric reducedness and eta-modification properties. An inverse on this model pulls
   back to the original diagram. Finite presentation implies finite type, and a finite map
   is finite type; lem-weil-pbc-finite-type-over-noetherian makes both total spaces
   Noetherian. In the remaining steps use this model.
3. Set A = f_* O of the source. By def-weil-finite-integral-morphism this is a finite
   quasi-coherent algebra. The kernel and cokernel of O → A are finite modules on each
   Noetherian affine chart. Their supports are closed: if a localization vanishes, one
   element outside the prime annihilates all of a finite set of generators, giving a
   principal neighbourhood of vanishing. Their common complement W is the isomorphism
   locus of f. It contains the generic fibre since f is an isomorphism on that fibre.
4. Choose a common schematically dense isomorphism open V. A section of A vanishing
   generically vanishes on V by step 1, applied to the flat open V, and hence on its
   corresponding source open. Schematic density of that source open makes the section zero.
   Also O → A is injective by step 1 and the generic isomorphism. Thus
   O ⊆ A ⊆ j_* O_W, where j is the inclusion of W.
5. By lem-trf-generic-fibre-points-smooth each fibre-component generic point has a smooth
   neighbourhood T. On affine charts, lem-weil-pbc-smooth-ring-map-iff-smooth-affine and
   lem-weil-pbc-smooth-over-normal-ring-normal make all local rings of T normal domains.
   The affine base rings are normal because all their prime localizations are normal.
   This uses smoothness only near fibre-component generic points.
6. On an affine open H of T, a section of A restricts to H intersect V and is integral over
   O(H), by lem-weil-pbc-finite-algebra-is-integral. Schematic density makes H intersect V
   dense. The lemma lem-sbc-normal-dense-open-integral-section extends this section over H.
   Schematic density on the source identifies the extension with the original A-section.
   Hence A restricts to O on T and W contains every fibre-component generic point.
7. For z outside W, its base image s is not generic. The normal Noetherian local domain
   O_(S,s) has a nonzero nonunit, so depth at least one. The fibre local ring at z is
   reduced by descent from its reduced geometric scalar extension. It has positive
   dimension, since z is not a fibre-component generic point. The S1 inequality in
   lem-weil-pbc-serre-criterion-reduced gives fibre depth at least one. Apply
   lem-weil-pbc-flat-local-depth-formula to the flat local stalk map to obtain total-space
   depth at least two at z.
8. Apply lem-sbc-depth-two-hartogs-restriction to the structure sheaf and W. The scheme is
   locally Noetherian, its structure sheaf is quasi-coherent and finite on affine charts,
   and step 7 gives the required depth. Thus O = j_* O_W. The intermediate finite algebra
   A from step 4 equals O. The affine description of a finite morphism then makes f an
   isomorphism. Along with step 1 this proves reducedness and eta-normality.
9. For a semistable multipointed curve, each geometric curve fibre is locally Noetherian.
   At a singular point, lem-weil-pbc-krull-intersection-jacobson injects its local ring
   into its maximal-ideal completion. By the semistability predicate that completion is
   the nodal algebra over the specified algebraically closed field. The nodal algebra
   embeds into the product of the two one-variable power series rings by restriction to
   the axes: a series vanishing on both axes is divisible by the product of the variables.
   The one-variable rings are domains by the lowest nonzero coefficient argument. Thus
   the local ring is reduced. Smooth points are reduced by
   sbc-lem-smooth-geometrically-reduced. These cases cover each geometric curve fibre.
10. The marking is etale, hence smooth by lem-weil-pbc-etale-smooth-zero-dimensional-fibres,
    and has reduced geometric fibres by sbc-lem-smooth-geometrically-reduced. The curve
    and marking maps are flat and finitely presented by MultipointedCurve. Apply steps
    1--8 to both maps. Empty markings and empty fibres are allowed. -/
theorem geometricallyReduced_etaNormal
    {S Z : Scheme.{u}} (p : Z ⟶ S) [IsIntegral S]
    [CompactSpace S] [QuasiSeparatedSpace S]
    (hS : ∀ x : S, IsIntegrallyClosed (S.presheaf.stalk x))
    [Flat p] [LocallyOfFinitePresentation p] [QuasiCompact p] [QuasiSeparated p]
    [GeometricallyReduced p] :
    IsReduced Z ∧ IsEtaNormal p ∧
      ∀ (C : MultipointedCurve S), C.IsSemistable →
        IsReduced C.X ∧ IsEtaNormal C.x ∧ IsReduced C.D ∧ IsEtaNormal C.d := by
  sorry

end AlgebraicGeometry
