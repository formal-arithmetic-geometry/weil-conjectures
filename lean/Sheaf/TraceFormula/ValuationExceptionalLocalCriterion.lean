/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q138
-/
module

public import Sheaf.AlgebraicGeometry.MultipointedCurveModification
public import Sheaf.TraceFormula.SemistableMarkedPoint
public import Sheaf.TraceFormula.ProjectiveLineTree
public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.Topology.KrullDimension
import WeilConjectures.AlgebraicGeometry.PerfectComplex
import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.PerfectBaseChange
import Sheaf.TraceFormula.CurveP1TreeLocalCriterion
import Sheaf.AlgebraicGeometry.GeometricallyReducedEtaNormal
import Sheaf.SixFunctors.TraceFormula.NodalFamilyFittingSingular
import Sheaf.SixFunctors.TraceFormula.NodalGeometricFibresReduced
import Sheaf.RingTheory.ProjectiveOverLocalFree
import Sheaf.AlgebraicGeometry.SemistableMarkedBaseChange
import Sheaf.AlgebraicGeometry.UnramifiedLocusBaseChange
import Sheaf.TraceFormula.MultipointedCurve
import Sheaf.TraceFormula.ValuationCurveProjectivePreparation
import Sheaf.AlgebraicGeometry.ProperNormalGeometricConnectedness
import Sheaf.AlgebraicGeometry.SepClosedValuationGeometricComponents

/-! # The valuation-curve exceptional-tree local criterion

Source: Temkin, *Stable modification of relative curves*, Lemma 4.4.2, pp. 30–31,
Lemma 5.1(i), p. 34, and Appendix B, Corollary B.2, pp. 56–58
(blueprint: lem-trf-valuation-exceptional-local-criterion).

The two auxiliary maps give the actual scheme-theoretic fibre its base residue-field
structure and embed its scalar extension in the geometric curve fibre. Neither map
passes to a reduced subscheme.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- The canonical map from the scheme-theoretic contracted fibre to the residue field
of its image on the base. It is induced by the residue-field homomorphism of the target
curve's structure map. Source: Temkin, Lemma 4.4.2 and its algebraic-closure comparison
(blueprint: lem-trf-valuation-exceptional-local-criterion). -/
def MultipointedCurve.Hom.exceptionalFiberScalar {T : Scheme.{u}}
    {P Q : MultipointedCurve T} (q : P.Hom Q) (x : Q.X) :
    q.curve.fiber x ⟶ Spec (.of (T.residueField (Q.x x))) :=
  q.curve.fiberToSpecResidueField x ≫ Spec.map (Q.x.residueFieldMap x)

/-- The canonical inclusion of the algebraic-closure base change of the scheme-theoretic
contracted fibre into the geometric curve fibre. This is the pullback-induced map, with
both projections fixed. Source: Temkin, Lemma 4.4.2 and Appendix B
(blueprint: lem-trf-valuation-exceptional-local-criterion). -/
def MultipointedCurve.Hom.exceptionalGeometricFiberι {T : Scheme.{u}}
    {P Q : MultipointedCurve T} (q : P.Hom Q) (x : Q.X) :
    pullback (q.exceptionalFiberScalar x)
        (Spec.map (CommRingCat.ofHom (algebraMap (T.residueField (Q.x x))
          (AlgebraicClosure (T.residueField (Q.x x)))))) ⟶
      pullback P.x (Orgogozo.geometricPoint T (Q.x x)) :=
  pullback.map _ _ _ _ (q.curve.fiberι x) (𝟙 _)
    (T.fromSpecResidueField (Q.x x))
    (by
      simp only [MultipointedCurve.Hom.exceptionalFiberScalar, Category.assoc,
        Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField]
      rw [← Category.assoc, ← Scheme.Hom.fiber_fac, Category.assoc, q.curve_over])
    (by simp only [Orgogozo.geometricPoint, Category.id_comp])

/-- A normal valuation curve is semistable at the contracted point precisely when the
actual scheme-theoretic exceptional fibre is a projective-line tree with at most two
geometric boundary and marking points.

Source: Temkin, Lemma 4.4.2, pp. 30–31; Lemma 5.1(i), p. 34; Appendix B,
Corollary B.2, pp. 56–58 (blueprint: lem-trf-valuation-exceptional-local-criterion).

Proof, following the six steps of the node:
1. The nodal-family fitting and unramified-locus lemmas make the semistable locus open;
   semistable marked base change identifies its geometric fibres and markings.
2. Apply semistable marked base change, nodal geometric fibres reduced, and the
   separably-closed valuation geometric-components lemma over an algebraic closure of
   the base residue field. Keep the scheme-theoretic fibre throughout this comparison.
3. Localize the valuation base and shrink about the target point. Valuation-curve
   projective preparation embeds the normal affine target into a normal projective curve
   and extends the modification by the identity. Geometrically-reduced eta-normality
   shows that relative normalization changes nothing near the semistable fibre.
4. Proper-flat perfect base change and projective-over-local freeness make the Euler
   characteristic constant; the generic isomorphism gives equal arithmetic genera.
   Proper-normal geometric connectedness supplies connectedness of the projective fibres.
5. Apply the proper marked curve projective-line-tree local criterion (Appendix B.2).
   The boundary number is the number of branches of the contracted point. Together with
   the marking number, the bound two gives the smooth unmarked, smooth marked, and
   unmarked nodal cases, in both directions.
6. The projective replacement is unchanged near the contracted fibre. Transport the
   tree and both geometric counts back to the original scheme-theoretic fibre using
   projective preparation and semistable marked base change. No reduction is substituted.
-/
theorem valuation_exceptional_local_criterion
    (K : Type u) [Field K] [IsSepClosed K]
    (V : ValuationSubring K) [Finite (PrimeSpectrum V)]
    (P Q : MultipointedCurve (Spec (.of V)))
    (hgenericSmooth : Smooth (pullback.snd Q.x (Spec.map (CommRingCat.ofHom V.subtype))))
    (hgenericEtale : Etale (pullback.snd Q.d (Spec.map (CommRingCat.ofHom V.subtype))))
    (q : P.Hom Q)
    (hq : q.IsEtaModification (Spec.map (CommRingCat.ofHom V.subtype)))
    (x : Q.X)
    (hx : IsClosed ({Q.x.asFiber x} : Set (Q.x.fiber (Q.x x))))
    (hnormal : ∀ c : Q.X,
      IsDomain (Q.X.presheaf.stalk c) ∧ IsIntegrallyClosed (Q.X.presheaf.stalk c))
    (hdim : topologicalKrullDim (q.curve.fiber x) = 1)
    (hsemi : ∀ z : q.curve.fiber x,
      (MultipointedPair.ofCurve P).IsSemistableAt (q.curve.fiberι x z)) :
    (MultipointedPair.ofCurve Q).IsSemistableAt x ↔
      IsProjectiveLineTree
        (pullback.snd (q.exceptionalFiberScalar x)
          (Spec.map (CommRingCat.ofHom
            (algebraMap ((Spec (.of V)).residueField (Q.x x))
              (AlgebraicClosure ((Spec (.of V)).residueField (Q.x x))))))) ∧
      (Set.range (q.exceptionalGeometricFiberι x) ∩
          closure ((Set.range (q.exceptionalGeometricFiberι x))ᶜ)).encard +
        (Set.range (P.markingBaseChange
            (Orgogozo.geometricPoint (Spec (.of V)) (Q.x x))) ∩
          Set.range (q.exceptionalGeometricFiberι x)).encard ≤ 2 := by
  sorry

end AlgebraicGeometry
