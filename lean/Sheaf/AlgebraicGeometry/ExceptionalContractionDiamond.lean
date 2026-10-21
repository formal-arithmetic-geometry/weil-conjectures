/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.ValuationStableBlowdownUniqueness
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.Topology.Connected.Basic
import Sheaf.SixFunctors.TraceFormula.NodalGeometricFibresReduced
import Sheaf.TraceFormula.NodalSubcurveBoundary
import Sheaf.AlgebraicGeometry.MultipointedCurveModification
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.TransitionUnits

/-! # Local diamond for exceptional rational-component contractions

Source: Temkin, *Stable modification of relative curves*, Appendix B, printed p. 58
(blueprint: lem-trf-exceptional-contraction-diamond).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Supplied exceptional-component pushouts are proper surjections with connected geometric
fibres, are isomorphisms off the contracted component, and preserve a proper noncollapsing
reference map. Two distinct exceptional components remain exceptional after either first
contraction and admit a common second contraction as pointed curves over the reference.
Source: Temkin, Appendix B, elementary pushouts preceding Lemma B.3, printed p. 58
(blueprint: lem-trf-exceptional-contraction-diamond).

Proof plan (the node's local diamond refinement of Temkin's argument):
1. Put Q equal to the reduced complementary subcurve of A. Nodal-geometric-fibres-reduced
   makes P reduced. Nodal-subcurve-boundary, applied to A and to Q, gives nodal Q and a
   reduced boundary E of smooth points on both branches. Noncollapse and exceptionality
   give 1 <= |E| <= 2 and |E| plus the number of markings on A at most two. Reducedness
   makes P the scheme-theoretic union; closed-union-pushout gives P = Q amalg_E A.
   Closed-immersion-proper makes Q proper over C.
2. Global functions on P1 are k by its two polynomial charts, so the singleton-image
   restriction of r factors through a k-point. Relative-nodal-point-pinching produces
   Y = Q amalg_E Spec k proper over C. The two pushout universal properties identify Y
   with every supplied contraction of A, including the reference and point legs.
3. Pinching is an isomorphism off E. The contracted fibre is A scheme-theoretically:
   at a boundary node k[[x,z]]/(xz), the pulled-back maximal ideal is the branch ideal
   (x). All geometric fibres are points or P1. Proper-to-separated proves properness
   of the curve map over C. A one-point boundary gives a smooth point carrying the
   possible single marking; a two-point boundary gives an unmarked node. Markings
   therefore remain distinct smooth points and are transported isomorphically.
4. Images of the finitely many clopen connected components under the proper surjection
   are closed, connected and disjoint by connected fibres. They are clopen and precisely
   the quotient's connected components. Their reference images are unchanged; thus
   noncollapse persists, and pinching already supplied properness of the reference.
5. Two exceptional components cannot meet twice: their union would be a collapsed
   connected component. The pinching subcurve clause therefore identifies each remaining
   component by a closed immersion, with irreducible-component image and singleton
   reference image.
6. If the components meet, a contracted tail replaces their common node by a smooth
   point, possibly marked, while a bridge replaces it by a node. The special-point
   count never increases. Disjoint components are unchanged. Repeat steps 1--3 on the
   two residual exceptional components, using properness and noncollapse from step 4.
7. Pushout universality factors either double contraction through the other, giving
   comparison maps over C compatible with the transported markings.
8. Every elementary pushout cancels morphisms: a k-point of its P1 component expresses
   the scalar leg through the curve leg. Pushout uniqueness then gives epimorphism.
   Cancel twice to see that the comparison maps are inverse, and transport one second
   contraction through their isomorphism to obtain the asserted common pointed target. -/
theorem exceptional_contraction_diamond
    (k : Type u) [Field k] [IsAlgClosed k]
    (C : Scheme.{u}) (c : C ⟶ Spec (.of k))
    (P : MultipointedCurve (Spec (.of k))) (hP : P.IsSemistable)
    (r : P.X ⟶ C) (hr : r ≫ c = P.x) (hrproper : IsProper r)
    (hnoncollapse : ∀ x : P.X, ¬ (r '' connectedComponent x).Subsingleton) :
    (∀ (Q : MultipointedCurve (Spec (.of k))) (hQ : Q.IsSemistable)
      (s : Q.X ⟶ C) (h : P.Hom Q) (hm : IsIso h.marking)
      (hs : h.curve ≫ s = r)
      (a : ProjectiveLine (Spec (.of k)) ⟶ P.X)
      (ha : P.IsReferenceExceptionalComponent k r a)
      (b : Spec (.of k) ⟶ Q.X)
      (hb : IsPushout a (ProjectiveLine (Spec (.of k)) ↘ Spec (.of k)) h.curve b),
      IsProper h.curve ∧ Surjective h.curve ∧ GeometricallyConnected h.curve ∧
      (∃ (U : P.X.Opens) (V : Q.X.Opens) (e : U.toScheme ≅ V.toScheme),
        (U : Set P.X) = (Set.range a)ᶜ ∧ (V : Set Q.X) = (Set.range b)ᶜ ∧
        e.hom ≫ V.ι = U.ι ≫ h.curve) ∧
      IsProper s ∧ (∀ x : Q.X, ¬ (s '' connectedComponent x).Subsingleton)) ∧
    (∀ (PA PB : MultipointedCurve (Spec (.of k)))
      (hPA : PA.IsSemistable) (hPB : PB.IsSemistable)
      (rA : PA.X ⟶ C) (rB : PB.X ⟶ C) (hA : P.Hom PA) (hB : P.Hom PB)
      (hmA : IsIso hA.marking) (hmB : IsIso hB.marking)
      (hrA : hA.curve ≫ rA = r) (hrB : hB.curve ≫ rB = r)
      (aA aB : ProjectiveLine (Spec (.of k)) ⟶ P.X)
      (haA : P.IsReferenceExceptionalComponent k r aA)
      (haB : P.IsReferenceExceptionalComponent k r aB)
      (hneq : Set.range aA ≠ Set.range aB)
      (bA : Spec (.of k) ⟶ PA.X) (bB : Spec (.of k) ⟶ PB.X)
      (hpA : IsPushout aA (ProjectiveLine (Spec (.of k)) ↘ Spec (.of k)) hA.curve bA)
      (hpB : IsPushout aB (ProjectiveLine (Spec (.of k)) ↘ Spec (.of k)) hB.curve bB),
      PA.IsReferenceExceptionalComponent k rA (aB ≫ hA.curve) ∧
      PB.IsReferenceExceptionalComponent k rB (aA ≫ hB.curve) ∧
      ∃ (T : MultipointedCurve (Spec (.of k))) (rT : T.X ⟶ C)
        (jA : PA.Hom T) (jB : PB.Hom T)
        (dA dB : Spec (.of k) ⟶ T.X),
        T.IsSemistable ∧ IsIso jA.marking ∧ IsIso jB.marking ∧
        jA.curve ≫ rT = rA ∧ jB.curve ≫ rT = rB ∧
        IsPushout (aB ≫ hA.curve) (ProjectiveLine (Spec (.of k)) ↘ Spec (.of k))
          jA.curve dA ∧
        IsPushout (aA ≫ hB.curve) (ProjectiveLine (Spec (.of k)) ↘ Spec (.of k))
          jB.curve dB ∧
        hA.curve ≫ jA.curve = hB.curve ≫ jB.curve ∧
        hA.marking ≫ jA.marking = hB.marking ≫ jB.marking) := by
  sorry

end AlgebraicGeometry
