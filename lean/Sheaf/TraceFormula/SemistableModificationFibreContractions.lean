/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q07
-/
module

public import Sheaf.AlgebraicGeometry.MultipointedCurveModification
public import Sheaf.AlgebraicGeometry.SemistableMultipointedPair
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.TransitionUnits
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
import Sheaf.AlgebraicGeometry.FiniteBirationalNormalIso
import Sheaf.AlgebraicGeometry.GeometricallyReducedEtaNormal
import Sheaf.AlgebraicGeometry.SemistableMarkedBaseChange
import Sheaf.TraceFormula.ValuationHorizontalCurveModels
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
import Mathlib.AlgebraicGeometry.Noetherian
import Sheaf.TraceFormula.NodalSubcurveBoundary
import Sheaf.TraceFormula.ValuationCurveProjectivePreparation
import Sheaf.TraceFormula.ValuationExceptionalLocalCriterion
import Sheaf.AlgebraicGeometry.FiniteBirationalNodalConnectedIso
import Sheaf.AlgebraicGeometry.ProperNormalGeometricConnectedness

/-! # Elementary contraction sequences on geometric fibres of semistable modifications

Source: Temkin, Stable modification of relative curves, Lemma 4.4.2, Corollary 4.4.3(i),
and Appendix B, before Lemma B.3 (blueprint: lem-trf-semistable-modification-fibre-contractions).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- A length-`n` exceptional contraction sequence, followed by an isomorphism of pairs.
The successor clause gives the actual scheme pushout of a projective-line component to
its scalar point. It retains the remaining map, the two factorization equations, the
marking isomorphism, semistability and the isomorphism on the complementary open.
Distinct special points are counted on the component, without counting branches.
These are the elementary contractions in Temkin, Appendix B before Lemma B.3
(blueprint: lem-trf-semistable-modification-fibre-contractions). -/
def MultipointedPair.HasExceptionalContractionSequence (Ω : Type u) [Field Ω]
    (n : ℕ) (P Q : MultipointedPair (Spec (.of Ω)))
    (f : P.curve ⟶ Q.curve) (d : P.marking ⟶ Q.marking) : Prop :=
  match n with
  | 0 => P.IsSemistable ∧ IsIso f ∧ IsIso d ∧ P.inclusion ≫ f = d ≫ Q.inclusion
  | n + 1 =>
    P.IsSemistable ∧
    ∃ (R : MultipointedPair (Spec (.of Ω)))
      (h : P.curve ⟶ R.curve) (hd : P.marking ⟶ R.marking)
      (r : R.curve ⟶ Q.curve) (rd : R.marking ⟶ Q.marking),
      R.IsSemistable ∧ P.inclusion ≫ h = hd ≫ R.inclusion ∧
      IsIso hd ∧ IsProper h.left ∧ h ≫ r = f ∧ hd ≫ rd = d ∧
      (∃ a : ProjectiveLine (Spec (.of Ω)) ⟶ P.curve.left,
        IsClosedImmersion a ∧
        a ≫ P.curve.hom = (ProjectiveLine (Spec (.of Ω)) ↘ Spec (.of Ω)) ∧
        Set.range a ∈ irreducibleComponents P.curve.left ∧
        (Set.range a ∩ (Set.range P.inclusion.left ∪
          {x | ¬ (P.curve.hom.stalkMap x).hom.FormallySmooth})).encard ≤ 2 ∧
        (Set.range (a ≫ f.left)).Subsingleton ∧
        ∃ b : Spec (.of Ω) ⟶ R.curve.left,
          b ≫ R.curve.hom = 𝟙 (Spec (.of Ω)) ∧
          IsPushout a (ProjectiveLine (Spec (.of Ω)) ↘ Spec (.of Ω)) h.left b ∧
          ∃ U : R.curve.left.Opens,
            (U : Set R.curve.left) = (Set.range b)ᶜ ∧
            h.left ⁻¹' (U : Set R.curve.left) = (Set.range a)ᶜ ∧
            IsIso (pullback.snd h.left U.ι)) ∧
      MultipointedPair.HasExceptionalContractionSequence Ω n R Q r rd

/-- Every geometric fibre map is a finite sequence of elementary exceptional contractions,
up to a final isomorphism of pairs. No properness, separatedness or connectedness of the
structural curves is assumed. Source: Temkin, Lemma 4.4.2, Corollary 4.4.3(i) and Appendix B
(blueprint: lem-trf-semistable-modification-fibre-contractions).

Proof plan (the nine steps of the DAG):
1. Valuation rings are integrally closed. Use geometrically-reduced eta-normality,
   valuation-curve projective preparation and horizontal curve models to deduce normality
   and finitely many components of P and Q.
2. Their generic fibres are schematically dense: invert a nonzero element in the smallest
   nonzero prime, or use the identity when V is a field. Componentwise normal-target
   Zariski connectedness gives nonempty connected geometric fibres of q.
3. The marking map has finite fibres; proper-finite-fibre-finite-near makes it finite.
   Eta-normality makes this finite eta-modification an isomorphism, also for empty markings.
4. Projective preparation gives a finite quasi-finite modification locus B. A fibre there
   cannot be zero-dimensional, by finite-near and finite-birational-normal-iso. Connectedness
   and Noetherianity make it pure one-dimensional; its points are semistable.
5. Apply valuation-exceptional-local-criterion on the original normal total spaces.
   The actual scheme-theoretic fibres are reduced exceptional projective-line trees.
6. Base change gives proper semistable pointed fibre maps, marking isomorphisms and
   isomorphisms off B. Each exceptional tree has nonempty boundary by properness and
   connectedness of fibres.
7. Induct on the number of exceptional components. A tree with boundary-plus-markings
   at most two has an exceptional leaf with at most two special points. Apply
   nodal-exceptional-component-pushout to that leaf.
8. Nodal-subcurve-boundary identifies the reduced attaching points. The pushout preserves
   the remaining maps, marking, semistability and tree boundary bounds, and removes one
   component. Thus the integer in the induction decreases by one.
9. At zero components the remaining proper map is finite by finite-near; the
   finite-birational-nodal-connected-iso criterion makes it an isomorphism of pairs.
   This also handles an initially empty sequence, without stable-blowdown uniqueness. -/
theorem semistable_modification_fibre_contractions
    (K : Type u) [Field K] [IsSepClosed K]
    (V : ValuationSubring K) [Finite (PrimeSpectrum V)]
    (P Q : MultipointedCurve (Spec (.of V))) (q : P.Hom Q)
    (hq : q.IsEtaModification (Spec.map (CommRingCat.ofHom V.subtype)))
    (hP : P.IsSemistable) (hQ : Q.IsSemistable)
    (hQη : Smooth (pullback.snd Q.x (Spec.map (CommRingCat.ofHom V.subtype))))
    (hNη : Etale (pullback.snd Q.d (Spec.map (CommRingCat.ofHom V.subtype))))
    (s : Spec (.of V)) (Ω : Type u) [Field Ω]
    [Algebra ((Spec (.of V)).residueField s) Ω]
    [IsAlgClosure ((Spec (.of V)).residueField s) Ω] :
    ∃ n : ℕ, MultipointedPair.HasExceptionalContractionSequence Ω n
      ((MultipointedPair.ofCurve P).baseChange
        (Spec.map (CommRingCat.ofHom (algebraMap ((Spec (.of V)).residueField s) Ω)) ≫
          (Spec (.of V)).fromSpecResidueField s))
      ((MultipointedPair.ofCurve Q).baseChange
        (Spec.map (CommRingCat.ofHom (algebraMap ((Spec (.of V)).residueField s) Ω)) ≫
          (Spec (.of V)).fromSpecResidueField s))
      ((Over.pullback
        (Spec.map (CommRingCat.ofHom (algebraMap ((Spec (.of V)).residueField s) Ω)) ≫
          (Spec (.of V)).fromSpecResidueField s)).map (Over.homMk q.curve q.curve_over))
      ((Over.pullback
        (Spec.map (CommRingCat.ofHom (algebraMap ((Spec (.of V)).residueField s) Ω)) ≫
          (Spec (.of V)).fromSpecResidueField s)).map
            (Over.homMk q.marking q.marking_over)) := by
  sorry

end AlgebraicGeometry
