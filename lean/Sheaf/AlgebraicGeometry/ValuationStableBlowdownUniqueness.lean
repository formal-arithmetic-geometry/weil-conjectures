/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NG
-/
module

public import Sheaf.AlgebraicGeometry.MultipointedCurveModification
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.TransitionUnits
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import Mathlib.Topology.Connected.Basic

/-! # Uniqueness and factorization of stable blowdowns

Source: Temkin, Stable modification of relative curves, Appendix B, Lemma B.3, p. 58
(blueprint: lem-trf-valuation-stable-blowdown-uniqueness).

The helpers express this node's reference-relative exceptional components, elementary
scheme pushouts and finite sequences. The reference scheme need not itself be a curve.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry
namespace MultipointedCurve

/-- An exceptional component for the specified reference map is a projective-line component,
contracted to a singleton, containing at most two distinct marked or nonsmooth points.
Source: Temkin, Appendix B before Lemma B.3, p. 58
(blueprint: lem-trf-valuation-stable-blowdown-uniqueness). -/
def IsReferenceExceptionalComponent (k : Type u) [Field k]
    {C : Scheme.{u}} (P : MultipointedCurve (Spec (.of k))) (r : P.X ⟶ C)
    (a : ProjectiveLine (Spec (.of k)) ⟶ P.X) : Prop :=
  IsClosedImmersion a ∧
  a ≫ P.x = (ProjectiveLine (Spec (.of k)) ↘ Spec (.of k)) ∧
  Set.range a ∈ irreducibleComponents P.X ∧
  (Set.range (a ≫ r)).Subsingleton ∧
  (Set.range a ∩ (Set.range P.i ∪ {x | x ∉ P.x.smoothLocus})).encard ≤ 2

/-- An elementary exceptional contraction is the actual scheme pushout of the indicated
component to its scalar point, with semistable source and quotient, invertible marking map
and a factored reference map. No properness or complementary-open condition is added.
Source: Temkin, Appendix B, elementary-pushout paragraph, p. 58
(blueprint: lem-trf-valuation-stable-blowdown-uniqueness). -/
def Hom.IsReferenceExceptionalContraction (k : Type u) [Field k]
    {C : Scheme.{u}} {P Q : MultipointedCurve (Spec (.of k))}
    (f : P.Hom Q) (r : P.X ⟶ C) (s : Q.X ⟶ C) : Prop :=
  P.IsSemistable ∧ Q.IsSemistable ∧ IsIso f.marking ∧ f.curve ≫ s = r ∧
  ∃ a : ProjectiveLine (Spec (.of k)) ⟶ P.X,
    P.IsReferenceExceptionalComponent k r a ∧
    ∃ b : Spec (.of k) ⟶ Q.X,
      b ≫ Q.x = 𝟙 (Spec (.of k)) ∧
      IsPushout a (ProjectiveLine (Spec (.of k)) ↘ Spec (.of k)) f.curve b

/-- A finite sequence of reference-relative elementary contractions and a final pointed
isomorphism. Every recursive step uses the marking and nonsmooth locus of its current
quotient and the induced reference map. Length zero allows every pointed isomorphism.
Source: Temkin, Appendix B, construction and final assertion of Lemma B.3, p. 58
(blueprint: lem-trf-valuation-stable-blowdown-uniqueness). -/
def Hom.HasReferenceExceptionalContractionSequence (k : Type u) [Field k]
    {C : Scheme.{u}} (n : ℕ) {P Q : MultipointedCurve (Spec (.of k))}
    (f : P.Hom Q) (r : P.X ⟶ C) (s : Q.X ⟶ C) : Prop :=
  match n with
  | 0 => P.IsSemistable ∧ Q.IsSemistable ∧ IsIso f.curve ∧ IsIso f.marking ∧
      f.curve ≫ s = r
  | n + 1 =>
    ∃ (R : MultipointedCurve (Spec (.of k))) (t : R.X ⟶ C)
      (h : P.Hom R) (g : R.Hom Q),
      h.IsReferenceExceptionalContraction k r t ∧
      h.curve ≫ g.curve = f.curve ∧ h.marking ≫ g.marking = f.marking ∧
      g.HasReferenceExceptionalContractionSequence k n t s

end MultipointedCurve

/-- A terminal exceptional-contraction sequence factors uniquely through every partial
sequence; any two terminal sequences are uniquely isomorphic over the original pointed
curve. No connectedness, properness or separatedness over the field is assumed.
Source: Temkin, Appendix B, Lemma B.3 and its final factorization assertion, p. 58
(blueprint: lem-trf-valuation-stable-blowdown-uniqueness).

Proof plan:
1. An elementary pushout map cancels morphisms: a k-point on the contracted projective
   line makes equality on the curve imply equality on the scalar vertex; use the colimit
   universal property. Marking maps are isomorphisms. Two pushouts of the same component
   are uniquely isomorphic over the source. Composites retain cancellation.
2. The exceptional-contraction diamond lemma preserves reference noncollapse. Strongly
   induct on the terminal sequence length n to factor it through any single contraction,
   with remaining length n-1. Absorb intermediate isomorphisms by conjugating pushouts.
3. At length zero no exceptional component exists. At positive length compare the first
   component A with the requested B; if equal, use the unique pushout isomorphism.
4. If distinct, the diamond supplies j_A and j_B to a common quotient. Apply induction
   to the tail and j_A, obtaining w; the desired map is j_B followed by w. At n=1 the
   diamond would supply an exceptional component on the terminal target, impossible.
5. Iterate the single-step factorization through the partial sequence. It cannot exceed
   length n. Compose with the inverse final isomorphism; the empty sequence is included.
6. Cancel the partial sequence for uniqueness. For two terminal sequences, factor each
   through the other and cancel to see the two factors are inverse. Empty markings and
   disconnected curves require no changes. -/
theorem valuation_stable_blowdown_uniqueness
    (k : Type u) [Field k] [IsAlgClosed k]
    (C : Scheme.{u}) (c : C ⟶ Spec (.of k))
    (P S : MultipointedCurve (Spec (.of k)))
    (r : P.X ⟶ C) (s : S.X ⟶ C) (hr : r ≫ c = P.x)
    (π : P.Hom S) (n : ℕ)
    (hπ : π.HasReferenceExceptionalContractionSequence k n r s)
    (hnoncollapse : ∀ x : P.X, ¬ (r '' connectedComponent x).Subsingleton)
    (hstable : ∀ a : ProjectiveLine (Spec (.of k)) ⟶ S.X,
      ¬ S.IsReferenceExceptionalComponent k s a) :
    (∀ (Q : MultipointedCurve (Spec (.of k))) (t : Q.X ⟶ C)
      (q : P.Hom Q) (m : ℕ),
      q.HasReferenceExceptionalContractionSequence k m r t →
      ∃! v : Q.Hom S,
        q.curve ≫ v.curve = π.curve ∧ q.marking ≫ v.marking = π.marking) ∧
    (∀ (Q : MultipointedCurve (Spec (.of k))) (t : Q.X ⟶ C)
      (q : P.Hom Q) (m : ℕ),
      q.HasReferenceExceptionalContractionSequence k m r t →
      (∀ a : ProjectiveLine (Spec (.of k)) ⟶ Q.X,
        ¬ Q.IsReferenceExceptionalComponent k t a) →
      ∃! v : Q.Hom S,
        (q.curve ≫ v.curve = π.curve ∧ q.marking ≫ v.marking = π.marking) ∧
          IsIso v.curve ∧ IsIso v.marking) := by
  sorry

end AlgebraicGeometry
