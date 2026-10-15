/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NS
-/
module

public import Sheaf.AlgebraicGeometry.NagataRelativeGluingValidStage
import Sheaf.AlgebraicGeometry.RelativeFiniteAffinePresentation
import Sheaf.Order.DirectedFiniteUpperBound
import Sheaf.AlgebraicGeometry.NagataMorphismEqEventually
import Sheaf.AlgebraicGeometry.NagataQCOpenEqEventually
import Sheaf.AlgebraicGeometry.NagataRelativeGluingDatumDescends

/-!
# Relative gluing axioms at the selected stage

Source: Weil conjectures blueprint, sec-nagata-compactification,
sk-prop-nagata-sketch-approximation, node order 361
(blueprint: lemma-nagata-relative-gluing-axioms-eventually).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- The explicit piecewise gluing axioms for the transported relative datum: diagonal
coverage, reversed-orientation coverage, domain matching in both directions, inverse
identities, agreement on intersections and with reversed orientations, diagonal identity,
and the triple cocycle on the canonical common fibre-product domain.
Source: blueprint nodes orders 360--361
(blueprint: lemma-nagata-relative-gluing-axioms-eventually).
This predicate only spells out the conclusion; it supplies no gluing equations as data. -/
def NagataRelativeGluingTransport.HasGluingAxioms
    {S : Scheme.{u}} {J : Type u} {K : J → J → Type u}
    (T : NagataRelativeGluingTransport S J K) : Prop :=
  let a := T.leftInclusion
  let b := T.rightInclusion
  let g := fun j k l ↦ T.forward j k l ≫ b j k l
  let h := fun j k l ↦ T.backward j k l ≫ a j k l
  let w := fun j k ↦ ⨆ l, T.leftOpen j k l
  let v := fun j k ↦ ⨆ l, T.rightOpen j k l
  (∀ j, w j j = ⊤) ∧
  (∀ j k, w j k = v k j) ∧
  (∀ j k z l, (g j k l).left ⁻¹ᵁ w k z = (a j k l).left ⁻¹ᵁ w j z) ∧
  (∀ j k z l, (h j k l).left ⁻¹ᵁ w j z = (b j k l).left ⁻¹ᵁ w k z) ∧
  (∀ j k l, T.forward j k l ≫ T.backward j k l = 𝟙 (T.left j k l) ∧
    T.backward j k l ≫ T.forward j k l = 𝟙 (T.right j k l)) ∧
  (∀ j k l m, pullback.fst (a j k l) (a j k m) ≫ g j k l =
    pullback.snd (a j k l) (a j k m) ≫ g j k m) ∧
  (∀ j k l m, pullback.fst (b j k l) (b j k m) ≫ h j k l =
    pullback.snd (b j k l) (b j k m) ≫ h j k m) ∧
  (∀ j k l m, pullback.fst (a j k l) (b k j m) ≫ g j k l =
    pullback.snd (a j k l) (b k j m) ≫ h k j m) ∧
  (∀ j l, g j j l = a j j l) ∧
  (∀ j k z l m n,
    pullback.fst (pullback.fst (g j k l) (a k z m) ≫ a j k l) (a j z n) ≫
      pullback.snd (g j k l) (a k z m) ≫ g k z m =
    pullback.snd (pullback.fst (g j k l) (a k z m) ≫ a j k l) (a j z n) ≫ g j z n)

/-- The named datum at lambda_rel satisfies all relative gluing axioms.
Source: blueprint node order 361
(blueprint: lemma-nagata-relative-gluing-axioms-eventually).

Proof:
1. Fix the raw datum, canonical inclusions, and equality choices of
   `def-nagata-relative-gluing-valid-stage`. By
   `lemma-nagata-relative-gluing-datum-descends`, its charts and both directions of
   its overlap maps pull back to the finite affine presentation of
   `def-nagata-relative-finite-affine-presentation`. That presentation satisfies
   the gluing equations. Canonical common domains are identified by their chart
   and base projections, using the fibre-product universal property. The retained
   compactness, finite-presentation and limit-equality inputs apply to these equations.
2. Apply `lemma-nagata-directed-finite-upper-bound` to the finite set containing
   the raw stage and every selected open- and map-equality stage. Hence every
   witness stage is below the very same selected lambda_rel.
3. Apply `lemma-nagata-qc-open-eq-eventually` to each listed open equation at
   lambda_rel. This gives diagonal coverage, reversed-orientation coverage, and
   forward domain matching. Functorial inverse images identify these opens with
   those of `nagataRelativeGluingValidDatum`.
4. Apply `lemma-nagata-morphism-eq-eventually` to each listed parallel-map
   equation at lambda_rel. Functorial pullback and its canonical identifications
   give both inverse identities, both piecewise agreement equations, orientation
   agreement, the diagonal identity and every triple cocycle. For backward domain
   matching, cover each right piece by its intersections with the reversed left
   pieces, using reversed-orientation coverage. On each intersection orientation
   agreement identifies the backward map with the reversed forward map, whose
   domain matching was proved in step 3. Equality of opens is local on this cover.
   No glued scheme or finite-stage gluing hypothesis is used. -/
theorem nagataRelativeGluingAxiomsEventually
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (D : Iᵒᵖ ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ {i j : Iᵒᵖ} (t : i ⟶ j), IsAffineHom (D.map t)]
    (i₀ : I) [CompactSpace (D.obj (op i₀))] [QuasiSeparatedSpace (D.obj (op i₀))]
    {X : Scheme.{u}} (f : X ⟶ c.pt)
    [CompactSpace c.pt] [QuasiSeparatedSpace c.pt]
    [LocallyOfFinitePresentation f] [QuasiCompact f] [QuasiSeparated f]
    (R : NagataRelativeGluingDatum D c hc i₀ f)
    (P : NagataRelativeRawInclusions D c hc i₀ f R)
    (A : NagataRelativeGluingValidStageData D c hc i₀ f R P) :
    (nagataRelativeGluingValidDatum D c hc i₀ f R P A).HasGluingAxioms := by
  sorry

end AlgebraicGeometry
