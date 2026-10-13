/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.Morphisms.PuncturedCompletionMatchingSections
public import Sheaf.RingTheory.FormalGlueingH0

/-! # Finite affine charts as module glueing data

Source: Stacks Project, Lemma 0BLH, first two paragraphs of its proof,
and Remark 05EL, the definition of H0.
(blueprint: lem-sbc-punctured-completion-formal-glueing-data)
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme.CompletionGluingData

/-- Affine chart sections give a module glueing datum and a map from compatible
families to the explicit matching ring, preserving the completed coordinate.
Source: Stacks Project, Lemma 0BLH, first two
paragraphs; Remark 05EL (remark-glueing-data), definition of H0.
(blueprint: lem-sbc-punctured-completion-formal-glueing-data)

Proof: the given finite list f generates the maximal ideal of A. Its
principal opens cover U by hU, including the empty cover when U is empty.
Since q is finite, its inverse images of these principal opens
are affine; let their section modules be the chart modules. Since s is finite,
E is affine; its section module is the prime module. The given overlapIso
identifies its localized prime module with the scalar extensions of the chart
modules. Restriction to double principal opens gives the overlap maps.
Functoriality of restriction proves their square and cocycle equations.
These maps are A-linear, and the prime comparison commutes with completed
scalars, so they form FormalGlueing.Data. Identify its prime module with
Gamma(E) with the module action induced by s. For an H0 family, the second
compatibility equations glue the chart sections to a section on Y. The first
compatibility equations make this section agree with its prime coordinate on
the overlap: check on the principal-open cover and use sheaf separatedness.
The two sections give an element of the ring pullback D.matchingRing. Its
second projection is the prime coordinate by the pullback lift equation.
No surjectivity or finiteness assertion about D.matchingRing is used here.
For empty U, both punctured section rings are zero and the pullback retains
just the prime coordinate. Zero chart rings satisfy the same sheaf equations. -/
theorem exists_formalGlueingData_matching_projection
    {A : Type u} [CommRing A] [IsLocalRing A]
    {U : (Spec (.of A)).Opens}
    (hU : ∀ x : Spec (.of A), x ∈ U ↔ x ≠ IsLocalRing.closedPoint A)
    {Y : Scheme.{u}} {q : Y ⟶ U.toScheme} [IsFinite q]
    {E : Scheme.{u}} {s : E ⟶ Spec
      (.of (AdicCompletion (IsLocalRing.maximalIdeal A) A))} [IsFinite s]
    (D : CompletionGluingData A U q E s) (t : ℕ) (f : Fin t → A)
    (hgen : Ideal.span (Set.range f) = IsLocalRing.maximalIdeal A) :
    let C := AdicCompletion (IsLocalRing.maximalIdeal A) A
    let φ := algebraMap A C
    let g : CommRingCat.of C ⟶ Γ(E, ⊤) := (ΓSpecIso (.of C)).inv ≫ s.appTop
    letI : Module C Γ(E, ⊤) := Module.compHom _ g.hom
    ∃ (X : FormalGlueing.Data.{u, u, u} φ f) (e : X.M' ≃ₗ[C] Γ(E, ⊤))
      (k : FormalGlueing.h0 φ f X → D.matchingRing),
      ∀ h, pullback.snd
        (pullback.fst q (completionSpecMap A ∣_ U)).appTop D.toCompleted.appTop
          (k h) = e h.val.1 := by sorry

end AlgebraicGeometry.Scheme.CompletionGluingData
