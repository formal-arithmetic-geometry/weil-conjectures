/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J4
-/
module

public import Sheaf.AlgebraicGeometry.Morphisms.PuncturedCompletionChartSectionModules

/-!
# Completed localization and affine pullback section identifications

Source: Stacks Project, Tags 0BLH and 05EL.
(blueprint: lem-sbc-punctured-completion-chart-completed-localizations)
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme.CompletionGluingData

/-- Completed pullback sections identify scalar extension with localized completed sections.
Source: Stacks Project, Tag 0BLH, first two proof paragraphs; Tag 05EL, item (1).
(blueprint: lem-sbc-punctured-completion-chart-completed-localizations)
(blueprint: lem-sbc-punctured-completion-chart-completed-localizations-d)

Proof: use the actual modules completedSectionModule s and chartSectionModule
(q followed by U's inclusion) f_i. The affine open V_i maps to the affine D(f_i)
in U. Its pullback to Spec C is affine, and the affine pullback tensor-product
formula identifies its sections with C tensor_A Gamma(Y,V_i), using the chart's
structural action. This gives d_i: on a pure tensor z tensor m its value is the product of the
structural C-section z and the pullback of m. The tensor relations hold because
the two maps agree over A; the affine pullback formula makes this map an
isomorphism. Its value on 1 tensor m is therefore pullback of m.
The equation D.over identifies that pullback with the principal open defined by
f_i in E: both structure maps to Spec C are the same and D(f_i) lies in U.
Since E is affine, localization of its actual global sections gives sections
on this principal open. Compose that localization identification, the sections
of D.overlapIso, and d_i inverse to define alpha_i. Explicitly alpha_i(m'/f_i^n) is d_i inverse
applied to the restriction of D.toCompleted^*(m') divided by the structural
section f_i^n. These denominators are units on the principal open, so this
formula is well defined by the module localization universal property. These maps are over A;
the completed section and tensor-product maps are also over C, proving alpha_smul
and the displayed d_scalar equation. On m'/1 the localization map is restriction,
and the overlap identification is D.toCompleted, giving d_prime. The universal
properties include empty principal opens, whose sections and localization modules
are zero. No arbitrary transition equivalence is supplied as input.
-/
theorem exists_chart_completed_localizations
    {A : Type u} [CommRing A] [IsLocalRing A]
    {U : (Spec (.of A)).Opens} {Y : Scheme.{u}} {q : Y ⟶ U.toScheme}
    {E : Scheme.{u}} [IsAffine E] {s : E ⟶ Spec
      (.of (AdicCompletion (IsLocalRing.maximalIdeal A) A))}
    (D : CompletionGluingData A U q E s) (t : ℕ) (f : Fin t → A)
    (hf : ∀ i, PrimeSpectrum.basicOpen (f i) ≤ U)
    (hV : ∀ i, IsAffineOpen ((q ≫ U.ι) ⁻¹ᵁ PrimeSpectrum.basicOpen (f i))) :
    let C := AdicCompletion (IsLocalRing.maximalIdeal A) A
    let φ := algebraMap A C
    let M' := completedSectionModule s
    let M := fun i ↦ chartSectionModule (q ≫ U.ι) (f i)
    ∃ (alpha : ∀ i,
        FormalGlueing.localize (f i) (FormalGlueing.restrict φ M') ≃ₗ[A]
          FormalGlueing.restrict φ (FormalGlueing.extend φ
            (FormalGlueing.piece (f i) (M i))))
      (d : ∀ i, FormalGlueing.extend φ (FormalGlueing.piece (f i) (M i)) ≃+
        Γ(pullback q (completionSpecMap A ∣_ U),
          (pullback.fst q (completionSpecMap A ∣_ U)) ⁻¹ᵁ
            ((q ≫ U.ι) ⁻¹ᵁ PrimeSpectrum.basicOpen (f i)))),
      (∀ i (z : C) (x : FormalGlueing.localize (f i) (FormalGlueing.restrict φ M')),
        alpha i ((FormalGlueing.localizedSModule φ (f i) M').smul z x) =
          z • (alpha i x : FormalGlueing.extend φ (FormalGlueing.piece (f i) (M i)))) ∧
      (∀ i m, d i (alpha i (LocalizedModule.mk m 1)) =
        (pullback q (completionSpecMap A ∣_ U)).presheaf.map (homOfLE le_top).op
          (D.toCompleted.appTop m)) ∧
      (∀ i m, d i (TensorProduct.tmul A (1 : C) m) =
        (pullback.fst q (completionSpecMap A ∣_ U)).app _ m) ∧
      (∀ i (z : C) m, d i (z • m) =
        ((ΓSpecIso (.of C)).inv ≫
          (pullback.snd q (completionSpecMap A ∣_ U) ≫
            (completionSpecMap A ⁻¹ᵁ U).ι).appTop ≫
          (pullback q (completionSpecMap A ∣_ U)).presheaf.map
            (homOfLE (le_top :
              (pullback.fst q (completionSpecMap A ∣_ U)) ⁻¹ᵁ
                ((q ≫ U.ι) ⁻¹ᵁ PrimeSpectrum.basicOpen (f i)) ≤ ⊤)).op).hom z * d i m) := by
  sorry

end AlgebraicGeometry.Scheme.CompletionGluingData
