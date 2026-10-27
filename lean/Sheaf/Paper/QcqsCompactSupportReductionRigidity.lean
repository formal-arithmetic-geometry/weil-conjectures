/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M4
-/
module

public import Sheaf.Paper.IntegralCompactSupportCoefficientComparison
import Sheaf.Paper.QcqsCompactSupportTorsionInputDetection
import Sheaf.Paper.QcqsCompactSupportTorsionCoefficientAction

/-! # Rigidity of natural compact-support comparisons

Source: Bhatt--Scholze, Definition 6.7.6 and Lemma 6.7.7; Stacks 0941, 0F7J
(blueprint: lem-qcqs-compact-support-reduction-rigidity).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures
open PurCompactSupport

variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (K₀ : Type u) [Field K₀] (hl : IsUnit (l : K₀))
  {X Y : Scheme.{u}} {f : X ⟶ Y}
  [X.Over (Spec (.of K₀))] [Y.Over (Spec (.of K₀))]
  [LocallyOfFiniteType (X ↘ Spec (.of K₀))] [QuasiCompact (X ↘ Spec (.of K₀))]
  [LocallyOfFiniteType (Y ↘ Spec (.of K₀))] [QuasiCompact (Y ↘ Spec (.of K₀))]
  [f.IsOver (Spec (.of K₀))] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
  (c : Compactification f)

private theorem reduction_map_ext_on_restriction
    {A B : Type*} [Category A] [Category B] {L : A ⥤ B} {R : B ⥤ A}
    (a : L ⊣ R) {P Q : A} (hQ : R.essImage Q) {f g : P ⟶ Q}
    (h : L.map f = L.map g) : f = g := by
  obtain ⟨N, ⟨e⟩⟩ := hQ
  apply (cancel_mono e.inv).mp
  apply (a.homEquiv P N).symm.injective
  simp only [Adjunction.homEquiv_counit, Functor.map_comp, h]

/-- Finite scalar reduction jointly detects natural transformations between these
specified compact-support functors. This asserts rigidity for natural transformations
on every constructible input, not faithfulness on individual derived Hom groups.

Source: Bhatt--Scholze Definition 6.7.6 and Lemma 6.7.7; Stacks 0941, 0F7J
(blueprint: lem-qcqs-compact-support-reduction-rigidity).

Proof: torsion-input detection reduces the assertion to constructible integral
inputs which are restrictions of finite-coefficient objects. The recorded
compact-support value of such an input is again a restriction from that same
finite quotient. For the scalar extension/restriction adjunction L adjoint to R,
the inverse Hom transpose of a map into R(N) is its L-image followed by the counit
at N. Thus equal reductions give equal inverse transposes, and injectivity of the
Hom equivalence identifies the original components. Torsion-input detection then
identifies the natural transformations. The two geometric steps are stated
separately; the scalar-adjunction argument is proved here. No faithfulness of
finite evaluation on arbitrary derived morphisms is asserted. Zero inputs and
empty schemes are included by the same adjunction. -/
theorem sfQcqsCompactSupport_reduction_ext
    (τ τ' : (sfIntegralConstructible l E X).ι ⋙ image (completed l E) c ⟶
      sfCompactSupportFiniteIntegralFunctor l K₀ hl c E ⋙
        (sfIntegralConstructible l E Y).ι)
    (h : ∀ (K : sfIntegralConstructibleCategory l E X) (n : ℕ),
      (scalarReductionDerivedExtension l E Y n).map (τ.app K) =
        (scalarReductionDerivedExtension l E Y n).map (τ'.app K)) : τ = τ' := by
  apply sfQcqsCompactSupport_torsion_input_ext l E K₀ hl c τ τ'
  intro n K hK
  have hQ := sfQcqsCompactSupport_torsion_coefficient_action l E K₀ hl c n K hK
  exact reduction_map_ext_on_restriction
    (derivedScalarExtensionRestrictionAdjunction l E Y n).choose hQ (h K n)

end WeilConjectures
