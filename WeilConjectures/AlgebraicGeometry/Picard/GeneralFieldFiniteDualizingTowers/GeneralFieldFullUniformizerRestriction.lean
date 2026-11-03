/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Picard.GeneralFieldFiniteDualizingTowers.GeneralFieldFiniteDualizingTowerData

/-! # The prescribed ramification restriction of finite dualizing towers

Source: current blueprint, `sec-smooth-purity/sk-lem-sp-tower/`
`lem-coef-integral-finite-extension.proof.md`.
(blueprint: lem-sf-general-field-full-uniformizer-restriction)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.FiniteCoefficientAdjoints
open WeilConjectures.FiniteDualizingTowers
namespace WeilConjectures.GeneralFieldFiniteDualizingTowers
variable (k : Type u) [Field k] (X : Scheme.{u})
  [X.Over (Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))]
  [QuasiCompact (X ↘ Spec (.of k))] [IsSeparated (X ↘ Spec (.of k))]
variable {l : ℕ} [Fact l.Prime] {E : Type (u + 1)} [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

private theorem ramification_ideals (s : Stage l E) :
    ∃ e : ℕ+, ∀ n : ℕ, (atLevel s n).ideal =
      (atLevel (baseStage (l := l) (E := s.field) 1) (ramificationIndices e n)).ideal := by
  obtain ⟨e, _z, _hz, hI, _hcofinal⟩ := stage_ramification s
  refine ⟨e, fun n ↦ ?_⟩
  change Ideal.span ({s.parameter} : Set s.integers) ^ (n + 1) =
    Padic.coefficientExtensionIdeal l s.field (ramificationIndices e n + 1)
  rw [ramificationIndices_exponent]
  exact hI (n + 1)

/-- Every specified realization is the prescribed ramification subsequence of a full
upper-uniformizer realization, through the fixed residue-preserving ring maps.
Source: `literature/blueprint/latest/blueprint/sec-smooth-purity/sk-lem-sp-tower/`
`lem-coef-integral-finite-extension.proof.md`, paragraphs 3-4
(blueprint: lem-sf-general-field-full-uniformizer-restriction).
Proof: stage_ramification supplies a positive ramification index e and the equalities
of principal-power ideals. At level n use ramificationIndices_exponent to identify
e(n+1) with the chosen upper-uniformizer index. The maps induced by these equalities
are the specified quotient-ring isomorphisms. Quotient induction on an integer
representative shows they commute with adjacent quotient maps; recursion gives all
maps in the inverse sequence and hence the ring-diagram isomorphism zeta. Realize the
full upper-uniformizer finite dualizing tower by the sequential realization theorem,
using the uniform finite dualizing lower bound, and take its subsequence. Exact
normalization restriction by zeta gives a tower over the original diagram. On each
level the finite coefficient theorem for the specified quotient-ring isomorphism
provides the normalized invertible counit comparison. Its composition equation with
quotient maps proves compatibility. Adjacent negative Hom vanishes by finite
biduality as in the sequential uniqueness argument. Lift this compatible family
uniquely through the sequential mapping theorem. Every evaluation is invertible, so
joint conservativity makes the lift an isomorphism. Undo the evaluation isomorphisms
to obtain precisely the displayed HEq in IsFullUniformizerRestriction, with the
specified ring quotient identification rather than an arbitrary automorphism. -/
theorem full_uniformizer_restriction
    (p : ℕ) (hp : p.Prime) (hchar : ringChar k = p)
    (hk : Finite k ∨ IsAlgClosed k) (hl : l ≠ p)
    (s : Stage l E) (P : Realization k X s) :
    IsFullUniformizerRestriction k X s P := by
  sorry

end WeilConjectures.GeneralFieldFiniteDualizingTowers
