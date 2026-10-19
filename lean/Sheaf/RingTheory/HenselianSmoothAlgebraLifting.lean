/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q158
-/
module

public import Mathlib.RingTheory.Smooth.Basic
public import WeilConjectures.Mathlib.RingTheory.Henselian
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Sheaf.Paper.SmoothSectionEtaleLift
import WeilConjectures.RingTheory.HenselizationStageMap

/-!
# Lifting maps from smooth algebras across henselian pairs

Source: Stacks Project, More on Algebra, Tag 0H74, `lemma-lift-smooth-henselian`
(blueprint: lem-trf-henselian-smooth-algebra-lifting).
-/

@[expose] public section

universe u v w

namespace Algebra.Smooth

/-- Every map from a smooth `R`-algebra to `A/I`, for a henselian pair `(A, I)`,
lifts to an `R`-algebra map to `A`.

Source: Stacks Project, More on Algebra, Tag 0H74, `lemma-lift-smooth-henselian`.
(blueprint: lem-trf-henselian-smooth-algebra-lifting)

Proof:
1. Put `B = A ⊗[R] S`, smooth over `A` by
   `lem-weil-pbc-smooth-ring-map-base-change-composition` (clause 1). The balanced formula
   `σ(a ⊗ s) = π(a) * τ(s)`, where `π : A → A/I`, defines an `A`-algebra map.
2. Use `lem-weil-pbc-smooth-ring-map-iff-smooth-affine` to obtain smoothness of
   `Spec B → Spec A`.
3. Apply `lem-weil-pbc-smooth-section-etale-lift` to get an étale `A`-algebra `A'`,
   the induced isomorphism `α : A/I ≃ A'/IA'`, and an `A`-algebra map `j : B → A'`
   with `q ∘ j = α ∘ σ`, where `q` is the quotient map of `A'`.
4. Apply `lem-weil-pbc-henselization-stage-map` to `A → A'`, the pair `(A, I)`, and
   the identity of `A`. This gives a retraction `r : A' → A`, an `A`-algebra map.
   For the single-universe inputs, place all rings in one common universe.
5. Since `r(f(i) * x) = i * r(x)`, the retraction induces `r̄ : A'/IA' → A/I`.
   The retraction identity gives `r̄ ∘ α = id`, hence `r̄ = α⁻¹`. The composite
   `s ↦ 1 ⊗ s ↦ j(1 ⊗ s) ↦ r(j(1 ⊗ s))` is the required `R`-algebra map:
   its reduction is `r̄(α(σ(1 ⊗ s))) = τ(s)`. -/
theorem exists_lift_of_henselianRing
    (R : Type u) [CommRing R]
    (S : Type v) [CommRing S] [Algebra R S] [Algebra.Smooth R S]
    (A : Type w) [CommRing A] [Algebra R A]
    (I : Ideal A) [HenselianRing A I] (τ : S →ₐ[R] A ⧸ I) :
    ∃ τ' : S →ₐ[R] A, (Ideal.Quotient.mkₐ R I).comp τ' = τ := by
  sorry

end Algebra.Smooth
