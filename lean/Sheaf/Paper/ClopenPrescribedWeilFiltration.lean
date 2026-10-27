/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q06
-/
module

public import Sheaf.Paper.AdicPunctualWeights
public import Sheaf.Paper.SfWeilSheafComplex
public import Sheaf.Paper.SfConstructibleHeart
public import Sheaf.Paper.DerivedPullbackTensorHom
public import Sheaf.Paper.QcqsCompactSupportRealization
public import Sheaf.Paper.SfDerivedDirectImage
public import Sheaf.Paper.WeilIndSheafCategory
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-! # Prescribed Weil filtrations on a finite clopen decomposition

Source: literature/blueprint/latest/blueprint/sec-deligne-laumon-general/
sk-i-dl-general-real/thm-zl-real-mixed-by-curves.proof.md, penultimate paragraph
(blueprint: lem-zl-clopen-prescribed-weil-filtration).

The actual common-stage Weil heart, its canonical inverse image and open extension
by zero are used throughout. Extension by zero is specified by its adjunction
with canonical restriction, which determines it up to unique compatible isomorphism.
The position of a quotient is its component's prefix
sum plus its within-component index. Thus the labels retain their given order.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped BigOperators
namespace WeilConjectures

/-- Concatenate the prescribed component filtrations, with exactly their original
pure quotient weights and exactly the sum of their lengths. The component indices
are zero-based, so the quotient in position (b,s) has index sum_{c<b} n_c + s.
An increasing chain of monomorphisms ending in H represents a filtration by its
constructible Weil subobjects. Endpoint isomorphisms avoid choosing representatives.
The existential functors J are the extensions by zero: their adjunctions to the
specified open restrictions characterize them up to unique compatible isomorphism.

Source: blueprint latest, thm-zl-real-mixed-by-curves.proof.md, penultimate paragraph
(blueprint: lem-zl-clopen-prescribed-weil-filtration).

Proof, following the six DAG steps:
1. The finite-clopen derived decomposition, identified with actual pullback by
   lem-pur-open-completed-restriction-identification and compatible scalar extension
   by lem-pur-integral-operations-scalar-extension, gives an equivalence on the
   common-stage categories. Immersion pullback is t-exact, so it restricts to hearts.
   The normalized Frobenius square and lem-fd-fixed-pair-equivalence-transport lift
   it to the Weil hearts. This additive equivalence detects subobjects and quotients
   (lem-zl-weil-heart-localization-exact).
2. Under this equivalence h_b! is insertion in component b and zero elsewhere:
   the normalized Weil open adjunction unit identifies its b-coordinate with the
   input, and the other coordinates vanish (lem-zl-open-weil-unit-and-empty-fibre).
   Open extension is exact by lem-zl-immersion-weil-local-behavior.
3. At component b and step s take all of H_c before b, the prescribed G_b,s at b,
   and zero after b. Lift the resulting subobject through the equivalence. The
   block endpoints coincide, giving a chain of exactly sum_b n_b arrows from zero
   to H. A block of length zero has zero restriction and contributes no arrows.
4. The coordinatewise cokernel of each inclusion is Q_b,s in component b and zero
   elsewhere. Preservation of cokernels and step 2 identify it as a Weil object
   with the actual h_b! Q_b,s. The prefix-sum formula retains the prescribed order.
5. The stalk and Frobenius of open extension inside its support are the original
   stalk and Frobenius with the same residue-field size; outside, the stalk is zero
   (lem-zl-immersion-weil-local-behavior). Purity of each assigned real weight follows
   from def-weil-punctual-weights and is invariant under Weil isomorphism. Every
   common upper bound therefore yields the stated mixedness bound for H.
6. Repeated terms have zero quotient, pure of every assigned weight. Empty pieces
   carry only zero objects. With no components the cover forces S to be empty,
   its Weil heart has only zero objects, and the filtration has length zero
   (lem-zl-weil-heart-localization-exact). No nonzero or positive-length assumption
   is needed, and no equality or ordering of weights is used. -/
theorem clopen_prescribed_weil_filtration
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    (iota : Ω ≃+* ℂ)
    (S₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType S₀.hom] [QuasiCompact S₀.hom] [IsSeparated S₀.hom]
    (N : ℕ) (V₀ : Fin N → Over (Spec (.of D.k₀)))
    [∀ b, LocallyOfFiniteType (V₀ b).hom] [∀ b, QuasiCompact (V₀ b).hom]
    [∀ b, IsSeparated (V₀ b).hom]
    (h₀ : ∀ b, V₀ b ⟶ S₀)
    [∀ b, IsOpenImmersion (h₀ b).left] [∀ b, IsClosedImmersion (h₀ b).left]
    (cover : ⋃ b, Set.range (h₀ b).left = Set.univ)
    (disjoint : ∀ b c, b ≠ c → Disjoint (Set.range (h₀ b).left) (Set.range (h₀ c).left))
    (H : sfCommonStageWeilSheaf D l hl S₀ Ω)
    (n : Fin N → ℕ)
    (G : ∀ b, Fin (n b + 1) → sfCommonStageWeilSheaf D l hl (V₀ b) Ω)
    (φ : ∀ (b : Fin N) (s : Fin (n b)), G b s.castSucc ⟶ G b s.succ)
    (weights : ∀ b, Fin (n b) → ℝ)
    (start : ∀ b, IsZero (G b 0))
    (finish : ∀ b, Nonempty (G b (Fin.last (n b)) ≅ (zlWeilPull D l hl Ω (h₀ b)).obj H))
    (inclusions : ∀ b s, Mono (φ b s))
    (pure : ∀ b s, SfIsPunctuallyPureOfWeight D l hl Ω (V₀ b) iota
      (cokernel (φ b s)) (weights b s)) :
    ∃ (J : ∀ b : Fin N, sfCommonStageWeilSheaf D l hl (V₀ b) Ω ⥤
        sfCommonStageWeilSheaf D l hl S₀ Ω)
      (_adj : ∀ b, J b ⊣ zlWeilPull D l hl Ω (h₀ b)),
    ∃ (F : Fin ((∑ b, n b) + 1) → sfCommonStageWeilSheaf D l hl S₀ Ω)
      (ψ : ∀ t : Fin (∑ b, n b), F t.castSucc ⟶ F t.succ)
      (position : ∀ b, Fin (n b) → Fin (∑ c, n c)),
      IsZero (F 0) ∧ Nonempty (F (Fin.last (∑ b, n b)) ≅ H) ∧
      (∀ t, Mono (ψ t)) ∧
      (∀ b s, (position b s).val = (∑ c : Fin N, if c < b then n c else 0) + s.val) ∧
      (∀ b s, Nonempty (cokernel (ψ (position b s)) ≅
          (J b).obj (cokernel (φ b s))) ∧
        SfIsPunctuallyPureOfWeight D l hl Ω S₀ iota
          (cokernel (ψ (position b s))) (weights b s)) ∧
      (∀ w : ℝ, (∀ b s, weights b s ≤ w) →
        SfIsMixedOfWeightsAtMost D l hl Ω S₀ iota H w) ∧
      (N = 0 → IsEmpty S₀.left ∧ IsZero H) := by
  sorry

end WeilConjectures
