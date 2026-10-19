/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q80
-/
module

public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
public import Mathlib.Topology.Algebra.Valued.ValuationTopology
public import WeilConjectures.Mathlib.RingTheory.Henselian
import Mathlib.FieldTheory.Galois.Infinite
import Sheaf.FieldTheory.HenselianFiniteExtensionTopology

/-!
# Krasner neighbourhoods over henselian valued fields

Source: Illusie--Laszlo--Orgogozo, Travaux de Gabber, Exposé XX, section 4.4,
printed page 374, forms of Krasner's lemma, referring to Bourbaki, Algèbre
commutative VI, section 8, exercises 12 and 14(a)
(blueprint: lem-per-henselian-krasner-neighbourhood).

Mathlib's valuations are multiplicative: additive infinity becomes zero and
`w (α - β) > w (α - σ α)` becomes `vN.v (α - β) < vN.v (α - σ α)`.
`Valued` supplies precisely the valuation topology. The valuation integer subring
is `{x | vF.v x ≤ 1}`, corresponding to the additive valuation ring.
-/

@[expose] public section

set_option autoImplicit false

universe u v a

namespace FieldTheory

/-- Krasner's lemma and its open-neighbourhood consequence for a finite Galois
extension of a nontrivially valued field with henselian valuation ring. There is
no completeness, rank-one, or discreteness assumption.

Source: ILO, Travaux de Gabber, Exposé XX, section 4.4, printed page 374,
forms of Krasner's lemma; Bourbaki, Algèbre commutative VI, section 8,
exercises 12 and 14(a). The finite-Galois proof below is agent-written, as
recorded in the node (blueprint: lem-per-henselian-krasner-neighbourhood).

Proof (the node's five steps, expressed multiplicatively):
1. Let `G = Aut_F(N)` and `O = {x | vN.v x ≤ 1}`. For each `σ ∈ G`, the
   valuation `vN.v ∘ σ` prolongs `vF.v`. The uniqueness clause of
   `lem-per-henselian-finite-extension-topology` makes its valuation subring
   equal to `O`, so `σ⁻¹(O) = O`.
2. By `lem-weil-pbc-finite-galois-fixed-field`, `G` is finite and every `σ`
   has finite order. For nonzero `b`, `vN.v a ≤ vN.v b` is equivalent to
   `a / b ∈ O`. Step 1 therefore makes `σ` preserve all comparisons of
   values. If `vN.v (σ x)` were strictly larger or strictly smaller than
   `vN.v x`, iterating the comparison up to the order of `σ` would give a
   strict inequality from `vN.v x` to itself. Thus `σ` preserves values;
   the case `x = 0` follows from preservation of zero.
3. If `σ β = β` but `σ α ≠ α`, put `d = α - β`. Then
   `vN.v (σ α - β) = vN.v d` by Step 2. The ultrametric inequality gives
   `vN.v (α - σ α) ≤ max (vN.v d) (vN.v (σ d)) = vN.v d`, contradicting
   the strict hypothesis. This also handles `d = 0`.
4. The subgroup fixing `β` is the subgroup fixing `F(β)` pointwise: fixed
   elements form a subfield containing `F` and `β`. By
   `lem-exc-etale-galois-fixed-field-subgroup` its fixed field is exactly
   `F(β)`, and Step 3 places `α` in this fixed field.
5. There are finitely many nonidentity conjugates of `α`. If there are any,
   take the minimum `r` of their nonzero difference values and the open ball
   `U = {β | vN.v (α - β) < r}`. It contains `α`, and Step 4 applies to
   every point of it. If there are none, the fixed-field clause of
   `lem-weil-pbc-finite-galois-fixed-field` gives `α ∈ F`; take `U = N`,
   since `F ⊆ F(β)` for all `β`. Conversely `α ∈ F` makes every automorphism
   fix `α`, so this is also the specified choice whenever `α ∈ F`.
-/
theorem henselianKrasnerNeighbourhood
    (F : Type u) (N : Type v) [Field F] [Field N] [Algebra F N]
    (Γ : Type a) [LinearOrderedCommGroupWithZero Γ]
    [vF : Valued F Γ] [vN : Valued N Γ]
    [HenselianLocalRing vF.v.integer]
    [FiniteDimensional F N] [IsGalois F N]
    (h_nontrivial : ∃ x : F, x ≠ 0 ∧ vF.v x ≠ 1)
    (h_prolong : ∀ x : F, vN.v (algebraMap F N x) = vF.v x) :
    ∀ α : N,
      (∀ β : N,
        (∀ σ : N ≃ₐ[F] N, σ α ≠ α →
          vN.v (α - β) < vN.v (α - σ α)) →
        α ∈ IntermediateField.adjoin F ({β} : Set N)) ∧
      ∃ U : Set N,
        IsOpen U ∧ α ∈ U ∧
          (∀ β : N, β ∈ U → α ∈ IntermediateField.adjoin F ({β} : Set N)) ∧
          (α ∈ Set.range (algebraMap F N) → U = Set.univ) := by
  sorry

end FieldTheory
