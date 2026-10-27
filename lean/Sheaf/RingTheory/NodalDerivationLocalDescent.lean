module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.LocalRing.ResidueField.Defs
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.PowerSeries.Derivative
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.RingTheory.TensorProduct.Maps
import WeilConjectures.RingTheory.Derivation.CompletionAndLocalization
import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
import Mathlib.RingTheory.AdicCompletion.LocalRing
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra

/-!
# Extension and descent of derivations at a completed node

Source: Stacks Project, curves.tex, Tag 0E68 (lemma-nodal-vector-fields), local argument;
more-algebra.tex, Tag 07PE (lemma-derivation-extends).
(blueprint: lem-sfb-nodal-derivation-local-descent)
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u v

open scoped TensorProduct

namespace RingTheory

/-- Evaluation on the two formal axes, written coefficientwise before passing to `(uv)`.
Source: Stacks Project, curves.tex, Tag 0E68, completed local calculation.
(blueprint: lem-sfb-nodal-derivation-local-descent) -/
noncomputable def nodalAxes {k : Type u} [CommRing k]
    (h : MvPowerSeries (Fin 2) k) : PowerSeries k × PowerSeries k :=
  (PowerSeries.mk fun n => MvPowerSeries.coeff (Finsupp.single 0 n) h,
   PowerSeries.mk fun n => MvPowerSeries.coeff (Finsupp.single 1 n) h)

/-- The explicit pair `(uf ∂u, vg ∂v)` on the completed normalization.
Source: Stacks Project, curves.tex, Tag 0E68, completed local calculation.
(blueprint: lem-sfb-nodal-derivation-local-descent) -/
noncomputable def nodalAxisAction {k : Type u} [CommRing k]
    (f g : PowerSeries k) (p : PowerSeries k × PowerSeries k) :
    PowerSeries k × PowerSeries k :=
  (PowerSeries.X * f * PowerSeries.derivative k p.1,
   PowerSeries.X * g * PowerSeries.derivative k p.2)

/-- Derivations preserving the two branch ideals, as an actual additive subgroup.
Source: Stacks Project, curves.tex, Tag 0E68, fixed-branch condition.
(blueprint: lem-sfb-nodal-derivation-local-descent) -/
def branchPreservingDerivations {k : Type u} {B : Type v}
    [CommRing k] [CommRing B] [Algebra k B] (n₀ n₁ : Ideal B) :
    AddSubgroup (Derivation k B B) where
  carrier := {d | (∀ b ∈ n₀, d b ∈ n₀) ∧ (∀ b ∈ n₁, d b ∈ n₁)}
  zero_mem' := ⟨fun _ _ => n₀.zero_mem, fun _ _ => n₁.zero_mem⟩
  add_mem' hd he :=
    ⟨fun b hb => n₀.add_mem (hd.1 b hb) (he.1 b hb),
     fun b hb => n₁.add_mem (hd.2 b hb) (he.2 b hb)⟩
  neg_mem' hd :=
    ⟨fun b hb => n₀.neg_mem (hd.1 b hb), fun b hb => n₁.neg_mem (hd.2 b hb)⟩

/-- Local extension and descent at a node, including its fraction, localization,
completion and faithful-flat membership compatibilities.

Source: Stacks Project, curves.tex, Tag 0E68 (lemma-nodal-vector-fields), forward and
reverse local arguments; more-algebra.tex, Tag 07PE (lemma-derivation-extends).
(blueprint: lem-sfb-nodal-derivation-local-descent)

Proof:
1. Put `R = Â` and `S = nonZeroDivisors A`. Faithful flatness of local completion and
flatness preserve the inclusions `A ⊆ B ⊆ Q(A)` after tensoring, giving
`R ⊆ P ⊆ E = Q(A) ⊗ R = S⁻¹R`. Tensoring multiplication by each `s ∈ S` shows it
remains regular on `R` and `P`; hence also `S⁻¹P = E`.
2. Tensor the quotient sequences for `Q(A)/B` and `B/A`. Their exactness and universal
injectivity under faithful flatness imply the two asserted membership equivalences.
No finite generation of these quotient modules is needed.
3. Extend a derivation to `R` and `Q(A)` by Tag 07PE. The estimate
`d(I^(r+1)) ⊆ I^r` makes these completion extensions continuous. Completion modulo
powers identifies their filtrations with the usual nodal and branch filtrations.
4. In the equal-constant presentation, differentiating `uv = 0` forces the opposite
branch components of `d(u), d(v)` to vanish; equality of constants then forces
`d(u) = uf` and `d(v) = vg`. Shifting coefficients constructs `f,g`, without division
by integers and in every characteristic.
5. Polynomial truncation and continuity show `d(h) = h' d(t)` on each branch.
The formal derivative satisfies Leibniz by finite convolution. Thus the pair
`(uf ∂u, vg ∂v)` is a continuous derivation of `P`, with both residue composites zero,
and restricts to the completed derivation on the equal-constant subring.
6. Localize this pair to `E`. The quotient formula identifies its restriction on
`Q(A)` with the unique fraction extension. Its values on `B` lie in `P`, hence in
`B` by step 2. This constructs the forward extension and proves its zero residues.
7. Conversely a derivation of `B` preserving both branch ideals has zero residues:
subtract the scalar residue before applying it. Complete it along `mB`; the residue
composites remain zero by the one-step filtration estimate. A derivation kills
idempotents, since `(1-2e)^2 = 1`, including in characteristic two. Consequently it
acts separately on the factors of `P`, and truncation gives the same displayed pair.
It preserves equal constants; step 2 then implies it preserves `A`.
8. Restrict to `A`. Uniqueness of localization to `S⁻¹B = Q(A)` proves uniqueness of
extension and that extension and restriction are inverse. Restriction and the quotient
formula are additive. The same formula after further localization proves all the
localization commutations, even when a multiplicative set contains zero.
-/
theorem nodal_derivation_local_descent
    {k : Type u} [Field k] [IsAlgClosed k]
    {A : Type v} [CommRing A] [Algebra k A] [IsLocalRing A]
    [IsNoetherianRing A] [IsReduced A]
    (B : Subalgebra A (FractionRing A)) (hB : B = integralClosure A (FractionRing A))
    [Module.Finite A B]
    (ρA : (A ⧸ IsLocalRing.maximalIdeal A) ≃ₐ[k] k)
    (n₀ n₁ : Ideal B) (hn₀ : n₀.IsMaximal) (hn₁ : n₁.IsMaximal) (hne : n₀ ≠ n₁)
    (hmax : ∀ n : Ideal B, n.IsMaximal → n = n₀ ∨ n = n₁)
    (ρ₀ : (B ⧸ n₀) ≃ₐ[k] k) (ρ₁ : (B ⧸ n₁) ≃ₐ[k] k)
    (eA : AdicCompletion (IsLocalRing.maximalIdeal A) A ≃ₐ[k]
      (MvPowerSeries (Fin 2) k ⧸ Ideal.span
        {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) k) * MvPowerSeries.X 1}))
    (eB : AdicCompletion ((IsLocalRing.maximalIdeal A).map (algebraMap A B)) B ≃ₐ[k]
      (PowerSeries k × PowerSeries k))
    (eT : (B ⊗[A] AdicCompletion (IsLocalRing.maximalIdeal A) A) ≃ₐ[k]
      (PowerSeries k × PowerSeries k))
    (hBT : ∀ b : B, eB (algebraMap B _ b) = eT (b ⊗ₜ[A] 1))
    (haxes : ∀ h : MvPowerSeries (Fin 2) k,
      eT (1 ⊗ₜ[A] eA.symm (Ideal.Quotient.mk _ h)) = nodalAxes h)
    (hρ₀ : ∀ b : B, ρ₀ (Ideal.Quotient.mk n₀ b) =
      PowerSeries.constantCoeff (eT (b ⊗ₜ[A] 1)).1)
    (hρ₁ : ∀ b : B, ρ₁ (Ideal.Quotient.mk n₁ b) =
      PowerSeries.constantCoeff (eT (b ⊗ₜ[A] 1)).2) :
    (∃ F : Derivation k A A ≃+ branchPreservingDerivations (k := k) n₀ n₁,
      (∀ (D : Derivation k A A) (a : A),
        (F D).val (algebraMap A B a) = algebraMap A B (D a)) ∧
      (∀ (d : branchPreservingDerivations (k := k) n₀ n₁) (a : A),
        algebraMap A B (F.symm d a) = d.val (algebraMap A B a)) ∧
      (∀ (D : Derivation k A A) (b : B),
        ρ₀ (Ideal.Quotient.mk n₀ ((F D).val b)) = 0 ∧
        ρ₁ (Ideal.Quotient.mk n₁ ((F D).val b)) = 0) ∧
      (∀ D : Derivation k A A,
        ∀ d : Derivation k B B,
        (∀ a : A, d (algebraMap A B a) = algebraMap A B (D a)) → d = (F D).val) ∧
      (∀ D : Derivation k A A,
        ∃ DQ : Derivation k (FractionRing A) (FractionRing A),
          (∀ b : B, DQ b.val = ((F D).val b).val) ∧
          (∀ (a : A) (s : nonZeroDivisors A),
            DQ (Localization.mk a s) = Localization.mk (D a) s -
              Localization.mk (a * D (s : A)) (s ^ 2))) ∧
      (∀ D : Derivation k A A,
        ∃ f g : PowerSeries k,
        ∃ δ : Derivation k (PowerSeries k × PowerSeries k) (PowerSeries k × PowerSeries k),
        ∃ δA : Derivation k (AdicCompletion (IsLocalRing.maximalIdeal A) A)
          (AdicCompletion (IsLocalRing.maximalIdeal A) A),
          (∀ p, δ p = nodalAxisAction f g p) ∧
          (∀ b : B, δ (eB (algebraMap B _ b)) = eB (algebraMap B _ ((F D).val b))) ∧
          (∀ a : A, δA (algebraMap A _ a) = algebraMap A _ (D a)) ∧
          (∀ r, δ (eT (1 ⊗ₜ[A] r)) = eT (1 ⊗ₜ[A] δA r)) ∧
          (∀ p : PowerSeries k × PowerSeries k,
            PowerSeries.constantCoeff p.1 = PowerSeries.constantCoeff p.2 →
            PowerSeries.constantCoeff (δ p).1 = PowerSeries.constantCoeff (δ p).2) ∧
          (∀ N : ℕ, ∃ M : ℕ, ∀ p q : PowerSeries k × PowerSeries k,
            (∀ j < M, PowerSeries.coeff j p.1 = PowerSeries.coeff j q.1 ∧
              PowerSeries.coeff j p.2 = PowerSeries.coeff j q.2) →
            ∀ j < N, PowerSeries.coeff j (δ p).1 = PowerSeries.coeff j (δ q).1 ∧
              PowerSeries.coeff j (δ p).2 = PowerSeries.coeff j (δ q).2)) ∧
      (∀ (D : Derivation k A A) (S : Submonoid A) (T : Submonoid B),
        ∃ DS : Derivation k (Localization S) (Localization S),
        ∃ DT : Derivation k (Localization T) (Localization T),
          (∀ (a : A) (s : S), DS (Localization.mk a s) =
            Localization.mk (D a) s - Localization.mk (a * D (s : A)) (s ^ 2)) ∧
          (∀ (b : B) (t : T), DT (Localization.mk b t) =
            Localization.mk ((F D).val b) t -
              Localization.mk (b * (F D).val (t : B)) (t ^ 2)) ∧
          (∀ ℓ : Localization S →ₐ[k] Localization T,
            (∀ a : A, ℓ (algebraMap A _ a) = algebraMap B _ (algebraMap A B a)) →
            ∀ x, DT (ℓ x) = ℓ (DS x)))) ∧
    (∀ q : FractionRing A,
      (∃ p : B ⊗[A] AdicCompletion (IsLocalRing.maximalIdeal A) A,
        TensorProduct.map B.val.toLinearMap LinearMap.id p = q ⊗ₜ[A] 1) ↔ q ∈ B) ∧
    (∀ b : B,
      (∃ r : AdicCompletion (IsLocalRing.maximalIdeal A) A,
        eT (b ⊗ₜ[A] 1) = eT (1 ⊗ₜ[A] r)) ↔ ∃ a : A, algebraMap A B a = b) := by
  sorry

end RingTheory
