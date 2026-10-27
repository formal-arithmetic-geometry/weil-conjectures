module

public import Mathlib.LinearAlgebra.StdBasis
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.Algebra.Group.Pi.Lemmas
public import Mathlib.Algebra.Group.Hom.Instances
public import Mathlib.GroupTheory.QuotientGroup.Basic

/-! # Graph edge labels modulo vertex coboundaries

Source: Stacks Project, Tag 0C1M, `lemma-glue-points`, units-sequence proof;
agent-written integral-lattice auxiliary motivated by that proof and by
Deligne–Mumford, Lemma 1.17, printed p. 86.
(blueprint: lem-sfb-finite-graph-cycle-character-quotient).
-/

@[expose] public section

set_option autoImplicit false

universe u v w

namespace FiniteGraphCycleCharacter

/-- The incidence map sends an edge basis vector to target minus source.
Source: agent lattice auxiliary for Stacks Tag 0C1M, units-sequence proof.
(blueprint: lem-sfb-finite-graph-cycle-character-quotient). -/
noncomputable def boundary {V : Type u} {E : Type v} [Finite V] [Finite E]
    (s t : E → V) : (E → ℤ) →ₗ[ℤ] (V → ℤ) :=
  (Pi.basisFun ℤ E).constr ℤ
    (fun e ↦ (Pi.basisFun ℤ V) (t e) - (Pi.basisFun ℤ V) (s e))

/-- Vertex coboundaries are target labels divided by source labels.
Source: Stacks Tag 0C1M, the map `ab⁻¹` in the units sequence.
(blueprint: lem-sfb-finite-graph-cycle-character-quotient). -/
def coboundary {V : Type u} {E : Type v} (s t : E → V)
    (A : Type w) [CommGroup A] : (V → A) →* (E → A) :=
  MonoidHom.pi (fun e ↦ Pi.evalMonoidHom (fun _ : V ↦ A) (t e) *
    (Pi.evalMonoidHom (fun _ : V ↦ A) (s e))⁻¹)

/-- Linear extension of the edge map `e ↦ ε(e) σ(e)`.
Source: agent lattice auxiliary for Stacks Tag 0C1M, signed equivariance step.
(blueprint: lem-sfb-finite-graph-cycle-character-quotient). -/
noncomputable def signedEdges {E : Type v} [Finite E]
    (σ : E → E) (ε : E → ℤ) : (E → ℤ) →ₗ[ℤ] (E → ℤ) :=
  (Pi.basisFun ℤ E).constr ℤ (fun e ↦ ε e • (Pi.basisFun ℤ E) (σ e))

/-- Edge labels modulo vertex coboundaries are precisely the multiplicative
characters of integral cycles, compatibly with signed permutations and reorientation.
Source: agent lattice auxiliary for Stacks Tag 0C1M, `lemma-glue-points`,
units-sequence proof; Deligne–Mumford, Lemma 1.17, printed p. 86.
(blueprint: lem-sfb-finite-graph-cycle-character-quotient).

Proof: (1) Use [lem-sfb-finite-graph-incidence-inner-inverse] to obtain `r` with
`∂r∂ = ∂`; then `p = 1-r∂` retracts the edge lattice onto its kernel.
(2) For `z`, the product `L_z(x) = ∏ e, z(e) ^ x(e)` is a character;
`L_{δa}(h) = ∏ v, a(v) ^ (∂h)(v) = 1` on cycles, so restriction descends.
(3) For a character `χ`, set `z(e) = χ(p(b_e))`. Expanding in the standard
basis gives `L_z(h) = χ(h)`, proving surjectivity for arbitrary coefficients.
(4) If restriction is trivial, `L_z(x) = L_z(r∂x)`; setting
`a(v) = L_z(r(b_v))` gives `δa = z`. Apply this to ratios for injectivity.
(5) Endpoint preservation gives `∂S_E = S_V∂`; thus the signed edge map
preserves cycles. Pullback carries `δa` to `δ(a ∘ σV)`, and evaluating gives
`L_{σ*z}(h) = L_z(S_E h)`, the signed equivariance formula.
(6) For reorientation, diagonal signs `η` give `∂old J = ∂new` and `J² = 1`.
Inversion in the reversed label coordinates takes old coboundaries to new ones,
is its own inverse, and satisfies `L_{z^η}(h) = L_z(Jh)`. -/
theorem quotientEquiv
    (V : Type u) (E : Type v) [Finite V] [Fintype E] [DecidableEq V]
    (s t : E → V) (_hne : ∀ e : E, s e ≠ t e) (A : Type w) [CommGroup A] :
    ∃ Φ : ((E → A) ⧸ (coboundary s t A).range) ≃*
        (Multiplicative (LinearMap.ker (boundary s t)) →* A),
      (∀ (z : E → A) (h : LinearMap.ker (boundary s t)),
        Φ (QuotientGroup.mk' (coboundary s t A).range z)
          (Multiplicative.ofAdd h) = ∏ e : E, z e ^ (h.val e)) ∧
      (∀ (σV : Equiv.Perm V) (σE : Equiv.Perm E),
        (∀ e : E,
          (s (σE e) = σV (s e) ∧ t (σE e) = σV (t e)) ∨
          (s (σE e) = σV (t e) ∧ t (σE e) = σV (s e))) →
        ∃ S : LinearMap.ker (boundary s t) →ₗ[ℤ] LinearMap.ker (boundary s t),
          (∀ h, (S h).val = signedEdges σE
            (fun e ↦ if s (σE e) = σV (s e) then 1 else -1) h.val) ∧
          (∀ (z : E → A) (h : LinearMap.ker (boundary s t)),
            Φ (QuotientGroup.mk' (coboundary s t A).range
                (fun e ↦ z (σE e) ^
                  (if s (σE e) = σV (s e) then (1 : ℤ) else -1)))
                (Multiplicative.ofAdd h) =
              Φ (QuotientGroup.mk' (coboundary s t A).range z)
                (Multiplicative.ofAdd (S h)))) ∧
      (∀ (s' t' : E → V),
        (∀ e : E, (s' e = s e ∧ t' e = t e) ∨ (s' e = t e ∧ t' e = s e)) →
        ∃ J : LinearMap.ker (boundary s' t') ≃ₗ[ℤ] LinearMap.ker (boundary s t),
        ∃ Ψ : ((E → A) ⧸ (coboundary s' t' A).range) ≃*
            ((E → A) ⧸ (coboundary s t A).range),
          (∀ h, (J h).val = signedEdges (fun e : E ↦ e)
            (fun e ↦ if s' e = s e then 1 else -1) h.val) ∧
          (∀ z : E → A,
            Ψ (QuotientGroup.mk' (coboundary s' t' A).range
              (fun e ↦ z e ^ (if s' e = s e then (1 : ℤ) else -1))) =
                QuotientGroup.mk' (coboundary s t A).range z) ∧
          (∀ (z : E → A) (h : LinearMap.ker (boundary s' t')),
            Φ (Ψ (QuotientGroup.mk' (coboundary s' t' A).range z))
                (Multiplicative.ofAdd (J h)) = ∏ e : E, z e ^ (h.val e))) := by
  sorry

end FiniteGraphCycleCharacter
