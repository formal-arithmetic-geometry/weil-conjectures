module
public import Sheaf.FieldTheory.SeparableExtension
public import Mathlib.RingTheory.AlgebraicIndependent.Basic
public import Mathlib.RingTheory.Kaehler.Basic
@[expose] public section
universe u v
namespace KaehlerDifferential
/-- The basis-existence part of the separably generated differential theorem.

Source: Stacks Project, Algebra, the computation in the proof of Tag 031W,
expanded using Tags 00RX, 00RT, and 090W.

Proof: Write F = k(x_i) and P = k[X_i]. Algebraic independence makes evaluation
P → K injective. The fractions of polynomial values form exactly F: they constitute
a subfield containing k and every x_i, and each such fraction belongs to F. Thus F
is the fraction field of P. Tag 00RX gives the P-basis dX_i of Ω[P/k]. Tag 00RT
identifies Ω[F/k] with F ⊗[P] Ω[P/k], and sends 1 ⊗ dX_i to dx_i, giving an F-basis.
The transcendence-basis hypothesis makes K/F algebraic, and hxs makes it separable.
If K = k(a_1, ..., a_n) by hfg, then K = F(a_1, ..., a_n). Successively adjoining
these algebraic elements proves that K/F is finite. Tag 090W makes this finite
separable extension formally étale. The canonical differential base-change
isomorphism K ⊗[F] Ω[F/k] ≃ Ω[K/k] sends 1 ⊗ dx_i to dx_i. Transporting the
scalar-extended basis through it proves the assertion. For r = 0 the empty
polynomial basis localizes and extends to the empty basis of the zero module.
The global separability hypothesis hsep is redundant for this argument, but is
retained to match the target's assumptions.
(blueprint: new-separably-generated-differentials-basis) -/
theorem exists_basis_differentials_of_separating_transcendenceBasis_basis
    {k : Type u} {K : Type v} [Field k] [Field K] [Algebra k K]
    (hfg : (⊤ : IntermediateField k K).FG)
    (hsep : Algebra.IsSeparableExtension k K)
    {r : ℕ} (x : Fin r → K) (hx : IsTranscendenceBasis k x)
    (hxs : Algebra.IsSeparable (IntermediateField.adjoin k (Set.range x)) K) :
    ∃ b : Module.Basis (Fin r) K (KaehlerDifferential k K),
      ∀ i : Fin r, b i = D k K (x i) := by
  sorry
end KaehlerDifferential
