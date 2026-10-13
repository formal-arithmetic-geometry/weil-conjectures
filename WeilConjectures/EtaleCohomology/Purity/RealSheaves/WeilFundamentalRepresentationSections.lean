/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.Purity.RealSheaves.WeilFundamentalRepresentation

/-!
# Global sections and invariants of the Weil fundamental representation

For a lisse Weil sheaf `ℱ` on a curve `C₀`, restriction to the stalk at the base point `t`
identifies the global sections `Γ(C, ℱ)` of `ℱ` on the geometric curve with the invariants
`V^{π₁(C)}` of its Weil fundamental representation `(V, ρ)`, compatibly with the Frobenius of
the global sections and `ρ(γ)` for any element `γ` of degree one
(`AlgebraicGeometry.WeilGroup.exists_globalSections_linearEquiv_invariants`).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.WeilGroup

open ProEtale Scheme.FiniteEtale

variable {K : Type u} [Field K] [Finite K] {C : Scheme.{u}} [C.Over (Spec (.of K))]
  {l : ℕ} [Fact l.Prime] [Fact (ringChar K ≠ l)] [IsCurve (C ↘ Spec (.of K))]
  {W : WeilGroup (C ↘ Spec (.of K))}
  {M : LisseMonodromy l (C ↘ Spec (.of K)).geometricFiber (AlgebraicClosure K)}
  {B : BasePointData W} (D : WeilMonodromyData B)

/-- **Global sections are invariants**: restriction to the stalk at the base point identifies the
global sections `Γ(C, ℱ)` of a lisse Weil sheaf with the `π₁(C)`-invariants of its Weil
fundamental representation, carrying the Frobenius of the global sections to the action of an
element `γ` of degree one. -/
theorem exists_globalSections_linearEquiv_invariants (hM : M.IsEquivalenceAt B.t)
    (F : WeilSheaf K l C) (hF : F.IsLisse) (γ : W.carrier)
    (hγ : W.deg γ = Multiplicative.ofAdd 1) :
    ∃ f : F.globalSections.carrier ≃ₗ[PadicAlgCl l]
        Representation.invariants ((fundamentalRep M D F hF).comp W.geometric.subtype),
      ∀ v, (f (F.globalSections.frobenius v) : LisseMonodromy.StalkSpace B.t (F.toLisse hF)) =
        fundamentalRep M D F hF γ (f v) := by
  sorry

end AlgebraicGeometry.WeilGroup
