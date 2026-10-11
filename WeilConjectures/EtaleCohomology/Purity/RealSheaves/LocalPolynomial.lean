/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafRepresentation
public import WeilConjectures.EtaleCohomology.Purity.RealSheaves.Weights

/-!
# Local Frobenius polynomials of lisse Weil sheaves

Let `ℱ` be a lisse Weil sheaf on a curve `C₀` over a finite field, with Weil fundamental
representation `(V, ρ)` under the lisse sheaf–representation equivalence
(`AlgebraicGeometry.WeilGroup.exists_equivalence_isLisse`). The local characteristic factor
`P_x(ℱ, T) = det (1 - T F_x ∣ ℱ_x̄)` at a closed point `x` is `det (1 - T ρ(g) ∣ V)` for every
member `g` of the Frobenius conjugacy class of `x` in the Weil group (blueprint
`p-real-operations`).

## Main statements

- `AlgebraicGeometry.WeilGroup.exists_equivalence_localPolynomial_stalk`: the local polynomials
  of a lisse Weil sheaf are those of its Weil fundamental representation.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

namespace WeilGroup

variable {K : Type u} [Field K] [Finite K] {C : Scheme.{u}} [C.Over (Spec (.of K))]
  [IsCurve (C ↘ Spec (.of K))] (W : WeilGroup (C ↘ Spec (.of K))) (l : ℕ) [Fact l.Prime]
  [Fact (ringChar K ≠ l)]

/-- Blueprint `p-real-operations`: Local Frobenius polynomials.

Under the lisse sheaf–representation equivalence `ℱ ↦ (V, ρ)` of
`AlgebraicGeometry.WeilGroup.exists_equivalence_isLisse`, the local characteristic factor
`P_x(ℱ, T) = det (1 - T F_x ∣ ℱ_x̄)` of a lisse Weil sheaf `ℱ` at a closed point `x` is
`det (1 - T ρ(g) ∣ V)` for every `g ∈ W(C₀)` conjugate to the local Frobenius element at `x`:
the stalk `ℱ_x̄` with `F_x` is `V` with `ρ (Frob_x)`, and a characteristic polynomial is invariant
under conjugation (`AlgebraicGeometry.WeilGroup.localPolynomial_eq_charpolyRev_of_isConj`).
The operations on lisse Weil sheaves are transported along this equivalence. -/
theorem exists_equivalence_localPolynomial_stalk :
    ∃ e : ObjectProperty.FullSubcategory (fun F : WeilSheaf K l C ↦ F.IsLisse) ≌
        ObjectProperty.FullSubcategory (W.isLisseRep l),
      ∀ (F : ObjectProperty.FullSubcategory (fun F : WeilSheaf K l C ↦ F.IsLisse))
        (x : C.finitePoints) (g : W.carrier), IsConj (W.frobenius x) g →
        haveI := (e.functor.obj F).property.1
        (F.obj.stalk x).localPolynomial = ((e.functor.obj F).obj.ρ g).charpolyRev := by
  obtain ⟨e, hst, -, -⟩ := W.exists_equivalence_isLisse l
  refine ⟨e, fun F x g hg ↦ ?_⟩
  have := (e.functor.obj F).property.1
  obtain ⟨f, hf⟩ := hst F x
  rw [← localPolynomial_eq_charpolyRev_of_isConj hg, localPolynomial,
    FrobeniusModule.localPolynomial, LinearMap.charpolyRev_def, LinearMap.charpolyRev_def]
  exact congrArg Polynomial.reverse
    (LinearMap.charpoly_eq_of_comp_eq f (LinearMap.ext fun v ↦ hf v))

end WeilGroup

end AlgebraicGeometry
