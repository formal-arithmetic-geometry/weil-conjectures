/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.Purity.RealSheaves.LocalSystems
public import WeilConjectures.WeilSheaf.Dual

/-!
# Lisse Weil sheaves and lisse Weil representations

Let `C₀` be a curve over the finite field `K` with Weil group `W = W(C₀)`
(`AlgebraicGeometry.WeilGroup`). This file connects the two sides of the purity theorem for
real sheaves: the sheaf side, lisse Weil sheaves `AlgebraicGeometry.WeilSheaf` on `C₀` with
their geometric stalks, local Frobenius, global sections and geometric coinvariants, and the
representation side, lisse representations of `W(C₀)`.

The lisse sheaf–representation equivalence (`prop-wf-weil-sheaf-representation-equivalence`,
`AlgebraicGeometry.WeilGroup.exists_equivalence_isLisse`) sends a lisse Weil sheaf `ℱ` to its
Weil fundamental representation `(V, ρ) = (ℱ_η̄, ρ_ℱ)`. From it we deduce that every lisse
representation `ρ` of `W(C₀)` is the fundamental representation of a lisse Weil sheaf `ℱ`
whose local Frobenius at a closed point `x` has the characteristic polynomial of
`ρ (Frob_x)`, and whose geometric coinvariants `Γ(C̄, ℱ^∨)^∨`
(`AlgebraicGeometry.WeilSheaf.geometricCoinvariants`) are the coinvariants `V_{π₁(C)}` with the
Frobenius induced by the degree-one lift `γ`
(`AlgebraicGeometry.WeilGroup.exists_weilSheaf_of_isLisse`).

## Main statements

- `AlgebraicGeometry.WeilGroup.exists_equivalence_isLisse`: the lisse sheaf–representation
  equivalence.
- `AlgebraicGeometry.WeilGroup.exists_weilSheaf_of_isLisse`: the lisse Weil sheaf of a lisse
  representation, with its stalks and its geometric coinvariants.

## Implementation notes

The Weil fundamental representation of `def-wf-fundamental-representation` is the geometric
generic stalk `ℱ_η̄` with the monodromy action of `π₁(C₀, η̄)` extended to the Weil group by the
Weil structure. Neither the monodromy action of the étale fundamental group on a stalk of an
`ℓ`-adic pro-étale sheaf nor the functor `ℱ ↦ ρ_ℱ` is available, so the equivalence is
existentially quantified, and the fact that it *is* the Weil fundamental representation is
recorded by the properties of it that the blueprint uses: at a closed point `x`, the stalk
`ℱ_x̄` with its local Frobenius `F_x` is `V` with `ρ (Frob_x)` (the stalk at `x̄` being
transported to the base point along a path, which carries the geometric Frobenius of `κ(x)` to
the Frobenius element `Frob_x` of `W(C₀)`); the equivalence is compatible with duals (it is a
tensor equivalence); and the global sections `H⁰(C̄, ℱ)` are the invariants `V ^ {π₁(C)}` with
the Frobenius `ρ (γ)`, which is `p-real-sections` for `U₀ = C₀`. The last clause is a
consequence of the equivalence in the blueprint (`p-real-sections`); it is recorded with it here
because the functor, being existentially quantified, can only be described through its
properties.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

namespace WeilGroup

variable {K : Type u} [Field K] [Finite K] {C : Scheme.{u}} [C.Over (Spec (.of K))]
  [IsCurve (C ↘ Spec (.of K))] (W : WeilGroup (C ↘ Spec (.of K))) (l : ℕ) [Fact l.Prime]
  [Fact (ringChar K ≠ l)]

/-- Blueprint `prop-wf-weil-sheaf-representation-equivalence` (subsection `sk-i-real-sheaves`):
The lisse sheaf–representation equivalence.

The functor `ℱ ↦ (V, ρ) = (ℱ_η̄, ρ_ℱ)`, sending a lisse Weil sheaf on the curve `C₀` to its Weil
fundamental representation (`def-wf-fundamental-representation`), is an exact tensor
equivalence between lisse Weil sheaves on `C₀` and lisse representations of `W(C₀)`
(`AlgebraicGeometry.WeilGroup.isLisseRep`). The functor `e.functor` is the Weil fundamental
representation:

* at every closed point `x`, the geometric stalk `ℱ_x̄` with its local Frobenius `F_x` is
  isomorphic to `V` with `ρ (Frob_x)`, `Frob_x = W.frobenius x` being a Frobenius element at `x`
  (`def-wf-fundamental-representation`, the stalk at `x̄` transported to the base point along a
  path);
* it is compatible with duals: the representation of `ℱ^∨` is the contragredient of that of `ℱ`;
* the global sections `H⁰(C̄, ℱ)` are the invariants `V ^ {π₁(C)}`, compatibly with the
  Frobenius `ρ (γ)` of the degree-one lift `γ` (`p-real-sections`, for `U₀ = C₀`). -/
theorem exists_equivalence_isLisse :
    ∃ e : ObjectProperty.FullSubcategory (fun F : WeilSheaf K l C ↦ F.IsLisse) ≌
        ObjectProperty.FullSubcategory (W.isLisseRep l),
      (∀ (F : ObjectProperty.FullSubcategory (fun F : WeilSheaf K l C ↦ F.IsLisse))
          (x : C.finitePoints),
        ∃ f : (F.obj.stalk x).carrier ≃ₗ[PadicAlgCl l] (e.functor.obj F).obj.V,
          ∀ v, f ((F.obj.stalk x).frobenius v) = (e.functor.obj F).obj.ρ (W.frobenius x) (f v)) ∧
      (∀ F : ObjectProperty.FullSubcategory (fun F : WeilSheaf K l C ↦ F.IsLisse),
        Nonempty ((e.functor.obj ⟨F.obj.dual F.property, F.property.dual⟩).obj.ρ.Equiv
          (e.functor.obj F).obj.ρ.dual)) ∧
      (∀ F : ObjectProperty.FullSubcategory (fun F : WeilSheaf K l C ↦ F.IsLisse),
        ∃ f : F.obj.globalSections.carrier ≃ₗ[PadicAlgCl l]
            ((e.functor.obj F).obj.ρ.comp W.geometric.subtype).invariants,
          ∀ v, (f (F.obj.globalSections.frobenius v) : (e.functor.obj F).obj.V) =
            (e.functor.obj F).obj.ρ W.frobeniusLift (f v)) := by
  sorry

end WeilGroup

end AlgebraicGeometry
