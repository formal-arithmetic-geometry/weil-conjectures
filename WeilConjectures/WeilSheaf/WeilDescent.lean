/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.ConstantFieldOfSmooth
public import WeilConjectures.WeilSheaf.WeilDescentConnected
public import WeilConjectures.WeilSheaf.WeilDescentConstantField

/-!
# Irreducible lisse Weil sheaves are twists of sheaves on the model

Let `V₀` be a smooth irreducible separated `k₀`-scheme of finite type. By Deligne (Weil II,
1.3.14), every irreducible lisse Weil sheaf `G` on `V₀` is, up to a constant twist by a unit
`b ∈ ℚ̄_ℓˣ`, the pullback `p^* H` of a lisse `ℓ`-adic sheaf `H` on `V₀` to the geometric fibre,
with its canonical Weil structure: some twist `G ⊗ 𝓑_{b⁻¹}` has a bounded Weil group action,
which extends continuously to `π₁(V₀)`.

## Main results

- `AlgebraicGeometry.WeilSheaf.IsIrreducibleLisse.exists_iso_constantTwist_geometricFiberPullback`.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.WeilSheaf

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
  {V : Scheme.{u}} [V.Over (Spec (CommRingCat.of k₀))]
  [IsSeparated (V ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (V ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (V ↘ Spec (CommRingCat.of k₀))] [Smooth (V ↘ Spec (CommRingCat.of k₀))]
  [IrreducibleSpace V] [IsAffine V]

open ProEtale in
/-- **Irreducible lisse Weil sheaves come from the model up to twist** (Deligne, Weil II,
1.3.14): on a smooth irreducible separated `k₀`-scheme `V₀` of finite type, every irreducible
lisse Weil sheaf is isomorphic to a constant twist `p^* H ⊗ 𝓑_b` of the pullback of a lisse
`ℓ`-adic sheaf `H` on `V₀`, with its canonical Weil structure. -/
theorem IsIrreducibleLisse.exists_iso_constantTwist_geometricFiberPullback
    {G : WeilSheaf k₀ l V} (hG : G.IsIrreducibleLisse) :
    ∃ (H : AdicSheaf l V) (hH : IsAdicLisseSheaf H) (b : (PadicAlgCl l)ˣ),
      Nonempty (G ≅ (geometricFiberPullback (k₀ := k₀) hH).constantTwist b) := by
  -- the separatedness and finiteness hypotheses of the statement are implied by smoothness and
  -- affineness
  have _ : IsSeparated (V ↘ Spec (CommRingCat.of k₀)) ∧
      LocallyOfFiniteType (V ↘ Spec (CommRingCat.of k₀)) ∧
      QuasiCompact (V ↘ Spec (CommRingCat.of k₀)) := ⟨‹_›, ‹_›, ‹_›⟩
  obtain ⟨k', _, _, _, c, hc, hsm, hgc⟩ := exists_constantField_of_smooth (V ↘ Spec (.of k₀))
  let : V.Over (Spec (.of k')) := ⟨c⟩
  have : Module.Finite k₀ k' := Module.Finite.of_finite
  obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero (Module.finrank_pos (R := k₀) (M := k')).ne'
  refine exists_iso_constantTwist_geometricFiberPullback_of_constantField hc hm
    (fun G' hG' ↦ ?_) hG
  have : Smooth (V ↘ Spec (.of k')) := hsm
  have : GeometricallyConnected (V ↘ Spec (.of k')) := hgc
  exact hG'.exists_iso_constantTwist_of_geometricallyConnected

end AlgebraicGeometry.WeilSheaf
