/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.ConstantFieldEquivalenceWeil

/-!
# Descent of irreducible lisse Weil sheaves along the constant field

Let `k₀ ⊆ k'` be finite fields with `[k' : k₀] = m + 1` and `V` a `k'`-scheme, regarded also as a
`k₀`-scheme. Weil sheaves on `V` relative to `k₀` and relative to `k'` are equivalent through the
first piece of the decomposition of `V ⊗_{k₀} k̄` into the Frobenius conjugates of
`V ⊗_{k'} k̄` (`AlgebraicGeometry.ProEtaleWeilSheaf.constantFieldFunctor`). This equivalence
preserves lisse and irreducible lisse sheaves, takes the pullback `π₀^* H` of a lisse sheaf on
`V` to `π'^* H`, and a constant twist by `b` to the constant twist by `b ^ (m + 1)`. Hence the
statement that irreducible lisse Weil sheaves are constant twists of pulled-back sheaves descends
from `k'` to `k₀`
(`AlgebraicGeometry.WeilSheaf.exists_iso_constantTwist_geometricFiberPullback_of_constantField`),
`ℚ̄_ℓ` being algebraically closed.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.WeilSheaf

open ProEtale

variable {k₀ k' : Type u} [Field k₀] [Field k'] [Finite k₀] [Finite k'] [Algebra k₀ k']
  {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)] {V : Scheme.{u}}
  [V.Over (Spec (CommRingCat.of k₀))] [V.Over (Spec (CommRingCat.of k'))]

/-- Constant twists of isomorphic Weil sheaves are isomorphic. -/
noncomputable def constantTwistIsoOfIso {k : Type u} [Field k] [Finite k] [Fact (ringChar k ≠ l)]
    {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k))] {F₁ F₂ : WeilSheaf k l X} (e : F₁ ≅ F₂)
    (b : (PadicAlgCl l)ˣ) : F₁.constantTwist b ≅ F₂.constantTwist b :=
  ObjectProperty.isoMk _ (constantTwistObjIso F₁ b ≪≫
    (ProEtaleWeilSheaf.constantTwist k l X b).mapIso ((ObjectProperty.ι _).mapIso e) ≪≫
    (constantTwistObjIso F₂ b).symm)

/-- **Descent of irreducible lisse Weil sheaves along the constant field.** If every irreducible
lisse Weil sheaf on `V` relative to the larger finite field `k'` is a constant twist of the
pullback of a lisse sheaf on `V`, then so is every irreducible lisse Weil sheaf on `V` relative to
`k₀`: the constant field equivalence `ProEtaleWeilSheaf.constantFieldFunctor` preserves irreducible
lisse sheaves, takes `π₀^* H` to `π'^* H` and the twist by `b` to the twist by `b ^ (m + 1)`, and
every unit of `ℚ̄_ℓ` has an `(m + 1)`-st root. -/
theorem exists_iso_constantTwist_geometricFiberPullback_of_constantField
    (hc : (V ↘ Spec (CommRingCat.of k')) ≫ Spec.map (CommRingCat.ofHom (algebraMap k₀ k')) =
      V ↘ Spec (CommRingCat.of k₀))
    {m : ℕ} (hm : Module.finrank k₀ k' = m + 1)
    (h : ∀ [Fact (ringChar k' ≠ l)] (G' : WeilSheaf k' l V), G'.IsIrreducibleLisse →
      ∃ (H : AdicSheaf l V) (hH : IsAdicLisseSheaf H) (b : (PadicAlgCl l)ˣ),
        Nonempty (G' ≅ (geometricFiberPullback (k₀ := k') hH).constantTwist b))
    {G : WeilSheaf k₀ l V} (hG : G.IsIrreducibleLisse) :
    ∃ (H : AdicSheaf l V) (hH : IsAdicLisseSheaf H) (b : (PadicAlgCl l)ˣ),
      Nonempty (G ≅ (geometricFiberPullback (k₀ := k₀) hH).constantTwist b) := by
  have : CharP k' (ringChar k₀) :=
    charP_of_injective_algebraMap (algebraMap k₀ k').injective (ringChar k₀)
  have : Fact (ringChar k' ≠ l) := ⟨by rw [ringChar.eq k' (ringChar k₀)]; exact Fact.out⟩
  obtain ⟨H, hH, b', ⟨e'⟩⟩ := h _ (hG.constantFieldFunctor hc hm)
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (b' : PadicAlgCl l) (Nat.succ_pos m)
  have hz0 : z ≠ 0 := by
    rintro rfl
    exact b'.ne_zero (by rw [← hz, zero_pow (Nat.succ_ne_zero m)])
  have hb : Units.mk0 z hz0 ^ (m + 1) = b' :=
    Units.ext (by rw [Units.val_pow_eq_pow_val, Units.val_mk0, hz])
  set ff := constantFieldFunctorFullyFaithful (l := l) hc hm
  refine ⟨H, hH, Units.mk0 z hz0, ⟨(ff.preimageIso
    (constantFieldFunctorConstantTwistIso hc hm _ _ ≪≫
      constantTwistIsoOfIso (constantFieldFunctorGeometricFiberPullbackIso hc hm hH) _ ≪≫
      eqToIso (congrArg (geometricFiberPullback (k₀ := k') hH).constantTwist hb) ≪≫ e'.symm)).symm⟩⟩

end AlgebraicGeometry.WeilSheaf
