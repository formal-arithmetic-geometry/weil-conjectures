/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.IntegralAdicLimit
public import WeilConjectures.SixFunctors.ProEtale.Adic.AdicConstantCup

/-!
# The cup product on `Hⁿ(S, ℤ/ℓᵐ)` as a Yoneda product

Write `Λ = ℤ/ℓᵐ` and `Fₘ = C(-, ℤ_ℓ/ℓᵐ)` for the corresponding abelian pro-étale sheaf. Every
class `b ∈ Hʲ(S, ℤ/ℓᵐ) = Extʲ(ℤ, Fₘ)` comes from a class `y ∈ Extʲ_Λ(Λ_S, Λ_S)`
(`AlgebraicGeometry.ProEtale.extAddEquivFiniteAdicH`), whose image under the exact functor
`ν^* ∘ forget` is a "multiplication by `b`" class `Lₘ b ∈ Extʲ(Fₘ, Fₘ)`
(`AlgebraicGeometry.ProEtale.finiteAdicMulLift`). The cup product is the Yoneda product
`a ⌣ b = a ∘ Lₘ b` (`AlgebraicGeometry.ProEtale.finiteAdicCup_eq_comp`).

Consequently the compatibility of the finite-level cup products with the transition maps
(`AlgebraicGeometry.ProEtale.FiniteAdicCupCompatible`) reduces to the compatibility of the
multiplication classes with the transition map `π : Fₘ₊₁ ⟶ Fₘ`, namely
`Lₘ₊₁ b ∘ π = π ∘ Lₘ (π b)` in `Extʲ(Fₘ₊₁, Fₘ)`
(`AlgebraicGeometry.ProEtale.finiteAdicCupCompatible_of_mulLift`).
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory Abelian

namespace AlgebraicGeometry.ProEtale

open Scheme

variable (l : ℕ) [Fact l.Prime] (m : ℕ) (S : Scheme.{u}) [CompactSpace S] [QuasiSeparatedSpace S]

/-- The multiplication class `Lₘ b ∈ Extʲ(Fₘ, Fₘ)` of `b ∈ Hʲ(S, ℤ/ℓᵐ)`, `Fₘ = C(-, ℤ_ℓ/ℓᵐ)`:
the image of the étale class of `b` under the exact functor `ν^* ∘ forget`. -/
noncomputable def finiteAdicMulLift (j : ℕ) :
    FiniteAdicH S l m j →+
      Ext (continuousSheaf S (ℤ_[l] ⧸ (PadicInt.powOpenAddSubgroup l m : AddSubgroup ℤ_[l])))
        (continuousSheaf S (ℤ_[l] ⧸ (PadicInt.powOpenAddSubgroup l m : AddSubgroup ℤ_[l]))) j :=
  AddMonoidHom.mk' (fun b ↦ Ext.mk₀CompMk₀ (forgetComparisonUpperStarConstantRingIso l m S).inv
      (((extAddEquivFiniteAdicH l m S j).symm b).mapExactFunctor (forgetComparisonUpperStar l m S))
      (forgetComparisonUpperStarConstantRingIso l m S).hom)
    fun b b' ↦ by rw [map_add, Ext.mapExactFunctor_add, Ext.mk₀CompMk₀_add]

lemma finiteAdicMulLift_extAddEquivFiniteAdicH (j : ℕ)
    (y : Ext (Sheaf.constantRing S.smallEtaleTopology (ULift.{u + 1} (ZMod (l ^ m))))
      (Sheaf.constantRing S.smallEtaleTopology (ULift.{u + 1} (ZMod (l ^ m)))) j) :
    finiteAdicMulLift l m S j (extAddEquivFiniteAdicH l m S j y) =
      Ext.mk₀CompMk₀ (forgetComparisonUpperStarConstantRingIso l m S).inv
        (y.mapExactFunctor (forgetComparisonUpperStar l m S))
        (forgetComparisonUpperStarConstantRingIso l m S).hom := by
  rw [finiteAdicMulLift, AddMonoidHom.mk'_apply, AddEquiv.symm_apply_apply]

/-- The comparison `Extⁿ_Λ(Λ_S, Λ_S) ≅ Hⁿ(S, ℤ/ℓᵐ)` turns Yoneda products into products with
the multiplication classes. -/
lemma extAddEquivFiniteAdicH_comp (i j k : ℕ) (h : i + j = k)
    (x : Ext (Sheaf.constantRing S.smallEtaleTopology (ULift.{u + 1} (ZMod (l ^ m))))
      (Sheaf.constantRing S.smallEtaleTopology (ULift.{u + 1} (ZMod (l ^ m)))) i)
    (y : Ext (Sheaf.constantRing S.smallEtaleTopology (ULift.{u + 1} (ZMod (l ^ m))))
      (Sheaf.constantRing S.smallEtaleTopology (ULift.{u + 1} (ZMod (l ^ m)))) j) :
    extAddEquivFiniteAdicH l m S k (x.comp y h) =
      Ext.comp (C := Sheaf (ProEt.topology S) AddCommGrpCat.{u + 1})
        (extAddEquivFiniteAdicH l m S i x)
        (finiteAdicMulLift l m S j (extAddEquivFiniteAdicH l m S j y)) h := by
  rw [extAddEquivFiniteAdicH_apply, extAddEquivFiniteAdicH_apply,
    finiteAdicMulLift_extAddEquivFiniteAdicH, Ext.mk₀CompMk₀_comp_mk₀CompMk₀,
    Ext.mapExactFunctor_comp]

set_option maxHeartbeats 1600000 in
-- the derived categories of étale sheaves make unification slow
/-- **The cup product on `Hⁿ(S, ℤ/ℓᵐ)` is a Yoneda product**: `a ⌣ b = a ∘ Lₘ b`. -/
theorem finiteAdicCup_eq_comp (i j k : ℕ) (h : i + j = k) (a : FiniteAdicH S l m i)
    (b : FiniteAdicH S l m j) :
    finiteAdicCup l m S i j k h a b =
      Ext.comp (C := Sheaf (ProEt.topology S) AddCommGrpCat.{u + 1}) a
        (finiteAdicMulLift l m S j b) h := by
  obtain ⟨x, rfl⟩ := (unitShiftAddEquivFiniteAdicH l m S i).surjective a
  obtain ⟨y, rfl⟩ := (unitShiftAddEquivFiniteAdicH l m S j).surjective b
  rw [finiteAdicCup_apply, AddEquiv.symm_apply_apply, AddEquiv.symm_apply_apply]
  simp only [unitShiftAddEquivFiniteAdicH, AddEquiv.trans_apply]
  rw [unitShiftAddEquivExt_cupProduct _ _ _ h, extAddEquivFiniteAdicH_comp]

/-- **Reduction of the compatibility of the cup products with the transition maps** to the
compatibility `Lₘ₊₁ b ∘ π = π ∘ Lₘ (π b)` of the multiplication classes with the transition map
`π : Fₘ₊₁ ⟶ Fₘ`. -/
theorem finiteAdicCupCompatible_of_mulLift
    (hL : ∀ (m j : ℕ) (b : FiniteAdicH S l (m + 1) j),
      (finiteAdicMulLift l (m + 1) S j b).comp (Ext.mk₀ (continuousSheafMap S
          (openAddSubgroupQuotientMap (PadicInt.powOpenAddSubgroup l)
            (PadicInt.powOpenAddSubgroup_succ_le l) m))) (add_zero j) =
        (Ext.mk₀ (continuousSheafMap S
          (openAddSubgroupQuotientMap (PadicInt.powOpenAddSubgroup l)
            (PadicInt.powOpenAddSubgroup_succ_le l) m))).comp
          (finiteAdicMulLift l m S j (finiteAdicTransition S l m j b)) (zero_add j)) :
    FiniteAdicCupCompatible l S := by
  intro m i j k h a b
  rw [finiteAdicCup_eq_comp, finiteAdicCup_eq_comp]
  refine (Ext.comp_assoc_of_third_deg_zero _ _ _ h).trans ?_
  rw [hL]
  exact (Ext.comp_assoc_of_second_deg_zero _ _ _ h).symm

end AlgebraicGeometry.ProEtale
