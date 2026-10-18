/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.ContinuousSheafPullback
public import WeilConjectures.SixFunctors.BaseChange.DerivedForget
public import WeilConjectures.SixFunctors.Etale.ConstantRingEndomorphisms
public import WeilConjectures.SixFunctors.ProEtale.Adic.FiniteAdicEtaleEquiv
public import WeilConjectures.SixFunctors.ProEtale.Comparison.UpperStar
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Iso

/-!
# Pullback along an automorphism and the comparison `Hⁿ(S_proét, ℤ/ℓᵐ) ≅ Extⁿ_Λ(Λ_S, Λ_S)`

Let `S` be a connected quasi-compact quasi-separated scheme, `e : S ≅ S` an automorphism (e.g.
the geometric Galois Frobenius of `X̄ = X ×_{k₀} k̄`) and `Λ = ℤ/ℓᵐ`. The comparison
`Extⁿ_Λ(Λ_S, Λ_S) ≅ Hⁿ(S_proét, ℤ_ℓ/ℓᵐ)` (`AlgebraicGeometry.ProEtale.extAddEquivFiniteAdicH`)
intertwines the pullback `e^*` of pro-étale cohomology
(`AlgebraicGeometry.ProEtale.finiteAdicHPullback`) with the pullback of `Ext`-classes along the
exact functor `e^*` on étale sheaves of `Λ`-modules, read through the identification
`e^* Λ_S ≅ Λ_S` underlying `Le^* Λ_S ≅ Λ_S`
(`AlgebraicGeometry.ProEtale.finiteAdicHPullback_extAddEquivFiniteAdicH`).

## Proof

`ν^* ∘ forget` commutes with the pullbacks up to a natural isomorphism, so both sides differ only
by morphisms on the two sides of the classes. As every endomorphism of `Λ_S` is a scalar and
`ν^* ∘ forget` is full on these, the two sides differ by an integer `c` independent of the degree
(`CategoryTheory.Abelian.Ext.exists_mk₀CompMk₀_mapExactFunctor_eq_zsmul`). In degree `0` both
pullbacks fix the class of the constant section `1`, whose order is `ℓᵐ`, so `c ≡ 1 mod ℓᵐ`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Abelian

namespace AlgebraicGeometry.ProEtale

open Scheme

variable (l : ℕ) [Fact l.Prime] (m : ℕ) {S : Scheme.{u}} (e : S ≅ S)

lemma surjective_intCast_ulift_zmod :
    Function.Surjective (Int.cast : ℤ → ULift.{u + 1} (ZMod (l ^ m))) := fun x ↦
  ⟨(ZMod.intCast_surjective x.down).choose, ULift.ext _ _ (by
    simpa using (ZMod.intCast_surjective x.down).choose_spec)⟩

/-- `ν^* ∘ forget` commutes with the pullbacks along `e`, the pro-étale one being the pushforward
along `e⁻¹`. -/
noncomputable def forgetComparisonUpperStarLowerStarIso :
    forgetComparisonUpperStar l m S ⋙ ProEtale.lowerStar AddCommGrpCat.{u + 1} e.inv ≅
      Etale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod (l ^ m)))) e.hom ⋙
        forgetComparisonUpperStar l m S :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _
      (Functor.isoWhiskerLeft _ (upperStarIsoLowerStarInv AddCommGrpCat.{u + 1} e).symm ≪≫
        comparisonUpperStarUpperStarIso AddCommGrpCat.{u + 1} e.hom) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (asIso (Etale.upperStarForget₂ (ULift.{u + 1} (ZMod (l ^ m))) e.hom).natTrans) _ ≪≫
    Functor.associator _ _ _

variable (S) in
/-- The class of the constant function `1` in `H⁰(S_proét, ℤ_ℓ/ℓᵐ)`. -/
noncomputable def finiteAdicHOne : FiniteAdicH S l m 0 :=
  Sheaf.H.map (continuousSheafMap S
    ⟨((zmodAddEquivQuotientPowOpenAddSubgroup l m).toAddMonoidHom.comp
      (Int.castAddHom (ZMod (l ^ m)))), continuous_of_discreteTopology⟩) 0
    (Ext.mk₀ (constantSheafIsoContinuousSheaf S ℤ).hom)

/-- The pullback fixes the class of the constant function `1`. -/
lemma finiteAdicHPullback_finiteAdicHOne :
    finiteAdicHPullback e l m 0 (finiteAdicHOne l m S) = finiteAdicHOne l m S := by
  refine (continuousSheafHPullback_map e _ 0 _).trans (congrArg _ ?_)
  rw [continuousSheafHPullback_apply, Ext.mapExactFunctor_mk₀, Ext.mk₀_comp_mk₀,
    Ext.mk₀_comp_mk₀]
  congr 1
  simp [constantIntIsoLowerStar, ← Functor.map_comp_assoc]

end AlgebraicGeometry.ProEtale
