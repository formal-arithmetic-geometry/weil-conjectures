/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.EtaleCohomologyComparison
public import WeilConjectures.CategoryTheory.Abelian.Ext.MapExactFunctorConj
public import WeilConjectures.SixFunctors.Etale.ConstantCohomologyExtPullback
public import WeilConjectures.SixFunctors.ProEtale.Adic.FiniteAdicEtale

/-!
# The explicit comparison of `Hⁿ(S_proét, ℤ/ℓᵐ)` with `Hom(Λ_S, Λ_S[n])`

For a quasi-compact quasi-separated scheme `S` and `Λ = ℤ/ℓᵐ`, the chain of comparisons
`Hom_{D(S_ét, Λ)}(Λ_S, Λ_S[n]) ≅ Extⁿ_Λ(Λ_S, Λ_S) ≅ Hⁿ(S_ét, Λ) ≅ Hⁿ(S_proét, ν^* Λ)
≅ Hⁿ(S_proét, C(-, ℤ_ℓ/ℓᵐ))` is given by explicit additive equivalences
(`AlgebraicGeometry.ProEtale.extAddEquivFiniteAdicH`,
`AlgebraicGeometry.ProEtale.unitShiftAddEquivFiniteAdicH`), making
`AlgebraicGeometry.ProEtale.nonempty_addEquiv_finiteAdicH_unitShift` explicit. The composite
`Extⁿ_Λ(Λ_S, Λ_S) ≅ Hⁿ(S_proét, C(-, ℤ_ℓ/ℓᵐ))` is the pushforward of `Ext`-classes along the exact
functor `ν^* ∘ forget` composed with explicit morphisms on both sides
(`AlgebraicGeometry.ProEtale.extAddEquivFiniteAdicH_apply`).
-/

@[expose] public section

universe u

open CategoryTheory Limits Abelian

namespace CategoryTheory.Sheaf

variable {C : Type*} [Category C] {J : GrothendieckTopology C} [HasSheafify J AddCommGrpCat.{u}]
  [HasExt.{u} (Sheaf J AddCommGrpCat.{u})]

/-- The additive equivalence of cohomology groups induced by an isomorphism of sheaves. -/
noncomputable def H.mapAddEquiv {F G : Sheaf J AddCommGrpCat.{u}} (e : F ≅ G) (n : ℕ) :
    H F n ≃+ H G n where
  toFun := H.map e.hom n
  invFun := H.map e.inv n
  left_inv x := by rw [← H.map_comp_apply, e.hom_inv_id, H.map_id_apply]
  right_inv x := by rw [← H.map_comp_apply, e.inv_hom_id, H.map_id_apply]
  map_add' := map_add _

end CategoryTheory.Sheaf

namespace AlgebraicGeometry.ProEtale

open Scheme

variable (l : ℕ) [Fact l.Prime] (m : ℕ) (S : Scheme.{u})

/-- The coefficients `ℤ/ℓᵐ ≅ ℤ_ℓ/ℓᵐ`, as abelian groups. -/
noncomputable def zmodIsoQuotientPowOpenAddSubgroup :
    AddCommGrpCat.of (ULift.{u + 1} (ZMod (l ^ m))) ≅
      AddCommGrpCat.of
        (ULift.{u + 1} (ℤ_[l] ⧸ (PadicInt.powOpenAddSubgroup l m : AddSubgroup ℤ_[l]))) :=
  (AddEquiv.ulift.trans ((zmodAddEquivQuotientPowOpenAddSubgroup l m).trans
    AddEquiv.ulift.symm)).toAddCommGrpIso

/-- The underlying abelian sheaf of the constant étale sheaf `ℤ/ℓᵐ` is the constant abelian
sheaf `ℤ_ℓ/ℓᵐ`. -/
noncomputable def sheafForget₂ConstantRingIsoQuotient :
    (Etale.sheafForget₂ (ULift.{u + 1} (ZMod (l ^ m))) S).obj
        (Sheaf.constantRing S.smallEtaleTopology (ULift.{u + 1} (ZMod (l ^ m)))) ≅
      (constantSheaf S.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
        (AddCommGrpCat.of
          (ULift.{u + 1} (ℤ_[l] ⧸ (PadicInt.powOpenAddSubgroup l m : AddSubgroup ℤ_[l])))) :=
  Etale.sheafForget₂ConstantRingIso (ULift.{u + 1} (ZMod (l ^ m))) S ≪≫
    (constantSheaf S.smallEtaleTopology AddCommGrpCat.{u + 1}).mapIso
      (zmodIsoQuotientPowOpenAddSubgroup l m)

/-- The exact functor `ν^* ∘ forget` from étale sheaves of `ℤ/ℓᵐ`-modules to abelian
pro-étale sheaves. -/
noncomputable abbrev forgetComparisonUpperStar :
    Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod (l ^ m)))) ⥤
      Sheaf (ProEt.topology S) AddCommGrpCat.{u + 1} :=
  Etale.sheafForget₂ (ULift.{u + 1} (ZMod (l ^ m))) S ⋙
    comparisonUpperStar AddCommGrpCat.{u + 1} S

/-- `ν^*` of the underlying abelian sheaf of `ℤ/ℓᵐ` is `C(-, ℤ_ℓ/ℓᵐ)`. -/
noncomputable def forgetComparisonUpperStarConstantRingIso :
    (forgetComparisonUpperStar l m S).obj
        (Sheaf.constantRing S.smallEtaleTopology (ULift.{u + 1} (ZMod (l ^ m)))) ≅
      continuousSheaf S (ℤ_[l] ⧸ (PadicInt.powOpenAddSubgroup l m : AddSubgroup ℤ_[l])) :=
  (comparisonUpperStar AddCommGrpCat.{u + 1} S).mapIso
      (sheafForget₂ConstantRingIsoQuotient l m S) ≪≫
    (comparisonUpperStarConstantSheafIsoAddCommGrpCat S).app _ ≪≫
      constantSheafIsoContinuousSheaf S _

/-- The class `ℤ ⟶ ν^* Λ` of the section `1`. -/
noncomputable def forgetComparisonUpperStarUnit :
    (constantSheaf (ProEt.topology S) AddCommGrpCat.{u + 1}).obj
        (AddCommGrpCat.of (ULift.{u + 1} ℤ)) ⟶
      (forgetComparisonUpperStar l m S).obj
        (Sheaf.constantRing S.smallEtaleTopology (ULift.{u + 1} (ZMod (l ^ m)))) :=
  (constantIntIsoComparisonUpperStar S).hom ≫ (comparisonUpperStar AddCommGrpCat.{u + 1} S).map
    (Sheaf.constantIntToRing S.smallEtaleTopology (Etale.terminalEtaleIsTerminal S)
      (ULift.{u + 1} (ZMod (l ^ m))))

variable [CompactSpace S] [QuasiSeparatedSpace S]

/-- **`Extⁿ_Λ(Λ_S, Λ_S)` is `Hⁿ(S_proét, ℤ_ℓ/ℓᵐ)`**, `Λ = ℤ/ℓᵐ`: the composite of the
comparison of `Ext` over `Λ` with abelian étale cohomology, of the coefficients, and of étale
with pro-étale cohomology. -/
noncomputable def extAddEquivFiniteAdicH (n : ℕ) :
    Ext (Sheaf.constantRing S.smallEtaleTopology (ULift.{u + 1} (ZMod (l ^ m))))
        (Sheaf.constantRing S.smallEtaleTopology (ULift.{u + 1} (ZMod (l ^ m)))) n ≃+
      FiniteAdicH S l m n :=
  (AddEquiv.ofBijective _
    (Etale.bijective_mapExtComp_constantIntToRing (ULift.{u + 1} (ZMod (l ^ m))) S _ n)).trans
    ((Sheaf.H.mapAddEquiv (sheafForget₂ConstantRingIsoQuotient l m S) n).trans
      ((cohomologyComparisonAddEquiv S _ n).trans
        (Sheaf.H.mapAddEquiv ((comparisonUpperStarConstantSheafIsoAddCommGrpCat S).app _ ≪≫
          constantSheafIsoContinuousSheaf S _) n)))

/-- The comparison `Extⁿ_Λ(Λ_S, Λ_S) ≅ Hⁿ(S_proét, ℤ_ℓ/ℓᵐ)` is `y ↦ u ∘ (ν^* ∘ forget)(y) ∘ v`. -/
lemma extAddEquivFiniteAdicH_apply (n : ℕ)
    (y : Ext (Sheaf.constantRing S.smallEtaleTopology (ULift.{u + 1} (ZMod (l ^ m))))
      (Sheaf.constantRing S.smallEtaleTopology (ULift.{u + 1} (ZMod (l ^ m)))) n) :
    extAddEquivFiniteAdicH l m S n y =
      Ext.mk₀CompMk₀ (forgetComparisonUpperStarUnit l m S)
        (y.mapExactFunctor (forgetComparisonUpperStar l m S))
        (forgetComparisonUpperStarConstantRingIso l m S).hom := by
  simp only [extAddEquivFiniteAdicH, AddEquiv.trans_apply, AddEquiv.ofBijective_apply,
    Sheaf.H.mapAddEquiv, AddEquiv.coe_mk, Equiv.coe_fn_mk, cohomologyComparisonAddEquiv_apply]
  rw [Functor.mapExtComp_apply, Sheaf.H.map_apply, Ext.mk₀_comp_comp_mk₀,
    cohomologyComparison_apply, Ext.mapExactFunctor_mk₀CompMk₀, Ext.mk₀_comp_mk₀CompMk₀]
  refine (Ext.mk₀CompMk₀_comp_mk₀ _ _ _ _).trans ?_
  rw [Ext.mapExactFunctor_mapExactFunctor]
  rfl

end AlgebraicGeometry.ProEtale
