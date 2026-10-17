/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Adic.ProperBaseChange
public import WeilConjectures.WeilSheaf.LocalizationCompactification
public import WeilConjectures.WeilSheaf.LowerShriek

/-!
# `Rḡ_* ā_!` is the extension by zero

Let `j : U ⟶ X` be an open immersion of `k₀`-schemes with closed complement `i : Z ⟶ X`, and let
`U ⟶[a] W ⟶[g] X` be a compactification of `j`: an open immersion `a` followed by a proper
morphism `g`, with `W` Noetherian. For a Weil complex `M` on `U`, the complex `N = Rg_* (a_! M)`
of pro-étale Weil sheaves on `X` is the extension by zero `j_! M`
(`AlgebraicGeometry.ProEtaleWeilSheaf.nonempty_rightDerivedLowerStar_extensionByZero_iso`).

Indeed `j^* N ≅ M`
(`AlgebraicGeometry.ProEtaleWeilSheaf.nonempty_upperStar_rightDerivedLowerStar_extensionByZero_iso`),
and `i^* N = 0` by proper base change
(`AlgebraicGeometry.ProEtale.isZero_adicUpperStar_rightDerivedLowerStar_of_isProper`, on the
geometric fibers), the restriction of `a_! M` to `g⁻¹(Z)` being zero. So the open–closed
triangle `j_! j^* N ⟶ N ⟶ Ri_* i^* N ⟶` of `N`
(`AlgebraicGeometry.ProEtaleWeilSheaf.exists_distTriang_openClosed`) has third vertex zero, and
`N ≅ j_! j^* N ≅ j_! M`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Pretriangulated Endofunctor

namespace AlgebraicGeometry

open ProEtale

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime]



section Forget

variable {U W : Scheme.{u}} [U.Over (Spec (CommRingCat.of k₀))]
  [W.Over (Spec (CommRingCat.of k₀))] (a : U ⟶ W) [IsOpenImmersion a]
  [a.IsOver (Spec (CommRingCat.of k₀))]

variable (k₀ l) in
/-- Forgetting the Weil structure commutes with the extension by zero `a_!` on the derived
categories of pro-étale Weil sheaves: `For ∘ D(a_!) ≅ D(ā_!) ∘ For`. -/
noncomputable def ProEtaleWeilSheaf.mapDerivedCategoryExtensionByZeroCompForgetIso :
    (ProEtaleWeilSheaf.extensionByZero k₀ l a).mapDerivedCategory ⋙
        (IsoAlgebra.forget _).mapDerivedCategory ≅
      (IsoAlgebra.forget _).mapDerivedCategory ⋙
        (adicOpenImmersionLowerShriek l (Scheme.Hom.geometricFiberMap a
          (comp_over a (Spec (CommRingCat.of k₀))))).mapDerivedCategory :=
  (Functor.mapDerivedCategoryCompIso (ProEtaleWeilSheaf.extensionByZero k₀ l a)
      (IsoAlgebra.forget _)).symm ≪≫
    Functor.mapDerivedCategoryNatIso
      (Iso.refl (ProEtaleWeilSheaf.extensionByZero k₀ l a ⋙ IsoAlgebra.forget _) :
        ProEtaleWeilSheaf.extensionByZero k₀ l a ⋙ IsoAlgebra.forget _ ≅
          IsoAlgebra.forget _ ⋙ adicOpenImmersionLowerShriek l
            (Scheme.Hom.geometricFiberMap a (comp_over a (Spec (CommRingCat.of k₀))))) ≪≫
    Functor.mapDerivedCategoryCompIso (IsoAlgebra.forget _)
      (adicOpenImmersionLowerShriek l
        (Scheme.Hom.geometricFiberMap a (comp_over a (Spec (CommRingCat.of k₀)))))

end Forget

section Compactification

variable [Fact (ringChar k₀ ≠ l)]
variable {Z U W X : Scheme.{u}} [Z.Over (Spec (CommRingCat.of k₀))]
  [U.Over (Spec (CommRingCat.of k₀))] [W.Over (Spec (CommRingCat.of k₀))]
  [X.Over (Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]

/-- **`i^* Rg_* a_! M = 0`.** Let `U ⟶[a] W ⟶[g] X` be a factorization of an open immersion `j`
into a quasi-compact open immersion `a` and a proper morphism `g`, and let `i : Z ⟶ X` be a
closed immersion whose range misses that of `j`. For a Weil complex `M` on `U`,
`i^* Rg_* (a_! M) = 0`: on the geometric fibers, by proper base change
(`AlgebraicGeometry.ProEtale.isZero_adicUpperStar_rightDerivedLowerStar_of_isProper`), it is the
direct image of the restriction of `ā_! M̄` to `ḡ⁻¹(Z̄)`, which is zero as `ā(Ū)` lies over `Ū`. -/
theorem ProEtaleWeilSheaf.isZero_upperStar_rightDerivedLowerStar_extensionByZero
    (j : U ⟶ X) (i : Z ⟶ X) (a : U ⟶ W) (g : W ⟶ X) [IsOpenImmersion j] [IsClosedImmersion i]
    [IsOpenImmersion a] [QuasiCompact a] [IsProper g] [j.IsOver (Spec (CommRingCat.of k₀))]
    [i.IsOver (Spec (CommRingCat.of k₀))] [a.IsOver (Spec (CommRingCat.of k₀))]
    [g.IsOver (Spec (CommRingCat.of k₀))] (hag : a ≫ g = j)
    (hij : Disjoint (Set.range j.base) (Set.range i.base))
    (M : DerivedCategory (ProEtaleWeilSheaf k₀ l U)) (hM : WeilComplex.objectProperty k₀ l U M) :
    IsZero ((ProEtaleWeilSheaf.upperStar k₀ l i).mapDerivedCategory.obj
      ((ProEtaleWeilSheaf.lowerStar k₀ l g).rightDerivedFunctor.obj
        ((ProEtaleWeilSheaf.extensionByZero k₀ l a).mapDerivedCategory.obj M))) := by
  subst hag
  have := IsGrothendieckAbelian.hasColimitsOfShape_discrete.{u + 2, u + 1, u + 1}
    (ProEtale.AdicSheaf l (W ↘ Spec (CommRingCat.of k₀)).geometricFiber) ℤ
  have := IsGrothendieckAbelian.hasExactColimitsOfShape_discrete.{u + 2, u + 1, u + 1}
    (ProEtale.AdicSheaf l (W ↘ Spec (CommRingCat.of k₀)).geometricFiber) ℤ
  let E := (ProEtaleWeilSheaf.extensionByZero k₀ l a).mapDerivedCategory.obj M
  have hE : WeilComplex.objectProperty k₀ l W E :=
    ⟨(ProEtaleWeilSheaf.extensionByZero k₀ l a).bounded_mapDerivedCategory_obj hM.1,
      fun n ↦ (WeilSheaf.objectProperty k₀ l W).prop_of_iso
        (((ProEtaleWeilSheaf.extensionByZero k₀ l a).mapDerivedCategoryHomologyFunctorIso
          n).app M) (WeilSheaf.isAdicConstructibleSheaf_extensionByZero a _ (hM.2 n))⟩
  -- the base changes to the geometric fibers
  let gb := Scheme.Hom.geometricFiberMap g (comp_over g (Spec (CommRingCat.of k₀)))
  let ib := Scheme.Hom.geometricFiberMap i (comp_over i (Spec (CommRingCat.of k₀)))
  let ab := Scheme.Hom.geometricFiberMap a (comp_over a (Spec (CommRingCat.of k₀)))
  let jb := Scheme.Hom.geometricFiberMap (a ≫ g)
    (comp_over (a ≫ g) (Spec (CommRingCat.of k₀)))
  have : IsProper gb :=
    Scheme.Hom.geometricFiberMap_of_isStableUnderBaseChange (P := @IsProper) g _ inferInstance
  have hsq : IsPullback (pullback.fst gb ib) (pullback.snd gb ib) gb ib :=
    IsPullback.of_hasPullback gb ib
  have hjb : jb = ab ≫ gb := Scheme.Hom.geometricFiberMap_comp _ _ _ _
  have hd : Disjoint (Set.range jb.base) (Set.range ib.base) := by
    rw [Scheme.Hom.range_geometricFiberMap, Scheme.Hom.range_geometricFiberMap]
    exact hij.preimage _
  -- `ā(Ū)` misses `ḡ⁻¹(Z̄)`
  have hdisj : Set.range ab.base ∩ Set.range (pullback.fst gb ib).base = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    rintro _ ⟨⟨x, rfl⟩, ⟨p, hp⟩⟩
    have hc : gb.base ((pullback.fst gb ib).base p) = ib.base ((pullback.snd gb ib).base p) := by
      rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, pullback.condition]
    refine Set.disjoint_left.1 hd ⟨x, ?_⟩ ⟨(pullback.snd gb ib).base p, rfl⟩
    rw [← hc, hp, hjb, Scheme.Hom.comp_apply]
  refine ProEtaleWeilSheaf.isZero_of_isZero_forget _ ?_
  have hK := (WeilComplex.objectProperty_iff E).1 hE
  let fb := pullback.fst gb ib
  have h₁ : IsZero ((adicUpperStar l fb).mapDerivedCategory.obj
      ((IsoAlgebra.forget _).mapDerivedCategory.obj E)) := by
    refine IsZero.of_iso ?_ ((adicUpperStar l fb).mapDerivedCategory.mapIso
      ((ProEtaleWeilSheaf.mapDerivedCategoryExtensionByZeroCompForgetIso k₀ l a).app M))
    exact (Functor.isZero_mapDerivedCategory_obj
      (adicOpenImmersionLowerShriek l ab ⋙ adicUpperStar l fb) _
      fun F ↦ isZero_adicUpperStar_adicOpenImmersionLowerShriek _ _ hdisj F).of_iso
        (((adicOpenImmersionLowerShriek l ab).mapDerivedCategoryCompIso
          (adicUpperStar l fb)).symm.app _)
  have h₂ := isZero_adicUpperStar_rightDerivedLowerStar_of_isProper
    (X ↘ Spec (CommRingCat.of k₀)).geometricFiberToAlgebraicClosure ringChar_algebraicClosure_ne
    hsq _ hK h₁
  have h₃ := h₂.of_iso ((adicUpperStar l ib).mapDerivedCategory.mapIso
    ((IsoAlgebra.rightDerivedFunctorMapOfNatIsoCompForgetIso
      (e := adicLowerStarGeometricFiberMapCompFrobeniusIso l g (comp_over g _))).app E))
  exact h₃.of_iso ((ProEtaleWeilSheaf.mapDerivedCategoryUpperStarCompForgetIso k₀ l i).app _)

/-- **`Rg_* a_!` is the extension by zero.** Let `U ⟶[a] W ⟶[g] X` be a factorization of an
open immersion `j` into a quasi-compact open immersion `a` and a proper morphism `g`, with `W`
Noetherian, and let `i : Z ⟶ X` be the complementary closed immersion. For a Weil complex `M`
on `U`, `Rg_* (a_! M) ≅ j_! M`, where `j_!` is the left adjoint of `j^*` on pro-étale Weil sheaves
(`AlgebraicGeometry.ProEtaleWeilSheaf.upperStarLeftAdjoint`): the open–closed triangle of
`N = Rg_* (a_! M)` has third vertex `Ri_* i^* N = 0`
(`AlgebraicGeometry.ProEtaleWeilSheaf.isZero_upperStar_rightDerivedLowerStar_extensionByZero`),
so `N ≅ j_! j^* N`, and `j^* N ≅ M`. -/
theorem ProEtaleWeilSheaf.nonempty_rightDerivedLowerStar_extensionByZero_iso
    (j : U ⟶ X) (i : Z ⟶ X) (a : U ⟶ W) (g : W ⟶ X) [IsOpenImmersion j] [QuasiCompact j]
    [IsClosedImmersion i] [IsOpenImmersion a] [QuasiCompact a] [IsProper g] [IsNoetherian W]
    [j.IsOver (Spec (CommRingCat.of k₀))] [i.IsOver (Spec (CommRingCat.of k₀))]
    [a.IsOver (Spec (CommRingCat.of k₀))] [g.IsOver (Spec (CommRingCat.of k₀))] (hag : a ≫ g = j)
    (hij : IsCompl (Set.range j.base) (Set.range i.base))
    (M : DerivedCategory (ProEtaleWeilSheaf k₀ l U)) (hM : WeilComplex.objectProperty k₀ l U M) :
    Nonempty ((ProEtaleWeilSheaf.lowerStar k₀ l g).rightDerivedFunctor.obj
        ((ProEtaleWeilSheaf.extensionByZero k₀ l a).mapDerivedCategory.obj M) ≅
      (ProEtaleWeilSheaf.upperStarLeftAdjoint k₀ l j).mapDerivedCategory.obj M) := by
  let N := (ProEtaleWeilSheaf.lowerStar k₀ l g).rightDerivedFunctor.obj
    ((ProEtaleWeilSheaf.extensionByZero k₀ l a).mapDerivedCategory.obj M)
  obtain ⟨w, hw⟩ := ProEtaleWeilSheaf.exists_distTriang_openClosed j i hij.symm N
  have h₃ : IsZero ((ProEtaleWeilSheaf.lowerStar k₀ l i).rightDerivedFunctor.obj
      ((ProEtaleWeilSheaf.upperStar k₀ l i).mapDerivedCategory.obj N)) :=
    (ProEtaleWeilSheaf.lowerStar k₀ l i).rightDerivedFunctor.map_isZero
      (ProEtaleWeilSheaf.isZero_upperStar_rightDerivedLowerStar_extensionByZero j i a g hag
        hij.disjoint M hM)
  have hiso := (Triangle.isZero₃_iff_isIso₁ _ hw).1 h₃
  obtain ⟨e⟩ := ProEtaleWeilSheaf.nonempty_upperStar_rightDerivedLowerStar_extensionByZero_iso
    (k₀ := k₀) (l := l) j a g hag M
  exact ⟨(asIso ((ProEtaleWeilSheaf.derivedUpperStarLeftAdjointAdjunction k₀ l j).counit.app
    N)).symm ≪≫ (ProEtaleWeilSheaf.upperStarLeftAdjoint k₀ l j).mapDerivedCategory.mapIso e⟩

end Compactification

end AlgebraicGeometry
