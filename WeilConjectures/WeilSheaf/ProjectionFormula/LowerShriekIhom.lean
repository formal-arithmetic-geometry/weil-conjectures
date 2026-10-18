/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.ProjectionFormula.LowerStarIhom
public import WeilConjectures.WeilSheaf.LowerShriek
public import WeilConjectures.WeilSheaf.FourierTateTwist.ConstantTwist
public import WeilConjectures.WeilSheaf.ProjectionFormula.DualPullbackWeil

/-!
# Direct image with compact support and internal homs out of lisse sheaves

For a compactification `X ⟶[i] Z ⟶[g] Y` of a morphism `f` of `k₀`-schemes and a pro-étale
Weil sheaf `A` on `Y` with lisse underlying sheaf, the direct image with compact support
`Rf_! = Rg_* ∘ i_!` commutes with the derived internal homs,
`Rf_! R[f^* A, -] ≅ R[A, -] Rf_!`, provided the extension by zero `i_!` commutes with the
internal hom out of `g^* A` on the underived level
(`AlgebraicGeometry.ProEtaleWeilSheaf.nonempty_rightDerivedLowerShriek_comp_ihom_iso`). The
derived pushforward `Rg_*` commutes with the derived internal homs by
`AlgebraicGeometry.ProEtaleWeilSheaf.nonempty_rightDerivedLowerStarCompIhomFunctorIso`, and for
the exact functors `i_!` and `[g^* A, -]` the derived statement follows from the underived one.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.ProEtaleWeilSheaf

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime]

/-- The extension by zero along an open immersion `j` commutes with the derived internal homs
out of a lisse sheaf `M` if it does so on the underived level, all functors involved being
exact. -/
theorem nonempty_mapDerivedCategory_extensionByZero_comp_ihom_iso {U Z : Scheme.{u}}
    [U.Over (Spec (CommRingCat.of k₀))] [Z.Over (Spec (CommRingCat.of k₀))] (j : U ⟶ Z)
    [IsOpenImmersion j] [j.IsOver (Spec (CommRingCat.of k₀))] (M : ProEtaleWeilSheaf k₀ l Z)
    (hM : ProEtale.IsAdicLisseSheaf M.carrier)
    (e : extensionByZero k₀ l j ⋙ ihomFunctor k₀ l Z M ≅
      ihomFunctor k₀ l U ((upperStar k₀ l j).obj M) ⋙ extensionByZero k₀ l j) :
    Nonempty ((extensionByZero k₀ l j).mapDerivedCategory ⋙
        (ihomFunctor k₀ l Z M).rightDerivedFunctor ≅
      (ihomFunctor k₀ l U ((upperStar k₀ l j).obj M)).rightDerivedFunctor ⋙
        (extensionByZero k₀ l j).mapDerivedCategory) := by
  have := preservesFiniteColimits_ihomFunctor M hM
  have := preservesFiniteColimits_ihomFunctor ((upperStar k₀ l j).obj M)
    (hM.upperStar (Scheme.Hom.geometricFiberMap j (comp_over j (Spec (CommRingCat.of k₀)))))
  exact ⟨Functor.isoWhiskerLeft _ (ihomFunctor k₀ l Z M).rightDerivedFunctorIsoMapDerivedCategory ≪≫
    (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫ Functor.mapDerivedCategoryNatIso e ≪≫
    Functor.mapDerivedCategoryCompIso _ _ ≪≫
    Functor.isoWhiskerRight
      (ihomFunctor k₀ l U ((upperStar k₀ l j).obj M)).rightDerivedFunctorIsoMapDerivedCategory.symm
      _⟩

attribute [local instance] Compactification.over

/-- **Direct image with compact support and internal homs out of lisse sheaves**: for a
compactification `X ⟶[i] Z ⟶[g] Y` of `f` and `A` with lisse underlying sheaf,
`Rf_! R[i^* g^* A, -] ≅ R[A, -] Rf_!`, provided `i_! [i^* g^* A, -] ≅ [g^* A, -] i_!` on the
underived level. -/
theorem nonempty_rightDerivedLowerShriek_comp_ihom_iso [Fact (ringChar k₀ ≠ l)] {X Y : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of k₀))] [Y.Over (Spec (CommRingCat.of k₀))] (f : X ⟶ Y)
    [f.IsOver (Spec (CommRingCat.of k₀))] (c : Compactification f) (A : ProEtaleWeilSheaf k₀ l Y)
    (hA : ProEtale.IsAdicLisseSheaf A.carrier) [IsOpenImmersion c.i]
    (hU2 :
      Nonempty (extensionByZero k₀ l c.i ⋙ ihomFunctor k₀ l c.Z ((upperStar k₀ l c.g).obj A) ≅
        ihomFunctor k₀ l X ((upperStar k₀ l c.i).obj ((upperStar k₀ l c.g).obj A)) ⋙
          extensionByZero k₀ l c.i)) :
    Nonempty (rightDerivedLowerShriek k₀ l f c ⋙ (ihomFunctor k₀ l Y A).rightDerivedFunctor ≅
      (ihomFunctor k₀ l X
        ((upperStar k₀ l c.i).obj ((upperStar k₀ l c.g).obj A))).rightDerivedFunctor ⋙
        rightDerivedLowerShriek k₀ l f c) := by
  obtain ⟨e₁⟩ := nonempty_rightDerivedLowerStarCompIhomFunctorIso c.g A hA
  obtain ⟨e₀⟩ := hU2
  obtain ⟨e₂⟩ := nonempty_mapDerivedCategory_extensionByZero_comp_ihom_iso c.i
    ((upperStar k₀ l c.g).obj A)
    (hA.upperStar (Scheme.Hom.geometricFiberMap c.g (comp_over c.g (Spec (CommRingCat.of k₀)))))
    e₀
  unfold rightDerivedLowerShriek
  exact ⟨Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _ e₁ ≪≫
    (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight e₂ _ ≪≫ Functor.associator _ _ _⟩

end AlgebraicGeometry.ProEtaleWeilSheaf

namespace CategoryTheory.ObjectProperty

variable {C D D' E : Type*} [Category* C] [Category* D] [Category* D'] [Category* E]
  {P : ObjectProperty C} {Q : ObjectProperty D} {Q' : ObjectProperty D'} {R : ObjectProperty E}

/-- Isomorphic composites of functors induce isomorphic composites of the induced functors
between full subcategories. -/
theorem nonempty_liftFullSubcategory_comp_iso {F₁ : C ⥤ D} {G₁ : D ⥤ E} {F₂ : C ⥤ D'}
    {G₂ : D' ⥤ E} (hF₁ : ∀ X, P X → Q (F₁.obj X)) (hG₁ : ∀ X, Q X → R (G₁.obj X))
    (hF₂ : ∀ X, P X → Q' (F₂.obj X)) (hG₂ : ∀ X, Q' X → R (G₂.obj X))
    (e : F₁ ⋙ G₁ ≅ F₂ ⋙ G₂) :
    Nonempty (P.liftFullSubcategory Q F₁ hF₁ ⋙ Q.liftFullSubcategory R G₁ hG₁ ≅
      P.liftFullSubcategory Q' F₂ hF₂ ⋙ Q'.liftFullSubcategory R G₂ hG₂) :=
  ⟨NatIso.ofComponents (fun K ↦ R.isoMk (e.app K.obj))
    fun g ↦ R.hom_ext (e.hom.naturality g.hom)⟩

end CategoryTheory.ObjectProperty

namespace AlgebraicGeometry.WeilComplex

open ProEtaleWeilSheaf

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]

attribute [local instance] Compactification.over

omit [Fact (ringChar k₀ ≠ l)] in
/-- Pullbacks along equal morphisms are isomorphic. -/
theorem nonempty_proEtaleWeilSheaf_upperStar_iso_of_eq {X Y : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of k₀))]
    [Y.Over (Spec (CommRingCat.of k₀))] {f f' : X ⟶ Y} [f.IsOver (Spec (CommRingCat.of k₀))]
    [f'.IsOver (Spec (CommRingCat.of k₀))] (h : f = f') :
    Nonempty (ProEtaleWeilSheaf.upperStar k₀ l f ≅ ProEtaleWeilSheaf.upperStar k₀ l f') := by
  subst h
  exact ⟨Iso.refl _⟩

omit [Fact (ringChar k₀ ≠ l)] in
/-- The pullback along `f` is the pullback along the open immersion of a compactification of
`f` after the pullback along its proper part. -/
theorem nonempty_upperStar_compactification_iso {X Y : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of k₀))] [Y.Over (Spec (CommRingCat.of k₀))] (f : X ⟶ Y)
    [f.IsOver (Spec (CommRingCat.of k₀))] (c : Compactification f) (A : ProEtaleWeilSheaf k₀ l Y) :
    Nonempty ((ProEtaleWeilSheaf.upperStar k₀ l f).obj A ≅
      (ProEtaleWeilSheaf.upperStar k₀ l c.i).obj
        ((ProEtaleWeilSheaf.upperStar k₀ l c.g).obj A)) := by
  obtain ⟨ψ⟩ := nonempty_proEtaleWeilSheaf_upperStar_iso_of_eq (k₀ := k₀) (l := l) c.comm
  exact ⟨ψ.app A ≪≫ (ProEtaleWeilSheaf.upperStarCompIso k₀ l c.i c.g).app _⟩

/-- **The projection formula for Weil complexes, from its two non-formal inputs**:
`Rf₀!(K) ⊗ G ≅ Rf₀!(K ⊗ f^* G)` for a lisse Weil sheaf `G`, assuming that the extension by zero
along open immersions commutes with internal homs out of lisse sheaves (`hU2`) and that the
dual of `G` commutes with the pullback along `f` (`hP4`). The derived pushforward along the
proper part of the compactification commutes with internal homs formally
(`AlgebraicGeometry.ProEtaleWeilSheaf.nonempty_rightDerivedLowerShriek_comp_ihom_iso`). -/
theorem nonempty_iso_derivedLowerShriek_tensorLisse_of_nonempty {X Y : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of k₀))] [Y.Over (Spec (CommRingCat.of k₀))] (f : X ⟶ Y)
    [f.IsOver (Spec (CommRingCat.of k₀))] [IsSeparated f] [LocallyOfFiniteType f]
    [QuasiCompact f] [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))]
    [QuasiSeparated (Y ↘ Spec (CommRingCat.of k₀))] (G : WeilSheaf k₀ l Y) (hG : G.IsLisse)
    (hU2 : ∀ {Z : Scheme.{u}} [Z.Over (Spec (CommRingCat.of k₀))] (j : X ⟶ Z) [IsOpenImmersion j]
      [j.IsOver (Spec (CommRingCat.of k₀))] (M : ProEtaleWeilSheaf k₀ l Z),
      ProEtale.IsAdicLisseSheaf M.carrier →
        Nonempty (extensionByZero k₀ l j ⋙ ihomFunctor k₀ l Z M ≅
          ihomFunctor k₀ l X ((ProEtaleWeilSheaf.upperStar k₀ l j).obj M) ⋙
            extensionByZero k₀ l j))
    (hP4 : Nonempty ((ProEtaleWeilSheaf.upperStar k₀ l f).obj (G.dual hG).obj ≅
      (((WeilSheaf.upperStar f).obj G).dual (ProEtale.IsAdicLisseSheaf.upperStar _ hG)).obj)) :
    Nonempty (derivedLowerShriek k₀ l f ⋙ tensorLisse G hG ≅
      tensorLisse ((WeilSheaf.upperStar f).obj G) (ProEtale.IsAdicLisseSheaf.upperStar _ hG) ⋙
        derivedLowerShriek k₀ l f) := by
  let c := HasCompactification.compactification f (hf := hasCompactification_of_over (k₀ := k₀) f)
  have := c.isOpenImmersion
  have hA : ProEtale.IsAdicLisseSheaf (G.dual hG).obj.carrier := hG.dual
  obtain ⟨E⟩ := nonempty_rightDerivedLowerShriek_comp_ihom_iso f c (G.dual hG).obj hA
    (hU2 c.i _ (hA.upperStar
      (Scheme.Hom.geometricFiberMap c.g (comp_over c.g (Spec (CommRingCat.of k₀))))))
  obtain ⟨φ⟩ := hP4
  obtain ⟨ψ⟩ := nonempty_upperStar_compactification_iso f c (G.dual hG).obj
  unfold derivedLowerShriek tensorLisse ihomLisse
  exact ObjectProperty.nonempty_liftFullSubcategory_comp_iso _ _ _ _
    (E ≪≫ Functor.isoWhiskerRight
      (Functor.rightDerivedFunctorNatIso (ihomFunctorMapIsoLeft (φ.symm ≪≫ ψ))) _)

/-- **The projection formula for Weil complexes, from the compatibility of extension by zero
with internal homs**: `Rf₀!(K) ⊗ G ≅ Rf₀!(K ⊗ f^* G)` for a lisse Weil sheaf `G`, assuming that
the extension by zero along open immersions commutes with internal homs out of lisse sheaves
(`hU2`). The dual of `G` commutes with the pullback along `f`
(`AlgebraicGeometry.ProEtaleWeilSheaf.nonempty_upperStar_obj_dual_iso`). -/
theorem nonempty_iso_derivedLowerShriek_tensorLisse_of_extensionByZero {X Y : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of k₀))] [Y.Over (Spec (CommRingCat.of k₀))] (f : X ⟶ Y)
    [f.IsOver (Spec (CommRingCat.of k₀))] [IsSeparated f] [LocallyOfFiniteType f]
    [QuasiCompact f] [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))]
    [QuasiSeparated (Y ↘ Spec (CommRingCat.of k₀))] (G : WeilSheaf k₀ l Y) (hG : G.IsLisse)
    (hU2 : ∀ {Z : Scheme.{u}} [Z.Over (Spec (CommRingCat.of k₀))] (j : X ⟶ Z) [IsOpenImmersion j]
      [j.IsOver (Spec (CommRingCat.of k₀))] (M : ProEtaleWeilSheaf k₀ l Z),
      ProEtale.IsAdicLisseSheaf M.carrier →
        Nonempty (extensionByZero k₀ l j ⋙ ihomFunctor k₀ l Z M ≅
          ihomFunctor k₀ l X ((ProEtaleWeilSheaf.upperStar k₀ l j).obj M) ⋙
            extensionByZero k₀ l j)) :
    Nonempty (derivedLowerShriek k₀ l f ⋙ tensorLisse G hG ≅
      tensorLisse ((WeilSheaf.upperStar f).obj G) (ProEtale.IsAdicLisseSheaf.upperStar _ hG) ⋙
        derivedLowerShriek k₀ l f) := by
  have : QuasiCompact (X ↘ Spec (CommRingCat.of k₀)) := by
    rw [← comp_over f (Spec (CommRingCat.of k₀))]
    infer_instance
  exact nonempty_iso_derivedLowerShriek_tensorLisse_of_nonempty f G hG hU2
    (nonempty_upperStar_obj_dual_iso f G hG)

end AlgebraicGeometry.WeilComplex
