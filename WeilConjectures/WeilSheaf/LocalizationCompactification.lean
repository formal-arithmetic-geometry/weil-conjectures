/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Adic.BaseChange
public import WeilConjectures.WeilSheaf.DirectImageRestriction
public import WeilConjectures.WeilSheaf.LocalizationOpenClosed
public import WeilConjectures.WeilSheaf.LowerStarComp
public import WeilConjectures.WeilSheaf.OpenImmersionRestriction
public import WeilConjectures.WeilSheaf.ProperCohomology.OpenImmersion
public import WeilConjectures.WeilSheaf.UpperStarComp

/-!
# Restricting `Rḡ_* ī_!` to the open part of a compactification

Let `j : U ⟶ X` be an open immersion of `k₀`-schemes, and let `U ⟶[a] W ⟶[g] X` be a
compactification of `j`: an open immersion `a` followed by a proper morphism `g`, with `W`
Noetherian. For `M` in the derived category of pro-étale Weil sheaves on `U`, the restriction
of `Rg_* (a_! M)` to `U` is `M` again
(`AlgebraicGeometry.ProEtaleWeilSheaf.nonempty_upperStar_rightDerivedLowerStar_extensionByZero_iso`).
This is the part of the identification of the direct image with compact support `Rj_!` with the
extension by zero which only uses open base change.

## Proof

Let `V = g⁻¹(U)`, with the open immersion `v : V ⟶ W` and `q : V ⟶ U`. Since `g` is separated,
the section `s : U ⟶ V` of `q` induced by `a` is a closed immersion; it is also an open
immersion. Let `θ : a_! M ⟶ Ra_* M` be the transpose of `a^* a_! M ≅ M`. Its cone `E` vanishes on
`V`: on `s(U)` because `a^* θ` is invertible, and on the complement `O` of `s(U)` because both
`a_! M` and `Ra_* M` vanish there, the latter by open base change, `O` missing `a(U)`. By open
base change (`AlgebraicGeometry.ProEtaleWeilSheaf.isZero_upperStar_rightDerivedLowerStar_of_isPullback`),
`j^* Rg_* E = 0`, so `j^* Rg_* θ` is invertible, and `j^* Rg_* Ra_* M ≅ j^* Rj_* M ≅ M`.

Open base change is reduced, through the forgetful functor, which reflects zero objects, to open
base change for `ℓ`-adic sheaves on the geometric fibers
(`AlgebraicGeometry.ProEtale.adicDerivedBaseChangeIso`).
-/

@[expose] public section

universe u

open CategoryTheory Limits Pretriangulated Endofunctor

namespace AlgebraicGeometry

open ProEtale

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime]

section Forget

/-- A complex of pro-étale Weil sheaves is zero if its underlying complex of `ℓ`-adic sheaves
is. -/
lemma ProEtaleWeilSheaf.isZero_of_isZero_forget {X : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of k₀))] (K : DerivedCategory (ProEtaleWeilSheaf k₀ l X))
    (h : IsZero ((IsoAlgebra.forget _).mapDerivedCategory.obj K)) : IsZero K :=
  (DerivedCategory.isZero_iff _).2 fun n ↦ (ProEtaleWeilSheaf.isZero_iff _).2
    (((DerivedCategory.isZero_iff _).1 h n).of_iso
      (((IsoAlgebra.forget _).mapDerivedCategoryHomologyFunctorIso n).app K))

/-- Over an empty scheme, every complex of pro-étale Weil sheaves is zero. -/
lemma ProEtaleWeilSheaf.isZero_of_isEmpty {P : Scheme.{u}} [P.Over (Spec (CommRingCat.of k₀))]
    [IsEmpty P] (K : DerivedCategory (ProEtaleWeilSheaf k₀ l P)) : IsZero K := by
  have : IsEmpty (P ↘ Spec (CommRingCat.of k₀)).geometricFiber :=
    ⟨fun x ↦ isEmptyElim ((P ↘ Spec (CommRingCat.of k₀)).geometricFiberProj.base x)⟩
  exact ProEtaleWeilSheaf.isZero_of_isZero_forget _ (ProEtale.isZero_of_isEmpty l _)

variable {X Y : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  [Y.Over (Spec (CommRingCat.of k₀))] (φ : X ⟶ Y) [φ.IsOver (Spec (CommRingCat.of k₀))]

variable (k₀ l) in
/-- Forgetting the Weil structure commutes with the pullback `φ^*` on the derived categories of
pro-étale Weil sheaves: `For ∘ D(φ^*) ≅ D(φ̄^*) ∘ For`. -/
noncomputable def ProEtaleWeilSheaf.mapDerivedCategoryUpperStarCompForgetIso :
    (ProEtaleWeilSheaf.upperStar k₀ l φ).mapDerivedCategory ⋙
        (IsoAlgebra.forget _).mapDerivedCategory ≅
      (IsoAlgebra.forget _).mapDerivedCategory ⋙
        ((Scheme.Hom.geometricFiberMap φ (comp_over φ _))^*ᵃ[l]).mapDerivedCategory :=
  (Functor.mapDerivedCategoryCompIso (ProEtaleWeilSheaf.upperStar k₀ l φ)
      (IsoAlgebra.forget _)).symm ≪≫
    Functor.mapDerivedCategoryNatIso
      (Iso.refl (ProEtaleWeilSheaf.upperStar k₀ l φ ⋙ IsoAlgebra.forget _) :
        ProEtaleWeilSheaf.upperStar k₀ l φ ⋙ IsoAlgebra.forget _ ≅
          IsoAlgebra.forget _ ⋙ (Scheme.Hom.geometricFiberMap φ (comp_over φ _))^*ᵃ[l]) ≪≫
    Functor.mapDerivedCategoryCompIso (IsoAlgebra.forget _)
      ((Scheme.Hom.geometricFiberMap φ (comp_over φ _))^*ᵃ[l])

end Forget

section BaseChange

variable {V U W X : Scheme.{u}} [V.Over (Spec (CommRingCat.of k₀))]
  [U.Over (Spec (CommRingCat.of k₀))] [W.Over (Spec (CommRingCat.of k₀))]
  [X.Over (Spec (CommRingCat.of k₀))]

/-- **Open base change, vanishing form.** For a cartesian square
```
V --v--> W
|q       |g
v        v
U --j--> X
```
of `k₀`-schemes with `j` an open immersion, and `E` a complex of pro-étale Weil sheaves on `W`
with `v^* E = 0`, also `j^* Rg_* E = 0`: forgetting the Weil structures, this is the open base
change isomorphism `j̄^* Rḡ_* ≅ Rq̄_* v̄^*` for `ℓ`-adic sheaves
(`AlgebraicGeometry.ProEtale.adicDerivedBaseChangeIso`). -/
theorem ProEtaleWeilSheaf.isZero_upperStar_rightDerivedLowerStar_of_isPullback {q : V ⟶ U}
    {v : V ⟶ W} {j : U ⟶ X} {g : W ⟶ X} [q.IsOver (Spec (CommRingCat.of k₀))]
    [v.IsOver (Spec (CommRingCat.of k₀))] [j.IsOver (Spec (CommRingCat.of k₀))]
    [g.IsOver (Spec (CommRingCat.of k₀))] [IsOpenImmersion j] [IsOpenImmersion v]
    (h : IsPullback q v j g) (E : DerivedCategory (ProEtaleWeilSheaf k₀ l W))
    (hE : IsZero ((ProEtaleWeilSheaf.upperStar k₀ l v).mapDerivedCategory.obj E)) :
    IsZero ((ProEtaleWeilSheaf.upperStar k₀ l j).mapDerivedCategory.obj
      ((ProEtaleWeilSheaf.lowerStar k₀ l g).rightDerivedFunctor.obj E)) := by
  have := IsGrothendieckAbelian.hasColimitsOfShape_discrete.{u + 2, u + 1, u + 1}
    (ProEtale.AdicSheaf l (W ↘ Spec (CommRingCat.of k₀)).geometricFiber) ℤ
  have := IsGrothendieckAbelian.hasExactColimitsOfShape_discrete.{u + 2, u + 1, u + 1}
    (ProEtale.AdicSheaf l (W ↘ Spec (CommRingCat.of k₀)).geometricFiber) ℤ
  have hsq := Scheme.Hom.isPullback_geometricFiberMap_of_isPullback h
    (comp_over q (Spec (CommRingCat.of k₀))) (comp_over v (Spec (CommRingCat.of k₀)))
    (comp_over j (Spec (CommRingCat.of k₀))) (comp_over g (Spec (CommRingCat.of k₀)))
  refine ProEtaleWeilSheaf.isZero_of_isZero_forget (k₀ := k₀) (l := l) (X := U) _ ?_
  have h₁ : IsZero (((Scheme.Hom.geometricFiberMap v (comp_over v _))^*ᵃ[l]).mapDerivedCategory.obj
      ((IsoAlgebra.forget _).mapDerivedCategory.obj E)) :=
    ((IsoAlgebra.forget _).mapDerivedCategory.map_isZero hE).of_iso
      ((ProEtaleWeilSheaf.mapDerivedCategoryUpperStarCompForgetIso k₀ l v).app E).symm
  have h₂ := ((Scheme.Hom.geometricFiberMap q (comp_over q _))_*ᵃ[l]).rightDerivedFunctor.map_isZero
    h₁
  have h₃ : IsZero (((Scheme.Hom.geometricFiberMap j (comp_over j _))^*ᵃ[l]).mapDerivedCategory.obj
      (((Scheme.Hom.geometricFiberMap g (comp_over g _))_*ᵃ[l]).rightDerivedFunctor.obj
        ((IsoAlgebra.forget _).mapDerivedCategory.obj E))) :=
    h₂.of_iso ((adicDerivedBaseChangeIso l hsq).app _)
  have h₄ := h₃.of_iso
    (((Scheme.Hom.geometricFiberMap j (comp_over j _))^*ᵃ[l]).mapDerivedCategory.mapIso
      ((IsoAlgebra.rightDerivedFunctorMapOfNatIsoCompForgetIso
        (e := adicLowerStarGeometricFiberMapCompFrobeniusIso l g (comp_over g _))).app E))
  exact h₄.of_iso ((ProEtaleWeilSheaf.mapDerivedCategoryUpperStarCompForgetIso k₀ l j).app _)

end BaseChange

section Compactification

variable {U W X : Scheme.{u}} [U.Over (Spec (CommRingCat.of k₀))]
  [W.Over (Spec (CommRingCat.of k₀))] [X.Over (Spec (CommRingCat.of k₀))]

local notation "𝐒" => Spec (CommRingCat.of k₀)

/-- **The restriction of `Rg_* a_!` to the open part.** Let `U ⟶[a] W ⟶[g] X` be a factorization
of an open immersion `j` into an open immersion `a` followed by a proper morphism `g`, with `W`
Noetherian. For every complex `M` of pro-étale Weil sheaves on `U`, `j^* Rg_* (a_! M) ≅ M`. -/
theorem ProEtaleWeilSheaf.nonempty_upperStar_rightDerivedLowerStar_extensionByZero_iso
    (j : U ⟶ X) (a : U ⟶ W) (g : W ⟶ X) [IsOpenImmersion j] [IsOpenImmersion a] [IsProper g]
    [j.IsOver (Spec (CommRingCat.of k₀))] [a.IsOver (Spec (CommRingCat.of k₀))]
    [g.IsOver (Spec (CommRingCat.of k₀))] (hag : a ≫ g = j) [IsNoetherian W]
    (M : DerivedCategory (ProEtaleWeilSheaf k₀ l U)) :
    Nonempty ((ProEtaleWeilSheaf.upperStar k₀ l j).mapDerivedCategory.obj
      ((ProEtaleWeilSheaf.lowerStar k₀ l g).rightDerivedFunctor.obj
        ((ProEtaleWeilSheaf.extensionByZero k₀ l a).mapDerivedCategory.obj M)) ≅ M) := by
  -- the open subscheme `V = g⁻¹(U)` of `W`
  let V := pullback g j
  let v : V ⟶ W := pullback.fst g j
  let q : V ⟶ U := pullback.snd g j
  have hpb : IsPullback q v j g := (IsPullback.of_hasPullback g j).flip
  let _ : V.Over 𝐒 := ⟨v ≫ W ↘ 𝐒⟩
  have : v.IsOver 𝐒 := ⟨rfl⟩
  have : q.IsOver 𝐒 := ⟨by
    change q ≫ U ↘ 𝐒 = v ≫ W ↘ 𝐒
    rw [← comp_over j 𝐒, ← comp_over g 𝐒, ← Category.assoc, ← Category.assoc, hpb.w]⟩
  -- the section `s : U ⟶ V` of `q` induced by `a`, an open and closed immersion
  let s : U ⟶ V := pullback.lift a (𝟙 U) (by rw [hag, Category.id_comp])
  have hsv : s ≫ v = a := pullback.lift_fst _ _ _
  have hsq : s ≫ q = 𝟙 U := pullback.lift_snd _ _ _
  have : IsOpenImmersion (s ≫ v) := by rw [hsv]; infer_instance
  have : IsOpenImmersion s := IsOpenImmersion.of_comp s v
  have : IsClosedImmersion (s ≫ q) := by rw [hsq]; infer_instance
  have : IsClosedImmersion s := IsClosedImmersion.of_comp s q
  have : s.IsOver 𝐒 := ⟨by
    change s ≫ v ≫ W ↘ 𝐒 = U ↘ 𝐒
    rw [← Category.assoc, hsv, comp_over]⟩
  -- the open complement `O` of `s(U)` in `V`
  let O : V.Opens := ⟨(Set.range s.base)ᶜ, s.isClosedEmbedding.isClosed_range.isOpen_compl⟩
  let t : O.toScheme ⟶ V := O.ι
  let _ : O.toScheme.Over 𝐒 := ⟨t ≫ V ↘ 𝐒⟩
  have : t.IsOver 𝐒 := ⟨rfl⟩
  have hst : IsCompl (Set.range s.base) (Set.range t.base) := by
    rw [show Set.range t.base = (O : Set V) from Scheme.Opens.range_ι O]
    exact isCompl_compl
  have : TopologicalSpace.NoetherianSpace O.toScheme :=
    (t ≫ v).isOpenEmbedding.isInducing.noetherianSpace
  let w : O.toScheme ⟶ W := t ≫ v
  have hdisj : Disjoint (Set.range a.base) (Set.range w.base) := by
    rw [Set.disjoint_left]
    rintro _ ⟨x, rfl⟩ ⟨y, hy⟩
    have h₁ : (t.base y : V) = s.base x := by
      apply v.isOpenEmbedding.injective
      rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hsv]
      exact hy
    exact (show t.base y ∈ (O : Set V) from (Scheme.Opens.range_ι O).subset ⟨y, rfl⟩)
      ⟨x, h₁.symm⟩
  -- the transpose `θ : a_! M ⟶ Ra_* M` of `a^* a_! M ≅ M`
  let adjA := ProEtaleWeilSheaf.derivedUpperStarLowerStarAdjunction k₀ l a
  let σ : ProEtaleWeilSheaf.extensionByZero k₀ l a ⋙ ProEtaleWeilSheaf.upperStar k₀ l a ≅ 𝟭 _ :=
    asIso (Functor.whiskerRight (ProEtaleWeilSheaf.extensionByZeroToLowerStar k₀ l a)
      (ProEtaleWeilSheaf.upperStar k₀ l a)) ≪≫
      asIso (ProEtaleWeilSheaf.upperStarLowerStarAdjunction k₀ l a).counit
  let φ : (ProEtaleWeilSheaf.upperStar k₀ l a).mapDerivedCategory.obj
      ((ProEtaleWeilSheaf.extensionByZero k₀ l a).mapDerivedCategory.obj M) ≅ M :=
    ((ProEtaleWeilSheaf.extensionByZero k₀ l a).mapDerivedCategoryCompIso
        (ProEtaleWeilSheaf.upperStar k₀ l a)).symm.app M ≪≫
      (Functor.mapDerivedCategoryNatIso σ).app M ≪≫ (Functor.mapDerivedCategoryIdIso _).app M
  let θ := adjA.homEquiv _ _ φ.hom
  have hθ : IsIso ((ProEtaleWeilSheaf.upperStar k₀ l a).mapDerivedCategory.map θ) := by
    have hfac : (ProEtaleWeilSheaf.upperStar k₀ l a).mapDerivedCategory.map θ ≫
        adjA.counit.app M = φ.hom := by
      have := adjA.homEquiv_counit (g := θ)
      simp only [θ, Equiv.symm_apply_apply] at this
      exact this.symm
    have : IsIso adjA.counit := Adjunction.isIso_mapDerivedCategoryRightDerivedAdjunction_counit _
    exact IsIso.of_isIso_fac_right hfac
  obtain ⟨E, e₁, e₂, hT⟩ := distinguished_cocone_triangle θ
  -- `a^* E = 0`
  have haE : IsZero ((ProEtaleWeilSheaf.upperStar k₀ l a).mapDerivedCategory.obj E) :=
    (Triangle.isZero₃_iff_isIso₁ _
      ((ProEtaleWeilSheaf.upperStar k₀ l a).mapDerivedCategory.map_distinguished _ hT)).2 hθ
  -- `w^* E = 0`, as `w^* a_! M = 0` and `w^* Ra_* M = 0`
  have hwE : IsZero ((ProEtaleWeilSheaf.upperStar k₀ l w).mapDerivedCategory.obj E) := by
    have h₁ : IsZero ((ProEtaleWeilSheaf.upperStar k₀ l w).mapDerivedCategory.obj
        ((ProEtaleWeilSheaf.extensionByZero k₀ l a).mapDerivedCategory.obj M)) := by
      have h0 (F : ProEtaleWeilSheaf k₀ l U) : IsZero ((ProEtaleWeilSheaf.extensionByZero k₀ l a ⋙
          ProEtaleWeilSheaf.upperStar k₀ l w).obj F) :=
        ProEtaleWeilSheaf.isZero_upperStar_obj_extensionByZero_obj a w hdisj F
      exact (Functor.isZero_mapDerivedCategory_obj _ M fun _ ↦ h0 _).of_iso
        (((ProEtaleWeilSheaf.extensionByZero k₀ l a).mapDerivedCategoryCompIso
          (ProEtaleWeilSheaf.upperStar k₀ l w)).symm.app M)
    have h₂ : IsZero ((ProEtaleWeilSheaf.upperStar k₀ l w).mapDerivedCategory.obj
        ((ProEtaleWeilSheaf.lowerStar k₀ l a).rightDerivedFunctor.obj M)) := by
      let P := pullback a w
      have hP : IsPullback (pullback.snd a w) (pullback.fst a w) w a :=
        (IsPullback.of_hasPullback a w).flip
      let _ : P.Over 𝐒 := ⟨pullback.fst a w ≫ U ↘ 𝐒⟩
      have : (pullback.fst a w).IsOver 𝐒 := ⟨rfl⟩
      have : (pullback.snd a w).IsOver 𝐒 := ⟨by
        change pullback.snd a w ≫ O.toScheme ↘ 𝐒 = pullback.fst a w ≫ U ↘ 𝐒
        rw [← comp_over a 𝐒, ← Category.assoc, pullback.condition]
        simp only [Category.assoc]
        rfl⟩
      have : IsEmpty P := ⟨fun x ↦ Set.disjoint_left.1 hdisj ⟨(pullback.fst a w).base x, rfl⟩
        ⟨(pullback.snd a w).base x, by
          rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, pullback.condition]⟩⟩
      exact ProEtaleWeilSheaf.isZero_upperStar_rightDerivedLowerStar_of_isPullback hP M
        (ProEtaleWeilSheaf.isZero_of_isEmpty _)
    exact Triangle.isZero₃_of_isZero₁₂ _
      ((ProEtaleWeilSheaf.upperStar k₀ l w).mapDerivedCategory.map_distinguished _ hT) h₁ h₂
  -- `v^* E = 0`, as `s^* v^* E = a^* E = 0` and `t^* v^* E = w^* E = 0`
  have hvE : IsZero ((ProEtaleWeilSheaf.upperStar k₀ l v).mapDerivedCategory.obj E) := by
    have hcomp {T : Scheme.{u}} [T.Over 𝐒] (r : T ⟶ V) [r.IsOver 𝐒] (b : T ⟶ W) [b.IsOver 𝐒]
        (hb : r ≫ v = b) :
        (ProEtaleWeilSheaf.upperStar k₀ l b).mapDerivedCategory ≅
          (ProEtaleWeilSheaf.upperStar k₀ l v).mapDerivedCategory ⋙
            (ProEtaleWeilSheaf.upperStar k₀ l r).mapDerivedCategory := by
      subst hb
      exact Functor.mapDerivedCategoryNatIso (ProEtaleWeilSheaf.upperStarCompIso k₀ l r v) ≪≫
        Functor.mapDerivedCategoryCompIso _ _
    refine DerivedCategory.isZero_of_isZero_mapDerivedCategory_obj
      (ProEtaleWeilSheaf.isZero_of_isZero_upperStar_of_isCompl s t hst) ?_ ?_
    · exact haE.of_iso ((hcomp s a hsv).app E).symm
    · exact hwE.of_iso ((hcomp t w rfl).app E).symm
  -- `j^* Rg_* E = 0`, hence `j^* Rg_* θ` is invertible
  have hjE := ProEtaleWeilSheaf.isZero_upperStar_rightDerivedLowerStar_of_isPullback hpb E hvE
  have hiso : IsIso ((ProEtaleWeilSheaf.upperStar k₀ l j).mapDerivedCategory.map
      ((ProEtaleWeilSheaf.lowerStar k₀ l g).rightDerivedFunctor.map θ)) :=
    (Triangle.isZero₃_iff_isIso₁ _
      ((ProEtaleWeilSheaf.upperStar k₀ l j).mapDerivedCategory.map_distinguished _
        ((ProEtaleWeilSheaf.lowerStar k₀ l g).rightDerivedFunctor.map_distinguished _ hT))).1 hjE
  -- `Rg_* Ra_* ≅ Rj_*`
  have := (ProEtaleWeilSheaf.upperStarLowerStarAdjunction k₀ l a).preservesKInjectiveComplexes
  let eComp : (ProEtaleWeilSheaf.lowerStar k₀ l g).rightDerivedFunctor.obj
      ((ProEtaleWeilSheaf.lowerStar k₀ l a).rightDerivedFunctor.obj M) ≅
        (ProEtaleWeilSheaf.lowerStar k₀ l j).rightDerivedFunctor.obj M :=
    (Functor.rightDerivedFunctorCompIso' _ _ (ProEtaleWeilSheaf.lowerStarCompIso k₀ l a g)).app M ≪≫
      (Functor.rightDerivedFunctorNatIso (ProEtaleWeilSheaf.lowerStarCongr (k₀ := k₀) (l := l) hag)).app M
  have : IsIso (ProEtaleWeilSheaf.derivedUpperStarLowerStarAdjunction k₀ l j).counit :=
    Adjunction.isIso_mapDerivedCategoryRightDerivedAdjunction_counit _
  exact ⟨asIso ((ProEtaleWeilSheaf.upperStar k₀ l j).mapDerivedCategory.map
      ((ProEtaleWeilSheaf.lowerStar k₀ l g).rightDerivedFunctor.map θ)) ≪≫
    (ProEtaleWeilSheaf.upperStar k₀ l j).mapDerivedCategory.mapIso eComp ≪≫
    asIso ((ProEtaleWeilSheaf.derivedUpperStarLowerStarAdjunction k₀ l j).counit.app M)⟩

end Compactification

end AlgebraicGeometry
