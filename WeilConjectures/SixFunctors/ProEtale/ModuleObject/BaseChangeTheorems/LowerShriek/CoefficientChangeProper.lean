/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.CoefficientChangeRefinement
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.PushforwardDataProper

/-!
# Coefficient changes and `Rf_! ≅ Rf_*` for a proper `f`

Let `C` be a coefficient change `Λ ⟶ Λ'` of the bounded constructible six functors
(`ProEtale.CondensedRing.BoundedConstructibleCoefficientChange`), along functors
`T_X : Dᵇc(X)⟦Λ⟧ ⥤ Dᵇc(X)⟦Λ'⟧`. This file proves that the identification `Rf_! ≅ Rf_*` of a
proper `f` (`BoundedConstructiblePushforwardData.lowerShriekIsoLowerStar`) is compatible with the
coefficient comparisons (Shriek) and (Push) of `C`
(`BoundedConstructibleCoefficientChange.squareCompatible_lowerShriekIsoLowerStar`).

It is assembled from the independence of the compactification
(`BoundedConstructibleCoefficientChange.squareCompatible_lowerShriekOfCompactificationIso`) and
the compatibility of (Shriek) with the identification `(𝟙 X)_! ≅ 𝟭` of the trivial
compactification of `f`
(`BoundedConstructibleCoefficientChange.squareCompatible_openImmersionLowerShriekOfIsProperIso`),
which in turn follows from the compatibility of (Pull) with `L(𝟙 X)^* ≅ 𝟭`
(`BoundedConstructibleCoefficientChange.squareCompatible_upperStarId`), a consequence of the
compatibility of (Pull) with composition and of the unit laws.
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Obj

namespace CategoryTheory.NatTrans.SquareCompatible

variable {A A' : Type*} [Category* A] [Category* A'] {J U : A ⥤ A} {J' U' : A' ⥤ A'}
  {T : A ⥤ A'}

/-- Let `a : J ⊣ U` and `a' : J' ⊣ U'` be adjunctions of endofunctors with commutation squares
`σ : J ⋙ T ≅ T ⋙ J'` and its mate `π : U ⋙ T ≅ T ⋙ U'`, and suppose that the counits factor as
`ε = ι ≫ d` and `ε' = ι' ≫ d'` through isomorphisms `ι : J ≅ 𝟭`, `d : U ≅ 𝟭` and their primed
versions. If `d` and `d'` are compatible with `π`, then `ι` and `ι'` are compatible with `σ`. -/
lemma of_counit_eq (a : J ⊣ U) (a' : J' ⊣ U') {σ : J ⋙ T ≅ T ⋙ J'} {π : U ⋙ T ≅ T ⋙ U'}
    (hm : a.IsMateSquare a' σ π) (ι : J ≅ 𝟭 A) (ι' : J' ≅ 𝟭 A') (d : U ≅ 𝟭 A) (d' : U' ≅ 𝟭 A')
    (hε : ∀ W, a.counit.app W = ι.hom.app (U.obj W) ≫ d.hom.app W)
    (hε' : ∀ W, a'.counit.app W = ι'.hom.app (U'.obj W) ≫ d'.hom.app W)
    (hd : SquareCompatible π (Functor.idSquareIso T) d.hom d'.hom) :
    SquareCompatible σ (Functor.idSquareIso T) ι.hom ι'.hom := by
  have key (W : A) : T.map (ι.hom.app (U.obj W)) =
      σ.hom.app (U.obj W) ≫ ι'.hom.app (T.obj (U.obj W)) := by
    have h₁ := counit hm W
    have h₂ := hd W
    have h₃ := ι'.hom.naturality (π.hom.app W)
    simp only [Functor.comp_obj, Functor.pasteSquareIso_hom_app, Functor.idSquareIso_hom_app,
      Category.comp_id, Functor.id_obj, Functor.id_map] at h₁ h₂ h₃
    rw [hε, hε', Functor.map_comp, Category.assoc, reassoc_of% h₃, ← h₂] at h₁
    simpa using (cancel_mono (T.map (d.hom.app W))).1 (h₁.trans (Category.assoc _ _ _).symm)
  intro M
  simp only [Functor.id_obj, Functor.idSquareIso_hom_app]
  have n₁ := ι.hom.naturality (d.hom.app M)
  have n₂ := σ.hom.naturality (d.hom.app M)
  have n₃ := ι'.hom.naturality (T.map (d.hom.app M))
  simp only [Functor.comp_obj, Functor.comp_map, Functor.id_obj, Functor.id_map] at n₁ n₂ n₃
  erw [Category.comp_id]
  rw [← cancel_epi (T.map (J.map (d.hom.app M))), ← Functor.map_comp, n₁, Functor.map_comp, key,
    Category.assoc, reassoc_of% n₂, n₃]

end CategoryTheory.NatTrans.SquareCompatible

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

namespace BoundedConstructibleCoefficientChange

variable {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}} {ℓ : ℕ} [Fact ℓ.Prime]
  [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ'] {k : Type u} [Field k]
  [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
  {P : BoundedConstructiblePushforwardData Λ ℓ k} {P' : BoundedConstructiblePushforwardData Λ' ℓ k}
  {T : ∀ (X : Over (Spec (.of k))) [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [IsSeparated X.hom], Dᵇc(X.left)⟦Λ⟧ ⥤ Dᵇc(X.left)⟦Λ'⟧}
  {pull : ∀ {X Y : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [IsSeparated X.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    (f : X ⟶ Y),
    boundedConstructibleUpperStar Λ ℓ f ⋙ T X ≅ T Y ⋙ boundedConstructibleUpperStar Λ' ℓ f}
  (C : BoundedConstructibleCoefficientChange Λ Λ' ℓ P P' T pull)

variable {X Y : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
  [IsSeparated X.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]

include C in
/-- (Pull) is compatible with the identifications `L(𝟙 X)^* ≅ 𝟭`: this follows from the
compatibility of (Pull) with the composition isomorphism `L(𝟙 ≫ 𝟙)^* ≅ L𝟙^* ⋙ L𝟙^*` and the unit
laws of the composition isomorphisms. -/
lemma squareCompatible_upperStarId (X : Over (Spec (.of k))) [LocallyOfFiniteType X.hom]
    [QuasiCompact X.hom] [IsSeparated X.hom] :
    NatTrans.SquareCompatible (pull (𝟙 X)) (Functor.idSquareIso (T X))
      (boundedConstructibleUpperStarId Λ ℓ X).hom
      (boundedConstructibleUpperStarId Λ' ℓ X).hom := by
  intro K
  simp only [Functor.id_obj, Functor.idSquareIso_hom_app]
  let U := boundedConstructibleUpperStar Λ ℓ (𝟙 X)
  let U' := boundedConstructibleUpperStar Λ' ℓ (𝟙 X)
  let u := (pull (𝟙 X)).hom
  let i := (boundedConstructibleUpperStarId Λ ℓ X).hom
  let i' := (boundedConstructibleUpperStarId Λ' ℓ X).hom
  -- the composition isomorphism `U ⋙ U ≅ L(𝟙 ≫ 𝟙)^*` read back on `U`
  have e₁ : boundedConstructibleUpperStar Λ ℓ (𝟙 X ≫ 𝟙 X) = U := by rw [Category.id_comp]
  have e₁' : boundedConstructibleUpperStar Λ' ℓ (𝟙 X ≫ 𝟙 X) = U' := by rw [Category.id_comp]
  -- `c ≫ U.map (i K) = id` and `c ≫ i (U K) = id`, with `c = comp.hom` cast to `U`
  let c : U.obj K ⟶ U.obj (U.obj K) :=
    eqToHom (by rw [e₁]) ≫ (boundedConstructibleUpperStarComp Λ ℓ (𝟙 X) (𝟙 X)).hom.app K
  let c' : U'.obj ((T X).obj K) ⟶ U'.obj (U'.obj ((T X).obj K)) :=
    eqToHom (by rw [e₁']) ≫
      (boundedConstructibleUpperStarComp Λ' ℓ (𝟙 X) (𝟙 X)).hom.app ((T X).obj K)
  have hR : c ≫ U.map (i.app K) = 𝟙 _ := by
    simp only [c, eqToHom_refl, Category.id_comp]
    exact (boundedConstructibleUpperStarComp_id_right_app Λ ℓ (𝟙 X) K).trans (eqToHom_refl _ _)
  have hR' : c' ≫ U'.map (i'.app ((T X).obj K)) = 𝟙 _ := by
    simp only [c', eqToHom_refl, Category.id_comp]
    exact (boundedConstructibleUpperStarComp_id_right_app Λ' ℓ (𝟙 X) ((T X).obj K)).trans
      (eqToHom_refl _ _)
  have hP : (T X).map c ≫ u.app (U.obj K) ≫ U'.map (u.app K) = u.app K ≫ c' := by
    have h := C.pull_comp (𝟙 X) (𝟙 X) K
    simp only [Functor.pasteSquareIso_hom_app] at h
    simp only [c, c', eqToHom_refl, Category.id_comp]
    exact h
  -- naturality of `u` at `i K`
  have hn : (T X).map (U.map (i.app K)) ≫ u.app K =
      u.app (U.obj K) ≫ U'.map ((T X).map (i.app K)) := u.naturality (i.app K)
  have hL : (T X).map c ≫ u.app (U.obj K) ≫ U'.map ((T X).map (i.app K)) = u.app K := by
    rw [← hn, ← Functor.map_comp_assoc, hR, CategoryTheory.Functor.map_id, Category.id_comp]
  have hRt : (T X).map c ≫ u.app (U.obj K) ≫ U'.map (u.app K ≫ i'.app ((T X).obj K)) =
      u.app K := by
    rw [U'.map_comp, reassoc_of% hP, hR', Category.comp_id]
  have key : U'.map ((T X).map (i.app K)) = U'.map (u.app K ≫ i'.app ((T X).obj K)) := by
    rw [← cancel_epi (u.app (U.obj K)), ← cancel_epi ((T X).map c), hL, hRt]
  have n₁ : U'.map ((T X).map (i.app K)) ≫ i'.app ((T X).obj K) =
      i'.app ((T X).obj (U.obj K)) ≫ (T X).map (i.app K) := i'.naturality _
  have n₂ : U'.map (u.app K ≫ i'.app ((T X).obj K)) ≫ i'.app ((T X).obj K) =
      i'.app ((T X).obj (U.obj K)) ≫ (u.app K ≫ i'.app ((T X).obj K)) := i'.naturality _
  have h := (cancel_epi (i'.app ((T X).obj (U.obj K)))).1
    (n₁.symm.trans ((congrArg (· ≫ i'.app ((T X).obj K)) key).trans n₂))
  simpa using h

section LeftFamily

/-! ### Coefficient changes along functors of the underlying schemes -/

variable {T₀ : ∀ X : Scheme.{u}, Dᵇc(X)⟦Λ⟧ ⥤ Dᵇc(X)⟦Λ'⟧}
  {pull₀ : ∀ {X Y : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [IsSeparated X.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    (f : X ⟶ Y),
    boundedConstructibleUpperStar Λ ℓ f ⋙ T₀ X.left ≅
      T₀ Y.left ⋙ boundedConstructibleUpperStar Λ' ℓ f}
  (C₀ : BoundedConstructibleCoefficientChange Λ Λ' ℓ P P' (fun X _ _ _ ↦ T₀ X.left) pull₀)

/-- (Shriek) for the open immersion of the trivial compactification `X ⟶[𝟙] X ⟶[f] Y` of a proper
`f` is compatible with the identifications `(𝟙 X)_! ≅ 𝟭`: the identification is read off the
counit of `(𝟙 X)_! ⊣ L(𝟙 X)^*`, which is compatible with the coefficient comparisons since (Pull)
is the mate of (Shriek), and (Pull) is compatible with `L(𝟙 X)^* ≅ 𝟭`. -/
lemma squareCompatible_openImmersionLowerShriekOfIsProperIso (f : X ⟶ Y) [IsProper f.left]
    (hpull : pull₀ (Compactification.ofIsProper f.left).overI = pull₀ (𝟙 X)) :
    NatTrans.SquareCompatible (C₀.shriek (Compactification.ofIsProper f.left).overI)
      (Functor.idSquareIso (T₀ X.left))
      (boundedConstructibleOpenImmersionLowerShriekOfIsProperIso Λ ℓ f).hom
      (boundedConstructibleOpenImmersionLowerShriekOfIsProperIso Λ' ℓ f).hom := by
  let i := (Compactification.ofIsProper f.left).overI
  let ι := boundedConstructibleOpenImmersionLowerShriekOfIsProperIso Λ ℓ f
  let ι' := boundedConstructibleOpenImmersionLowerShriekOfIsProperIso Λ' ℓ f
  let a := boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction Λ ℓ i
  let a' := boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction Λ' ℓ i
  let d := (boundedConstructibleUpperStarId Λ ℓ X).hom
  let d' := (boundedConstructibleUpperStarId Λ' ℓ X).hom
  refine NatTrans.SquareCompatible.of_counit_eq a a' (C₀.isMateSquare_shriek_pull i) ι ι'
    (boundedConstructibleUpperStarId Λ ℓ X) (boundedConstructibleUpperStarId Λ' ℓ X)
    (fun W ↦ ?_) (fun W ↦ ?_) ?_
  · rw [← cancel_epi (ι.inv.app _), Iso.inv_hom_id_app_assoc]
    exact boundedConstructibleOpenImmersionLowerShriekOfIsProperIso_inv_app_comp_adjunction_counit
      Λ ℓ f W
  · rw [← cancel_epi (ι'.inv.app _), Iso.inv_hom_id_app_assoc]
    exact boundedConstructibleOpenImmersionLowerShriekOfIsProperIso_inv_app_comp_adjunction_counit
      Λ' ℓ f W
  · rw [hpull]
    exact C₀.squareCompatible_upperStarId X

/-- **`Rf_! ≅ Rf_*` is compatible with the coefficient comparisons** for a proper `f`: under
(Shriek) along the chosen compactification of `f` and (Push) along `f`, the identification
`Rf_! ≅ Rf_*` (`BoundedConstructiblePushforwardData.lowerShriekIsoLowerStar`) over `Λ`
corresponds to the one over `Λ'`. -/
lemma squareCompatible_lowerShriekIsoLowerStar (hP : P.IsIsoRefinementPushforward)
    (hP' : P'.IsIsoRefinementPushforward) (f : X ⟶ Y) [IsProper f.left]
    (hpull : pull₀ (Compactification.ofIsProper f.left).overI = pull₀ (𝟙 X)) :
    NatTrans.SquareCompatible (C₀.shriekOfCompactification (compactificationOverField f))
      (C₀.push (Compactification.ofIsProper f.left).overG)
      (P.lowerShriekIsoLowerStar hP f).hom (P'.lowerShriekIsoLowerStar hP' f).hom := by
  have h := (C₀.squareCompatible_lowerShriekOfCompactificationIso hP hP'
      (compactificationOverField f) (Compactification.ofIsProper f.left)).comp
    ((NatTrans.SquareCompatible.whiskerRight (C₀.push (Compactification.ofIsProper f.left).overG)
      (C₀.squareCompatible_openImmersionLowerShriekOfIsProperIso f hpull)).comp
      (NatTrans.SquareCompatible.leftUnitor_hom _))
  simpa only [BoundedConstructiblePushforwardData.lowerShriekIsoLowerStar,
    BoundedConstructiblePushforwardData.lowerShriekOfCompactificationOfIsProperIso, Iso.trans_hom,
    Functor.isoWhiskerRight_hom] using h

end LeftFamily

end BoundedConstructibleCoefficientChange

end AlgebraicGeometry.ProEtale.CondensedRing
