/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.CategoryTheory.Adjunction.ExchangeRightPaste
public import WeilConjectures.CategoryTheory.Adjunction.MateTransposeIsIso
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.WeaklyEtale
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.WeaklyEtaleBaseChange

/-!
# Base change for the extension by zero of module objects

Let `Λ` be a commutative condensed ring.

* For a cartesian square `g' ≫ f = f' ≫ g` of schemes with `f` and `f'` weakly étale and `g`
  arbitrary, the exchange morphism `g'^* ⋙ f'_! ⟶ f_! ⋙ g^*` of the extension by zero of module
  objects (`ProEtale.CondensedRing.weaklyEtaleLowerShriekBaseChange`), the left mate of the
  comparison of the pullbacks, is an isomorphism
  (`ProEtale.CondensedRing.weaklyEtaleLowerShriekBaseChangeIso`). Its other mate is the base
  change morphism `f^* g_* ⟶ g'_* f'^*` of the flipped square, invertible by weakly étale base
  change for the pushforward (`ProEtale.CondensedRing.isIso_lowerStarBaseChange_of_isPullback`).
* If `p : P ⟶ T` is weakly étale and `P` is the disjoint union of finitely many copies of `T`
  through sections `s j` of `p`, then `p_! M ≅ ⨁ⱼ (s j)^* M`
  (`ProEtale.CondensedRing.weaklyEtaleLowerShriekObjIsoBiproduct`): both corepresent
  `N ↦ Hom(M, p^* N)`, since a module object on `P` is the product of the pushforwards of its
  restrictions (`ProEtale.CondensedRing.isLimitFanUnitOfIsColimitCofanConst`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

section Corepresentable

variable {C D : Type*} [Category* C] [Category* D] {J : Type*} {F : J → C ⥤ D}
  {G : J → D ⥤ C}

/-- If `X` is the product of the `G j (F j X)` through the units of adjunctions `F j ⊣ G j`, then
`F j` applied to the morphism into `X` with components the transposes of `x j` is `x j`. -/
lemma map_fanIsLimitLift_homEquiv (adj : ∀ j, F j ⊣ G j) {X : C}
    (hX : IsLimit (Fan.mk X fun j ↦ (adj j).unit.app X)) {M : C}
    (x : ∀ j, (F j).obj M ⟶ (F j).obj X) (j : J) :
    (F j).map (Fan.IsLimit.lift hX fun j ↦ (adj j).homEquiv _ _ (x j)) = x j := by
  apply ((adj j).homEquiv _ _).injective
  rw [Adjunction.homEquiv_unit, Adjunction.unit_naturality]
  exact Fan.IsLimit.fac hX _ j

/-- Let `F j ⊣ G j` be finitely many adjunctions and `R : D ⥤ C` a functor with `R ⋙ F j ≅ 𝟭`,
such that every `R N` is the product of the `G j (F j (R N))` through the units. Then
`⨁ⱼ F j M` corepresents `N ↦ Hom(M, R N)`. -/
noncomputable def corepresentableByBiproductOfIsLimitFanUnit [HasZeroMorphisms D] [Finite J]
    [HasFiniteBiproducts D] (adj : ∀ j, F j ⊣ G j) (R : D ⥤ C) (e : ∀ j, R ⋙ F j ≅ 𝟭 D)
    (hR : ∀ N, IsLimit (Fan.mk (R.obj N) fun j ↦ (adj j).unit.app (R.obj N))) (M : C) :
    (R ⋙ coyoneda.obj (Opposite.op M)).CorepresentableBy (⨁ fun j ↦ (F j).obj M) where
  homEquiv {N} := Equiv.symm
    { toFun ψ := biproduct.desc fun j ↦ (F j).map ψ ≫ (e j).hom.app N
      invFun φ := Fan.IsLimit.lift (hR N) fun j ↦ (adj j).homEquiv _ _
          (biproduct.ι (fun j ↦ (F j).obj M) j ≫ φ ≫ (e j).inv.app N)
      left_inv ψ := Fan.IsLimit.hom_ext (hR N) _ _ fun j ↦ by
        simpa [Adjunction.homEquiv_unit] using
          Fan.IsLimit.fac (hR N) (fun j ↦ ψ ≫ (adj j).unit.app (R.obj N)) j
      right_inv φ := biproduct.hom_ext' _ _ fun j ↦ by
        simp [map_fanIsLimitLift_homEquiv] }
  homEquiv_comp {N N'} g φ := by
    rw [Equiv.symm_apply_eq]
    refine biproduct.hom_ext' _ _ fun j ↦ ?_
    have h := (e j).inv.naturality g
    rw [Functor.id_map, Functor.comp_map] at h
    simp [map_fanIsLimitLift_homEquiv, ← reassoc_of% h]

end Corepresentable

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]

section BaseChange

variable {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X}

/-- The exchange morphism `g'^* ⋙ f'_! ⟶ f_! ⋙ g^*` of the extension by zero along weakly étale
morphisms, for a commutative square `g' ≫ f = f' ≫ g`: the left mate of the comparison
`f^* ⋙ g'^* ≅ g^* ⋙ f'^*` of the pullbacks. -/
noncomputable def weaklyEtaleLowerShriekBaseChange (sq : CommSq g' f' f g) [WeaklyEtale f]
    [WeaklyEtale f'] :
    (g')^*⟦Λ⟧ ⋙ weaklyEtaleLowerShriek Λ f' ⟶ weaklyEtaleLowerShriek Λ f ⋙ (g)^*⟦Λ⟧ :=
  (mateEquiv (weaklyEtaleLowerShriekUpperStarAdjunction Λ f)
    (weaklyEtaleLowerShriekUpperStarAdjunction Λ f')).symm
      (upperStarSquareComparison Λ sq.flip).hom

/-- For a cartesian square, the exchange morphism of the extension by zero is an isomorphism: its
other mate is the weakly étale base change morphism of the pushforward along `g`. -/
theorem isIso_weaklyEtaleLowerShriekBaseChange (hsq : IsPullback g' f' f g) [WeaklyEtale f]
    [WeaklyEtale f'] : IsIso (weaklyEtaleLowerShriekBaseChange Λ hsq.toCommSq) := by
  have := isIso_lowerStarBaseChange_of_isPullback Λ hsq.flip
  rw [lowerStarBaseChange, Adjunction.exchangeRight_eq_mateEquiv] at this
  exact isIso_mateEquiv_symm_of_isIso_mateEquiv _ _
    (upperStarLowerStarAdjunction Λ g') (upperStarLowerStarAdjunction Λ g) _

/-- **Base change for the extension by zero**: for a cartesian square `g' ≫ f = f' ≫ g` with
`f` and `f'` weakly étale and `g` arbitrary, `g'^* ⋙ f'_! ≅ f_! ⋙ g^*`. -/
noncomputable def weaklyEtaleLowerShriekBaseChangeIso (hsq : IsPullback g' f' f g) [WeaklyEtale f]
    [WeaklyEtale f'] :
    (g')^*⟦Λ⟧ ⋙ weaklyEtaleLowerShriek Λ f' ≅ weaklyEtaleLowerShriek Λ f ⋙ (g)^*⟦Λ⟧ :=
  have := isIso_weaklyEtaleLowerShriekBaseChange Λ hsq
  asIso (weaklyEtaleLowerShriekBaseChange Λ hsq.toCommSq)

end BaseChange

section SplitCover

variable {J : Type u} [Finite J] {P T : Scheme.{u}}

/-- For a section `s` of `p : P ⟶ T`, the identification `p^* ⋙ s^* ≅ 𝟭` of pullbacks of
module objects. -/
noncomputable def upperStarCompSectionIso (p : P ⟶ T) {s : T ⟶ P} (h : s ≫ p = 𝟙 T) :
    (p)^*⟦Λ⟧ ⋙ (s)^*⟦Λ⟧ ≅ 𝟭 _ :=
  (upperStarComp Λ s p).symm ≪≫ upperStarCongr Λ h ≪≫ upperStarId Λ T

/-- **Extension by zero along a split finite cover**: if `P` is the disjoint union of finitely
many copies of `T` through sections `s j` of the weakly étale morphism `p : P ⟶ T`, then
`p_! M ≅ ⨁ⱼ (s j)^* M`. -/
noncomputable def weaklyEtaleLowerShriekObjIsoBiproduct {p : P ⟶ T} [WeaklyEtale p]
    {s : J → (T ⟶ P)} (hs : ∀ j, s j ≫ p = 𝟙 T) (hP : IsColimit (Cofan.mk P s))
    (M : Mod (Sheaf (Scheme.ProEt.topology P) Ab.{u + 1}) (condensedRingObj Λ P)) :
    (weaklyEtaleLowerShriek Λ p).obj M ≅ ⨁ fun j ↦ ((s j)^*⟦Λ⟧).obj M :=
  ((weaklyEtaleLowerShriekUpperStarAdjunction Λ p).corepresentableBy M).uniqueUpToIso
    (corepresentableByBiproductOfIsLimitFanUnit (fun j ↦ upperStarLowerStarAdjunction Λ (s j))
      (p)^*⟦Λ⟧ (fun j ↦ upperStarCompSectionIso Λ p (hs j))
      (fun N ↦ isLimitFanUnitOfIsColimitCofanConst Λ hP ((p)^*⟦Λ⟧.obj N)) M)

end SplitCover

end AlgebraicGeometry.ProEtale.CondensedRing
