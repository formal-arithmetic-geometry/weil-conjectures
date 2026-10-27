/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.Purity.Smooth.AffineLineNormalization
public import WeilConjectures.EtaleCohomology.TateTwist.KummerClass
public import WeilConjectures.SixFunctors.Etale.Derived.DirectImageAmplitude

import WeilConjectures.EtaleCohomology.Purity.Smooth.GmRelativeKummer
import WeilConjectures.SixFunctors.Etale.Derived.BaseChangeCube
import WeilConjectures.SixFunctors.Etale.Derived.SmoothDuality.Local

/-!
# The cohomology of `𝔸¹` and `𝔾ₘ` with coefficients in the Tate twist `μₙ ⊗ Λ`

For the concrete Tate twist `Λ(1) = μₙ ⊗ Λ` and its Kummer classes
(`AlgebraicGeometry.Etale.hasKummerClass`), the computations of `sk-prop-a1-kummer` on the
affine line `p : 𝔸¹_B ⟶ B` and on `π : 𝔾_{m,B} ⟶ 𝔸¹_B ⟶ B`, over a base `B` separated and
locally of finite type over a field on which `n` is invertible:

* `Rp_* Λ(1)` is `Λ_B(1)` in degree zero;
* restriction along `j : 𝔾_{m,B} ⟶ 𝔸¹_B` identifies `R⁰p_* Λ(1)` with `R⁰π_* Λ(1)`;
* `R¹π_* Λ(1)` is free of rank one on the Kummer class `κ(t)` of the coordinate;
* `R^mπ_* Λ(1) = 0` for `m ≥ 2`.

These are the clauses (a)–(c) of `sk-prop-a1-kummer`, read for the twisted coefficients `Λ(1)`
as they are used in the proof of `sk-prop-a1`, and with the generator `κ(t)` of clause (b) made
explicit. The forms `AlgebraicGeometry.Etale.nonempty_iso_homology_one_multiplicativeGroup` and
`AlgebraicGeometry.Etale.isZero_homology_multiplicativeGroup` of
`WeilConjectures.EtaleCohomology.Purity.Smooth.AffineLine` assume a normalized twist datum,
which for the concrete twist is the very statement `sk-prop-a1` they are used to prove, and they
do not name the generator; hence these statements for the concrete twist. The vanishing in
negative degrees is the left t-exactness of the direct images.

Over an algebraically closed field and for `B` quasi-compact, the same computations, phrased
for the direct image along the composite `G ⟶ 𝔸¹_B ⟶ B` of an arbitrary open complement of the
zero section, are proved in `WeilConjectures.EtaleCohomology.Purity.Smooth.GmRelativeKummer`,
for instance clause (c) as
`AlgebraicGeometry.Etale.isZero_homology_rightDerivedLowerStar_tateObject_multiplicativeGroup`;
the statements here are over an arbitrary field.

## Main statements

- `AlgebraicGeometry.Etale.affineLine_multiplicativeGroup_homology_tateObject`
- `AlgebraicGeometry.Etale.isZero_homology_rightDerivedLowerStar_tateObject_affineLine`
- `AlgebraicGeometry.Etale.isIso_homology_zero_map_unit_multiplicativeGroup`
- `AlgebraicGeometry.Etale.isIso_shiftMap_kummerClassAffineLineDirectImage`
- `AlgebraicGeometry.Etale.isZero_homology_rightDerivedLowerStar_tateObject_basicOpen`
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

-- Keep the symmetric braiding and sheaf colimits explicit during instance search.
attribute [local instance high] SymmetricCategory.toBraidedCategory
attribute [local instance 2000] CategoryTheory.Sheaf.instHasColimitsOfShape

attribute [local irreducible] upperStar lowerStar CategoryTheory.Functor.leftDerivedFunctor
  rightDerivedLowerStar derivedUpperStarLowerStarAdjunction
  CategoryTheory.Functor.rightDerivedFunctor derivedBaseChangeMap derivedSquareUpperStarIso
  tateTwistObject tateTwistSheaf
  leftDerivedUpperStarConstantComplexIso leftDerivedUpperStarTateObjectIso
  rightDerivedLowerStarComp leftDerivedUpperStarComp

attribute [local instance] HasInvertibleExponent.opens

-- An interface for the class map, proved before protecting the constant-object alias.
private theorem kummer_direct_image_formula (Λ : Type (u + 1)) [CommRing Λ]
    [NeZero (ringChar Λ)] (B : Scheme.{u}) [HasInvertibleExponent Λ B] :
    let X := 𝔸(ULift.{u} (Fin 1); B)
    let p : X ⟶ B := X ↘ B
    let j := (X.basicOpen (AffineSpace.coord B (ULift.up.{u} (0 : Fin 1)))).ι
    let Rp := R((p)_*[ModuleCat.{u + 1} Λ])
    let Rj := R((j)_*[ModuleCat.{u + 1} Λ])
    kummerClassAffineLineDirectImage Λ B =
      (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) p).homEquiv _ _
        ((leftDerivedUpperStarConstantComplexIso Λ p).hom ≫
          (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) j).homEquiv _ _
            ((leftDerivedUpperStarConstantComplexIso Λ j).hom ≫
              kummerClass Λ (X.basicOpenUnit (AffineSpace.coord B (ULift.up 0))) ≫
                (leftDerivedUpperStarTateObjectIso (Λ := Λ) j 1).inv⟦(1 : ℤ)⟧')) ≫
        Rp.map ((Rj.commShiftIso (1 : ℤ)).hom.app _) ≫
          (Rp.commShiftIso (1 : ℤ)).hom.app _ := by
  dsimp only
  simp only [kummerClassAffineLineDirectImage, ShiftedHom.map, kummerClassAdjoint,
    Adjunction.homEquiv_unit, constantComplex, Functor.map_comp, Category.assoc]

attribute [local irreducible] constantComplex conjugateEquiv Adjunction.comp

-- Naturality and composition of adjoints, with no geometric constructions to unfold.
private theorem adjoint_composition {C D E : Type*} [Category C] [Category D] [Category E]
    {F : C ⥤ D} {R : D ⥤ C} {F' : D ⥤ E} {R' : E ⥤ D}
    {L : C ⥤ E} {S : E ⥤ C} (a : F ⊣ R) (b : F' ⊣ R') (c : L ⊣ S)
    (e : L ⟶ F ⋙ F') {A : C} {B : D} {N N' : E}
    (θ : F.obj A ⟶ B) (α : F'.obj B ⟶ N) (v : N ⟶ N') :
    a.homEquiv _ _ (θ ≫ b.homEquiv _ _ α) ≫ R.map (R'.map v) ≫
        (conjugateEquiv (a.comp b) c e).app N' =
      c.homEquiv _ _ (e.app A ≫ F'.map θ ≫ α ≫ v) := by
  have h : a.homEquiv _ _ (θ ≫ b.homEquiv _ _ α) ≫ R.map (R'.map v) =
      (a.comp b).homEquiv _ _ (F'.map θ ≫ α ≫ v) := by
    rw [Adjunction.comp_homEquiv]
    change a.homEquiv _ _ (θ ≫ b.homEquiv _ _ α) ≫ R.map (R'.map v) =
      a.homEquiv _ _ (b.homEquiv _ _ (F'.map θ ≫ α ≫ v))
    rw [← Adjunction.homEquiv_naturality_right]
    congr 1
    rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right]
    exact Category.assoc _ _ _
  rw [← Category.assoc, h, Adjunction.homEquiv_comp_conjugateEquiv_app]

private theorem iso_adjoint_composition {C D E V : Type*}
    [Category C] [Category D] [Category E] [Category V]
    {F : C ⥤ D} {R : D ⥤ C} {F' : D ⥤ E} {R' : E ⥤ D}
    {L : C ⥤ E} {S : E ⥤ C} (a : F ⊣ R) (b : F' ⊣ R') (c : L ⊣ S)
    (e : L ⟶ F ⋙ F') {A : C} {B : D} {N N' : E}
    (θ : F.obj A ⟶ B) (α : F'.obj B ⟶ N) (v : N ⟶ N') [IsIso v]
    [IsIso ((conjugateEquiv (a.comp b) c e).app N')]
    (H : C ⥤ V)
    (h : IsIso (H.map (c.homEquiv _ _ (e.app A ≫ F'.map θ ≫ α ≫ v)))) :
    IsIso (H.map (a.homEquiv _ _ (θ ≫ b.homEquiv _ _ α))) := by
  have he := congrArg H.map (adjoint_composition a b c e θ α v)
  simp only [Functor.map_comp] at he
  rw [← he] at h
  rw [← Category.assoc, isIso_comp_right_iff, isIso_comp_right_iff] at h
  exact h

private theorem field_exchange (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {k : Type u} [Field k] [HasInvertibleExponent Λ (Spec (.of k))]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [Smooth f] [IsSeparated f] [QuasiCompact f]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    [IsFiniteLocallyConstantSheaf F] {T XT : Scheme.{u}} [IsNoetherian T]
    (t : T ⟶ Spec (.of k)) (g : XT ⟶ X) (fT : XT ⟶ T)
    (sq : IsPullback g fT f t) :
    IsIso ((derivedBaseChangeMap (ModuleCat.{u + 1} Λ) sq.toCommSq).app
      ((_root_.DerivedCategory.singleFunctor _ 0).obj F)) := by
  obtain ⟨U, ⟨s, hs⟩, h⟩ := smoothGenericDirectImage Λ (𝟙 (Spec (.of k))) f F
  have hr : Set.range t ⊆ (U : Set (Spec (.of k))) := by
    intro x hx
    rwa [Subsingleton.elim x s]
  have h' := (hasConstructibleDirectImageBaseChangeOn_iff (𝟙 _) f F U).2 h
  exact (h' T t hr T XT t (𝟙 T) g fT (by simpa using IsPullback.id_vert t) sq).2


private theorem field_exchange_tate (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    [NeZero (ringChar Λ)] {k : Type u} [Field k]
    [HasInvertibleExponent Λ (Spec (.of k))]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [Smooth f] [IsSeparated f] [QuasiCompact f]
    [HasInvertibleExponent Λ X] {T XT : Scheme.{u}} [IsNoetherian T]
    (t : T ⟶ Spec (.of k)) (g : XT ⟶ X) (fT : XT ⟶ T)
    (sq : IsPullback g fT f t) :
    IsIso ((derivedBaseChangeMap (ModuleCat.{u + 1} Λ) sq.toCommSq).app
      (tateObject Λ X 1)) := by
  have := isFiniteLocallyConstantSheaf_tateTwistSheaf Λ X 1
  exact (NatTrans.isIso_app_iff_of_iso _ (tateTwistObjectIsoSingleFunctor Λ X 1)).2
    (field_exchange Λ f (tateTwistSheaf Λ X 1) t g fT sq)



private theorem etale_exchange (Λ : Type (u + 1)) [CommRing Λ]
    {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y} (sq : IsPullback g' f' f g) [Etale g]
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (n : ℤ) [K.IsGE n] :
    IsIso ((derivedBaseChangeMap (ModuleCat.{u + 1} Λ) sq.toCommSq).app K) := by
  let K' : _root_.DerivedCategory.Plus
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) := ⟨K, ⟨n, inferInstance⟩⟩
  have := isIso_derivedBaseChangeMapPlus_of_etale (Λ := Λ) sq
  exact (isIso_derivedBaseChangeMap_app_ι_obj_iff
    (ModuleCat.{u + 1} Λ) sq.toCommSq K').2 inferInstance

-- Coherence of the three derived comparison functors is expensive to elaborate.
private theorem field_exchange_local (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    [NeZero (ringChar Λ)] {k : Type u} [Field k]
    [HasInvertibleExponent Λ (Spec (.of k))]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [Smooth f] [IsSeparated f] [QuasiCompact f]
    [HasInvertibleExponent Λ X] {T XT : Scheme.{u}} [IsLocallyNoetherian T]
    (t : T ⟶ Spec (.of k)) (g : XT ⟶ X) (fT : XT ⟶ T)
    (sq : IsPullback g fT f t) :
    IsIso ((derivedBaseChangeMap (ModuleCat.{u + 1} Λ) sq.toCommSq).app
      (tateObject Λ X 1)) := by
  let M := tateObject Λ X 1
  have : M.IsGE 0 := DerivedCategory.TStructure.t.isGE_of_iso
    (tateTwistObjectIsoSingleFunctor Λ X 1).symm 0
  refine isIso_of_isIso_leftDerivedUpperStar_map_of_jointlySurjective Λ T.affineCover.f
    (fun x ↦ ⟨T.affineCover.idx x, T.affineCover.covers x⟩) _ fun i ↦ ?_
  let v := T.affineCover.f i
  have : IsNoetherian (T.affineCover.X i) := ⟨⟩
  let P := pullback fT v
  let h : P ⟶ XT := pullback.fst fT v
  let fP : P ⟶ T.affineCover.X i := pullback.snd fT v
  have sq' : IsPullback h fP fT v := IsPullback.of_hasPullback fT v
  have h₂ := field_exchange_tate Λ f (v ≫ t) (h ≫ g) fP (sq'.paste_horiz sq)
  have : HasInvertibleExponent Λ XT := .of_hom g
  have : ((L((g)^*[ModuleCat.{u + 1} Λ])).obj M).IsGE 0 :=
    DerivedCategory.TStructure.t.isGE_of_iso
      (leftDerivedUpperStarTateObjectIso (Λ := Λ) g 1 ≪≫
        tateTwistObjectIsoSingleFunctor Λ XT 1).symm 0
  have h₃ := etale_exchange Λ sq' ((L((g)^*[ModuleCat.{u + 1} Λ])).obj M) 0
  have hp := derivedBaseChangeMap_paste (ModuleCat.{u + 1} Λ) sq.toCommSq sq'.toCommSq
    (sq'.paste_horiz sq).toCommSq rfl rfl M
  have hcomp : IsIso
      ((leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ) v t (v ≫ t) rfl).hom.app
        ((R((f)_*[ModuleCat.{u + 1} Λ])).obj M) ≫
      (L((v)^*[ModuleCat.{u + 1} Λ])).map
        ((derivedBaseChangeMap (ModuleCat.{u + 1} Λ) sq.toCommSq).app M) ≫
      (derivedBaseChangeMap (ModuleCat.{u + 1} Λ) sq'.toCommSq).app
        ((L((g)^*[ModuleCat.{u + 1} Λ])).obj M) ≫
      (R((fP)_*[ModuleCat.{u + 1} Λ])).map
        ((leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ) h g (h ≫ g) rfl).inv.app M)) := by
    rw [hp]
    exact h₂
  rw [isIso_comp_left_iff, ← Category.assoc, isIso_comp_right_iff,
    isIso_comp_right_iff] at hcomp
  exact hcomp


private theorem field_exchange_cancel (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    [NeZero (ringChar Λ)] {k : Type u} [Field k]
    [HasInvertibleExponent Λ (Spec (.of k))]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [Smooth f] [IsSeparated f] [QuasiCompact f]
    [HasInvertibleExponent Λ X] {T XT T' XT' : Scheme.{u}}
    [IsLocallyNoetherian T] [IsLocallyNoetherian T'] [HasInvertibleExponent Λ XT]
    (t : T ⟶ Spec (.of k)) (g : XT ⟶ X) (fT : XT ⟶ T)
    (sq : IsPullback g fT f t) (v : T' ⟶ T) (h : XT' ⟶ XT) (fT' : XT' ⟶ T')
    (sq' : IsPullback h fT' fT v) :
    IsIso ((derivedBaseChangeMap (ModuleCat.{u + 1} Λ) sq'.toCommSq).app
      (tateObject Λ XT 1)) := by
  let M := tateObject Λ X 1
  have h₁ := field_exchange_local Λ f t g fT sq
  have h₂ := field_exchange_local Λ f (v ≫ t) (h ≫ g) fT' (sq'.paste_horiz sq)
  have hp := derivedBaseChangeMap_paste (ModuleCat.{u + 1} Λ) sq.toCommSq sq'.toCommSq
    (sq'.paste_horiz sq).toCommSq rfl rfl M
  have hcomp : IsIso
      ((leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ) v t (v ≫ t) rfl).hom.app
        ((R((f)_*[ModuleCat.{u + 1} Λ])).obj M) ≫
      (L((v)^*[ModuleCat.{u + 1} Λ])).map
        ((derivedBaseChangeMap (ModuleCat.{u + 1} Λ) sq.toCommSq).app M) ≫
      (derivedBaseChangeMap (ModuleCat.{u + 1} Λ) sq'.toCommSq).app
        ((L((g)^*[ModuleCat.{u + 1} Λ])).obj M) ≫
      (R((fT')_*[ModuleCat.{u + 1} Λ])).map
        ((leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ) h g (h ≫ g) rfl).inv.app M)) := by
    rw [hp]
    exact h₂
  rw [isIso_comp_left_iff, isIso_comp_left_iff,
    isIso_comp_right_iff] at hcomp
  exact (NatTrans.isIso_app_iff_of_iso _ (leftDerivedUpperStarTateObjectIso g 1)).1 hcomp



-- The unit comparison is formed from several derived functors.
private theorem unit_homology_exchange (Λ : Type (u + 1)) [CommRing Λ]
    [NeZero (ringChar Λ)] {X' X Y' Y : Scheme.{u}}
    [HasInvertibleExponent Λ X] [HasInvertibleExponent Λ Y]
    [HasInvertibleExponent Λ Y']
    {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
    (sq : CommSq g' f' f g)
    (hex : IsIso ((derivedBaseChangeMap (ModuleCat.{u + 1} Λ) sq).app
      (tateObject Λ X 1))) (n : ℤ) :
    IsIso ((_root_.DerivedCategory.homologyFunctor _ n).map
      ((L((g)^*[ModuleCat.{u + 1} Λ])).map
        ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f).unit.app
          (tateObject Λ Y 1)))) ↔
    IsIso ((_root_.DerivedCategory.homologyFunctor _ n).map
      ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f').unit.app
        (tateObject Λ Y' 1))) := by
  let H := _root_.DerivedCategory.homologyFunctor
    (Sheaf Y'.smallEtaleTopology (ModuleCat.{u + 1} Λ)) n
  let M := tateObject Λ Y 1
  have hb : IsIso ((derivedBaseChangeMap (ModuleCat.{u + 1} Λ) sq).app
      ((L((f)^*[ModuleCat.{u + 1} Λ])).obj M)) :=
    (NatTrans.isIso_app_iff_of_iso _ (leftDerivedUpperStarTateObjectIso f 1)).2 hex
  have hu := congrArg H.map
    (map_unit_derivedBaseChangeMap_app (ModuleCat.{u + 1} Λ) sq M)
  simp only [Functor.map_comp] at hu
  have hi : IsIso (H.map ((L((g)^*[ModuleCat.{u + 1} Λ])).map
      ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f).unit.app M))) ↔
      IsIso (H.map ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f').unit.app
        ((L((g)^*[ModuleCat.{u + 1} Λ])).obj M))) := by
    rw [← isIso_comp_right_iff _ (H.map
      ((derivedBaseChangeMap (ModuleCat.{u + 1} Λ) sq).app
        ((L((f)^*[ModuleCat.{u + 1} Λ])).obj M))), hu, isIso_comp_right_iff]
  exact hi.trans (NatTrans.isIso_app_iff_of_iso
    (Functor.whiskerRight (derivedUpperStarLowerStarAdjunction
      (ModuleCat.{u + 1} Λ) f').unit H) (leftDerivedUpperStarTateObjectIso g 1))



-- Compare the adjoint class through the base-change and coefficient isomorphisms.
private theorem kummer_homology_exchange (Λ : Type (u + 1)) [CommRing Λ]
    [NeZero (ringChar Λ)] {X' X Y' Y : Scheme.{u}}
    [HasInvertibleExponent Λ X] [HasInvertibleExponent Λ X']
    {q : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
    (sq : CommSq q f' f g) (v : Γ(X, ⊤)ˣ) (v' : Γ(X', ⊤)ˣ)
    (hv : Units.map q.appTop.hom.toMonoidHom v = v')
    (hex : IsIso ((derivedBaseChangeMap (ModuleCat.{u + 1} Λ) sq).app
      (tateObject Λ X 1))) :
    IsIso ((_root_.DerivedCategory.homologyFunctor _ 0).map
      ((L((g)^*[ModuleCat.{u + 1} Λ])).map
        ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f).homEquiv _ _
          ((leftDerivedUpperStarConstantComplexIso Λ f).hom ≫ kummerClass Λ v)))) ↔
    IsIso ((_root_.DerivedCategory.homologyFunctor _ 0).map
      ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f').homEquiv _ _
        ((leftDerivedUpperStarConstantComplexIso Λ f').hom ≫ kummerClass Λ v'))) := by
  let H := _root_.DerivedCategory.homologyFunctor
    (Sheaf Y'.smallEtaleTopology (ModuleCat.{u + 1} Λ)) 0
  let K := tateObject Λ X 1
  let BC := derivedBaseChangeMap (ModuleCat.{u + 1} Λ) sq
  let θf := leftDerivedUpperStarConstantComplexIso Λ f
  let θf' := leftDerivedUpperStarConstantComplexIso Λ f'
  let θg := leftDerivedUpperStarConstantComplexIso Λ g
  let θq := leftDerivedUpperStarConstantComplexIso Λ q
  let κb := (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f).homEquiv _ _
    (θf.hom ≫ kummerClass Λ v)
  let κb' := (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f').homEquiv _ _
    (θf'.hom ≫ kummerClass Λ v')
  let C := ((L((q)^*[ModuleCat.{u + 1} Λ])).commShiftIso (1 : ℤ)).app K ≪≫
    (shiftFunctor _ (1 : ℤ)).mapIso (leftDerivedUpperStarTateObjectIso q 1)
  have hnat : (L((q)^*[ModuleCat.{u + 1} Λ])).map (kummerClass Λ v) ≫ C.hom =
      θq.hom ≫ kummerClass Λ v' := by
    simpa only [C, Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom, hv] using
      leftDerivedUpperStar_map_kummerClass Λ q v
  have hR : (L((g)^*[ModuleCat.{u + 1} Λ])).map κb ≫ BC.app (K⟦(1 : ℤ)⟧) ≫
      (R((f')_*[ModuleCat.{u + 1} Λ])).map C.hom = θg.hom ≫ κb' := by
    rw [← Category.assoc, derivedBaseChangeMap_app_homEquiv,
      ← Adjunction.homEquiv_naturality_right, ← Adjunction.homEquiv_naturality_left]
    congr 1
    simp only [Functor.map_comp, Category.assoc]
    rw [hnat]
    exact (reassoc_of% (derivedSquareUpperStarIso_hom_app_constantComplex Λ sq)) _
  have hb : IsIso (BC.app (K⟦(1 : ℤ)⟧)) := by
    rw [NatTrans.app_shift BC (1 : ℤ) K]
    infer_instance
  have h := congrArg H.map hR
  simp only [Functor.map_comp] at h
  change IsIso (H.map ((L((g)^*[ModuleCat.{u + 1} Λ])).map κb)) ↔ IsIso (H.map κb')
  rw [← isIso_comp_right_iff _ (H.map (BC.app (K⟦(1 : ℤ)⟧))),
    ← isIso_comp_right_iff _ (H.map ((R((f')_*[ModuleCat.{u + 1} Λ])).map C.hom)),
    Category.assoc, h, isIso_comp_left_iff]



-- First base change the smooth field model, then cancel its comparison map.
private theorem affine_point_exchange (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    [NeZero (ringChar Λ)] {k Ω : Type u} [Field k] [Field Ω]
    {B : Scheme.{u}} (aB : B ⟶ Spec (.of k)) [LocallyOfFiniteType aB]
    [HasInvertibleExponent Λ B] (x : Spec (.of Ω) ⟶ B) :
    IsIso ((derivedBaseChangeMap (ModuleCat.{u + 1} Λ)
      (AffineSpace.isPullback_map (n := ULift.{u} (Fin 1)) x).toCommSq).app
        (tateObject Λ 𝔸(ULift.{u} (Fin 1); B) 1)) := by
  have : Nonempty B := ⟨x (IsLocalRing.closedPoint Ω)⟩
  have : HasInvertibleExponent Λ (Spec (.of k)) := .of_hom_of_nonempty aB
  have : IsLocallyNoetherian B := LocallyOfFiniteType.isLocallyNoetherian aB
  have : Smooth (𝔸(ULift.{u} (Fin 1); Spec (.of k)) ↘ Spec (.of k)) :=
    SmoothOfRelativeDimension.smooth (n := Nat.card (ULift.{u} (Fin 1))) _
  exact field_exchange_cancel Λ (𝔸(ULift.{u} (Fin 1); Spec (.of k)) ↘ Spec (.of k))
    aB (AffineSpace.map (ULift.{u} (Fin 1)) aB) _ (AffineSpace.isPullback_map aB)
    x (AffineSpace.map (ULift.{u} (Fin 1)) x) _ (AffineSpace.isPullback_map x)

-- The punctured line is the smooth affine open of the field model.
private theorem multiplicative_point_exchange (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    [NeZero (ringChar Λ)] {k Ω : Type u} [Field k] [Field Ω]
    {B : Scheme.{u}} (aB : B ⟶ Spec (.of k)) [LocallyOfFiniteType aB]
    [HasInvertibleExponent Λ B] (x : Spec (.of Ω) ⟶ B)
    {G G' : Scheme.{u}} (j : G ⟶ 𝔸(ULift.{u} (Fin 1); B)) [IsOpenImmersion j]
    (hj : Set.range j.base =
      (Set.range (AffineSpace.zeroSection (ULift.{u} (Fin 1)) B).base)ᶜ)
    (j' : G' ⟶ 𝔸(ULift.{u} (Fin 1); Spec (.of Ω))) [IsOpenImmersion j']
    (hj' : Set.range j'.base =
      (Set.range (AffineSpace.zeroSection (ULift.{u} (Fin 1)) (Spec (.of Ω))).base)ᶜ)
    [HasInvertibleExponent Λ G] :
    IsIso ((derivedBaseChangeMap (ModuleCat.{u + 1} Λ)
      (AffineSpace.isPullback_complementMap_over x j j' hj hj').toCommSq).app
        (tateObject Λ G 1)) := by
  have : Nonempty B := ⟨x (IsLocalRing.closedPoint Ω)⟩
  have : HasInvertibleExponent Λ (Spec (.of k)) := .of_hom_of_nonempty aB
  have : IsLocallyNoetherian B := LocallyOfFiniteType.isLocallyNoetherian aB
  let j₀ := (multiplicativeGroupModel k).ι
  have hj₀ := range_multiplicativeGroupModel_ι k
  have : HasInvertibleExponent Λ (multiplicativeGroupModel k) := .of_hom j₀
  have : Smooth (𝔸(ULift.{u} (Fin 1); Spec (.of k)) ↘ Spec (.of k)) :=
    SmoothOfRelativeDimension.smooth (n := Nat.card (ULift.{u} (Fin 1))) _
  have : IsOpenImmersion j₀ := inferInstance
  exact field_exchange_cancel Λ
    (j₀ ≫ 𝔸(ULift.{u} (Fin 1); Spec (.of k)) ↘ Spec (.of k))
    aB (AffineSpace.complementMap aB j₀ j hj₀ hj) _
    (AffineSpace.isPullback_complementMap_over aB j₀ j hj₀ hj)
    x (AffineSpace.complementMap x j j' hj hj') _
    (AffineSpace.isPullback_complementMap_over x j j' hj hj')



private theorem reflect_homology_iso (Λ : Type (u + 1)) [CommRing Λ]
    {B : Scheme.{u}} {M N : _root_.DerivedCategory
      (Sheaf B.smallEtaleTopology (ModuleCat.{u + 1} Λ))} (f : M ⟶ N) (n : ℤ)
    (h : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ B),
      IsIso ((_root_.DerivedCategory.homologyFunctor _ n).map
        ((L((x)^*[ModuleCat.{u + 1} Λ])).map f))) :
    IsIso ((_root_.DerivedCategory.homologyFunctor _ n).map f) := by
  refine isIso_of_isIso_upperStar_map_of_jointlySurjective (ModuleCat.{u + 1} Λ)
    (fun y ↦ B.algClosurePoint y)
    (fun y ↦ ⟨y, IsLocalRing.closedPoint _, Scheme.algClosurePoint_base _ _ _⟩) _ fun y ↦ ?_
  exact (NatIso.isIso_map_iff
    (leftDerivedUpperStarHomologyFunctorIso _ (B.algClosurePoint y) n) f).2 (h _ _)

private theorem reflect_homology_zero (Λ : Type (u + 1)) [CommRing Λ]
    {B : Scheme.{u}} (M : _root_.DerivedCategory
      (Sheaf B.smallEtaleTopology (ModuleCat.{u + 1} Λ))) (n : ℤ)
    (h : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ B),
      IsZero ((_root_.DerivedCategory.homologyFunctor _ n).obj
        ((L((x)^*[ModuleCat.{u + 1} Λ])).obj M))) :
    IsZero ((_root_.DerivedCategory.homologyFunctor _ n).obj M) := by
  exact isZero_homology_of_jointlySurjective Λ (fun y ↦ B.algClosurePoint y)
    (fun y ↦ ⟨y, IsLocalRing.closedPoint _, Scheme.algClosurePoint_base _ _ _⟩) M n
    (fun y ↦ h _ _)


variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] [NeZero (ringChar Λ)]
  {k : Type u} [Field k] (B : Scheme.{u}) (aB : B ⟶ Spec (.of k)) [IsSeparated aB]
  [LocallyOfFiniteType aB] [HasInvertibleExponent Λ B]

attribute [local instance] HasInvertibleExponent.opens



-- The adopted statement retains separatedness, though the comparison proof does not need it.
set_option linter.unusedSectionVars false in
set_option maxHeartbeats 600000 in
-- The proof compares the units and class maps of composite derived adjunctions.
set_option maxRecDepth 10000 in
include aB in
/-- Blueprint `sk-prop-a1-kummer`: The affine line and `𝔾ₘ` with `Λ(1)`-coefficients

The proposition `sk-prop-a1-kummer`, clauses (a)–(c), for the concrete Tate twist
`Λ(1) = μₙ ⊗ Λ`, with the generator `κ(t)` of clause (b) made explicit. Write
`p : 𝔸¹_B ⟶ B` for the projection, `j : 𝔾_{m,B} ⟶ 𝔸¹_B` for the open complement of the zero
section and `π = p ∘ j`, so that `Rπ_* Λ(1) = Rp_* Rj_* j^* Λ(1)`:
* (a) `R^m p_* Λ(1) = 0` for `m > 0` (the affine line is acyclic, and `Λ(1)` is pulled back
  from `B`);
* (b) restriction along `j` identifies `R⁰p_* Λ(1)` with `R⁰π_* Λ(1)`, and the Kummer class
  `κ(t) : Λ_B ⟶ (Rπ_* Λ(1))[1]` (`AlgebraicGeometry.Etale.kummerClassAffineLineDirectImage`)
  induces an isomorphism `Λ_B ≅ R¹π_* Λ(1)`;
* (c) `R^m π_* Λ(1) = 0` for `m ≥ 2`.

The forms of this proposition in `WeilConjectures.EtaleCohomology.Purity.Smooth.AffineLine`
assume a normalized twist datum, which for the concrete twist is the statement `sk-prop-a1`
proved from this one, and do not name the generator. -/
theorem affineLine_multiplicativeGroup_homology_tateObject :
    (∀ n : ℤ, 0 < n → IsZero ((_root_.DerivedCategory.homologyFunctor _ n).obj
      ((R((𝔸(ULift.{u} (Fin 1); B) ↘ B)_*[ModuleCat.{u + 1} Λ])).obj
        (tateObject Λ 𝔸(ULift.{u} (Fin 1); B) 1)))) ∧
    IsIso ((_root_.DerivedCategory.homologyFunctor _ 0).map
      ((R((𝔸(ULift.{u} (Fin 1); B) ↘ B)_*[ModuleCat.{u + 1} Λ])).map
        ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ)
          ((𝔸(ULift.{u} (Fin 1); B).basicOpen (AffineSpace.coord B (ULift.up 0))).ι)).unit.app
            (tateObject Λ 𝔸(ULift.{u} (Fin 1); B) 1)))) ∧
    IsIso ((_root_.DerivedCategory.homologyFunctor _ 0).shiftMap
      (kummerClassAffineLineDirectImage Λ B) 0 1 (by norm_num)) ∧
    (∀ n : ℤ, 2 ≤ n → IsZero ((_root_.DerivedCategory.homologyFunctor _ n).obj
      ((R((𝔸(ULift.{u} (Fin 1); B) ↘ B)_*[ModuleCat.{u + 1} Λ])).obj
        ((R(((𝔸(ULift.{u} (Fin 1); B).basicOpen (AffineSpace.coord B (ULift.up 0))).ι)_*[
            ModuleCat.{u + 1} Λ])).obj
          ((L(((𝔸(ULift.{u} (Fin 1); B).basicOpen (AffineSpace.coord B (ULift.up 0))).ι)^*[
            ModuleCat.{u + 1} Λ])).obj (tateObject Λ 𝔸(ULift.{u} (Fin 1); B) 1)))))) := by
  let X := 𝔸(ULift.{u} (Fin 1); B)
  let p : X ⟶ B := X ↘ B
  let j := (X.basicOpen (AffineSpace.coord B (ULift.up.{u} (0 : Fin 1)))).ι
  let G := (X.basicOpen (AffineSpace.coord B (ULift.up.{u} (0 : Fin 1)))).toScheme
  have hj : Set.range j.base =
      (Set.range (AffineSpace.zeroSection (ULift.{u} (Fin 1)) B).base)ᶜ :=
    AffineSpace.range_basicOpen_ι_coord B
  let Rp := R((p)_*[ModuleCat.{u + 1} Λ])
  let Rj := R((j)_*[ModuleCat.{u + 1} Λ])
  let Lj := L((j)^*[ModuleCat.{u + 1} Λ])
  let H := _root_.DerivedCategory.homologyFunctor
    (Sheaf B.smallEtaleTopology (ModuleCat.{u + 1} Λ))
  let M := tateObject Λ B 1
  let tX := leftDerivedUpperStarTateObjectIso (Λ := Λ) p 1
  have hp : IsIso ((derivedUpperStarLowerStarAdjunction
      (ModuleCat.{u + 1} Λ) p).unit.app M) := by
    rw [_root_.DerivedCategory.isIso_iff]
    intro n
    refine reflect_homology_iso Λ _ n fun Ω _ _ x ↦ ?_
    have : HasInvertibleExponent Λ (Spec (.of Ω)) := .of_hom x
    have hΩ := isIso_unit_tateObject_affineLine Λ (𝟙 (Spec (.of Ω)))
    exact (unit_homology_exchange Λ
      (AffineSpace.isPullback_map (n := ULift.{u} (Fin 1)) x).toCommSq
      (affine_point_exchange Λ aB x) n).2 inferInstance
  have hjp : IsIso ((H 0).map ((derivedUpperStarLowerStarAdjunction
      (ModuleCat.{u + 1} Λ) (j ≫ p)).unit.app M)) := by
    refine reflect_homology_iso Λ _ 0 fun Ω _ _ x ↦ ?_
    have : HasInvertibleExponent Λ (Spec (.of Ω)) := .of_hom x
    let j' := (multiplicativeGroupModel Ω).ι
    have hj' := range_multiplicativeGroupModel_ι Ω
    have : HasInvertibleExponent Λ (multiplicativeGroupModel Ω) := .of_hom j'
    have hΩ := isIso_homology_zero_unit_tateObject_multiplicativeGroup
      Λ (𝟙 (Spec (.of Ω))) j' hj'
    exact (unit_homology_exchange Λ
      (AffineSpace.isPullback_complementMap_over x j j' hj hj').toCommSq
      (multiplicative_point_exchange Λ aB x j hj j' hj') 0).2 hΩ
  have hvan : ∀ n : ℤ, 2 ≤ n → IsZero ((H n).obj
      ((R((j ≫ p)_*[ModuleCat.{u + 1} Λ])).obj (tateObject Λ G 1))) := by
    intro n hn
    refine reflect_homology_zero Λ _ n fun Ω _ _ x ↦ ?_
    have : HasInvertibleExponent Λ (Spec (.of Ω)) := .of_hom x
    let j' := (multiplicativeGroupModel Ω).ι
    have hj' := range_multiplicativeGroupModel_ι Ω
    have : HasInvertibleExponent Λ (multiplicativeGroupModel Ω) := .of_hom j'
    let q := AffineSpace.complementMap x j j' hj hj'
    have hex := multiplicative_point_exchange Λ aB x j hj j' hj'
    exact (isZero_homology_rightDerivedLowerStar_tateObject_multiplicativeGroup
      Λ (𝟙 (Spec (.of Ω))) j' hj' n (by omega) (by omega)).of_iso
      ((_root_.DerivedCategory.homologyFunctor _ n).mapIso
        (asIso ((derivedBaseChangeMap (ModuleCat.{u + 1} Λ)
          (AffineSpace.isPullback_complementMap_over x j j' hj hj').toCommSq).app
            (tateObject Λ G 1)) ≪≫
          (R((j' ≫ 𝔸(ULift.{u} (Fin 1); Spec (.of Ω)) ↘ Spec (.of Ω))_*[
            ModuleCat.{u + 1} Λ])).mapIso (leftDerivedUpperStarTateObjectIso q 1)))
  let θp := leftDerivedUpperStarConstantComplexIso Λ p
  let θj := leftDerivedUpperStarConstantComplexIso Λ j
  let tU := leftDerivedUpperStarTateObjectIso (Λ := Λ) j 1
  let κU := kummerClass Λ (X.basicOpenUnit (AffineSpace.coord B (ULift.up 0)))
  let α := θj.hom ≫ κU ≫ tU.inv⟦(1 : ℤ)⟧'
  let Ψ₁ := (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) p).homEquiv _ _
    (θp.hom ≫ (derivedUpperStarLowerStarAdjunction
      (ModuleCat.{u + 1} Λ) j).homEquiv _ _ α)
  have hgen : IsIso ((H 0).map ((derivedUpperStarLowerStarAdjunction
      (ModuleCat.{u + 1} Λ) (j ≫ p)).homEquiv _ _
        ((leftDerivedUpperStarConstantComplexIso Λ (j ≫ p)).hom ≫
          kummerClass Λ (AffineSpace.unitLineCoord j hj)))) := by
    refine reflect_homology_iso Λ _ 0 fun Ω _ _ x ↦ ?_
    have : HasInvertibleExponent Λ (Spec (.of Ω)) := .of_hom x
    let j' := (multiplicativeGroupModel Ω).ι
    have hj' := range_multiplicativeGroupModel_ι Ω
    have : HasInvertibleExponent Λ (multiplicativeGroupModel Ω) := .of_hom j'
    have hex := multiplicative_point_exchange Λ aB x j hj j' hj'
    exact (kummer_homology_exchange Λ
      (AffineSpace.isPullback_complementMap_over x j j' hj hj').toCommSq _ _
      (units_map_unitLineCoord x j hj j' hj' _
        (AffineSpace.complementMap_comp x j j' hj hj')) hex).2
      (isIso_homology_zero_kummerClassAdjoint Λ (𝟙 (Spec (.of Ω))) j' hj')
  have hΨ₁ : IsIso ((H 0).map Ψ₁) := by
    have hunit : X.basicOpenUnit (AffineSpace.coord B (ULift.up 0)) =
        AffineSpace.unitLineCoord j hj := Units.ext rfl
    let Bι : (L((j ≫ p)^*[ModuleCat.{u + 1} Λ])).obj (constantComplex Λ B) ≅
        constantComplex Λ G :=
      (leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ) j p (j ≫ p) rfl).app _ ≪≫
        Lj.mapIso θp ≪≫ θj
    have hBi : Bι = leftDerivedUpperStarConstantComplexIso Λ (j ≫ p) :=
      (leftDerivedUpperStarConstantComplexIso_comp Λ j p (j ≫ p) rfl).symm
    let c := (rightDerivedLowerStarCompHom (ModuleCat.{u + 1} Λ) j p (j ≫ p) rfl).app
      ((tateObject Λ G 1)⟦(1 : ℤ)⟧)
    have hc : IsIso c := by
      simp only [c]
      rw [← rightDerivedLowerStarComp_hom_comp_congr_hom]
      infer_instance
    let e := (leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ) j p (j ≫ p) rfl).hom
    have harg : e.app (constantComplex Λ B) ≫ Lj.map θp.hom ≫ α ≫
        tU.hom⟦(1 : ℤ)⟧' = Bι.hom ≫ kummerClass Λ (AffineSpace.unitLineCoord j hj) := by
      simp only [e, Bι, α, κU, hunit, Iso.trans_hom, Iso.app_hom,
        Functor.mapIso_hom, Category.assoc, ← Functor.map_comp, Iso.inv_hom_id]
      erw [CategoryTheory.Functor.map_id, Category.comp_id]
    exact iso_adjoint_composition
      (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) p)
      (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) j)
      (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) (j ≫ p))
      e θp.hom α (tU.hom⟦(1 : ℤ)⟧') (H 0) (by
        rw [harg, hBi]
        exact hgen)
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro n hn
    have : M.IsLE 0 := DerivedCategory.TStructure.t.isLE_of_iso
      (tateTwistObjectIsoSingleFunctor Λ B 1).symm 0
    have hz : IsZero ((H n).obj M) := _root_.DerivedCategory.isZero_of_isLE _ 0 n hn
    exact hz.of_iso ((H n).mapIso
      (Rp.mapIso tX.symm ≪≫ (asIso ((derivedUpperStarLowerStarAdjunction
        (ModuleCat.{u + 1} Λ) p).unit.app M)).symm))
  · have hc : IsIso ((rightDerivedLowerStarCompHom (ModuleCat.{u + 1} Λ) j p (j ≫ p) rfl).app
        (Lj.obj ((L((p)^*[ModuleCat.{u + 1} Λ])).obj M))) := by
      rw [← rightDerivedLowerStarComp_hom_comp_congr_hom]
      infer_instance
    have hu := congrArg (H 0).map (unit_comp_rightDerivedLowerStar_map_unit Λ p j M)
    simp only [Functor.map_comp] at hu
    have hb : IsIso ((H 0).map (Rp.map
        ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) j).unit.app
          ((L((p)^*[ModuleCat.{u + 1} Λ])).obj M)))) := by
      let a := (H 0).map ((derivedUpperStarLowerStarAdjunction
        (ModuleCat.{u + 1} Λ) p).unit.app M)
      let b := (H 0).map (Rp.map ((derivedUpperStarLowerStarAdjunction
        (ModuleCat.{u + 1} Λ) j).unit.app ((L((p)^*[ModuleCat.{u + 1} Λ])).obj M)))
      let c := (H 0).map ((rightDerivedLowerStarCompHom
        (ModuleCat.{u + 1} Λ) j p (j ≫ p) rfl).app
        (Lj.obj ((L((p)^*[ModuleCat.{u + 1} Λ])).obj M)))
      have h3 : IsIso (a ≫ b ≫ c) := by
        simp only [a, b, c]
        rw [hu]
        infer_instance
      have : IsIso (b ≫ c) := IsIso.of_isIso_comp_left a (b ≫ c)
      exact IsIso.of_isIso_comp_right b c
    have hnat := (derivedUpperStarLowerStarAdjunction
      (ModuleCat.{u + 1} Λ) j).unit.naturality tX.hom
    have hm : Rp.map ((derivedUpperStarLowerStarAdjunction
        (ModuleCat.{u + 1} Λ) j).unit.app (tateObject Λ X 1)) =
        Rp.map tX.inv ≫ Rp.map ((derivedUpperStarLowerStarAdjunction
          (ModuleCat.{u + 1} Λ) j).unit.app ((L((p)^*[ModuleCat.{u + 1} Λ])).obj M)) ≫
        Rp.map ((Lj ⋙ Rj).map tX.hom) := by
      rw [← Functor.map_comp, ← Functor.map_comp, ← hnat]
      simp
    rw [hm, Functor.map_comp, Functor.map_comp]
    infer_instance
  · have hκ : kummerClassAffineLineDirectImage Λ B = Ψ₁ ≫
        Rp.map ((Rj.commShiftIso (1 : ℤ)).hom.app _) ≫
        (Rp.commShiftIso (1 : ℤ)).hom.app _ := by
      exact kummer_direct_image_formula Λ B
    have hiso : IsIso ((H 0).map (kummerClassAffineLineDirectImage Λ B)) := by
      rw [hκ, Functor.map_comp, Functor.map_comp]
      infer_instance
    have : IsIso (((H 0).shift (0 : ℤ)).map
        (kummerClassAffineLineDirectImage Λ B)) :=
      (NatIso.isIso_map_iff ((H 0).isoShiftZero ℤ) _).2 hiso
    rw [Functor.shiftMap]
    infer_instance
  · intro n hn
    exact (hvan n hn).of_iso ((H n).mapIso
      ((rightDerivedLowerStarComp (ModuleCat.{u + 1} Λ) j p).app (Lj.obj
        (tateObject Λ X 1)) ≪≫ (R((j ≫ p)_*[ModuleCat.{u + 1} Λ])).mapIso tU))

include aB in
/-- Blueprint `sk-prop-a1-kummer`: The affine line and `𝔾ₘ` with `Λ(1)`-coefficients

*(a), twisted.* For the projection `p : 𝔸¹_B ⟶ B`, `R^m p_* Λ(1) = 0` for `m > 0`: the affine
line is acyclic, and `Λ(1)` is pulled back from `B`, so by the projection formula the twisted
statement follows from `Rp_* Λ ≅ Λ_B`. -/
theorem isZero_homology_rightDerivedLowerStar_tateObject_affineLine_of_pos (n : ℤ) (hn : 0 < n) :
    IsZero ((_root_.DerivedCategory.homologyFunctor _ n).obj
      ((R((𝔸(ULift.{u} (Fin 1); B) ↘ B)_*[ModuleCat.{u + 1} Λ])).obj
        (tateObject Λ 𝔸(ULift.{u} (Fin 1); B) 1))) :=
  (affineLine_multiplicativeGroup_homology_tateObject Λ B aB).1 n hn

include aB in
/-- Blueprint `sk-prop-a1-kummer`: The affine line and `𝔾ₘ` with `Λ(1)`-coefficients

*(b), degree zero.* For the open complement `j : 𝔾_{m,B} ⟶ 𝔸¹_B` of the zero section, the
restriction `R⁰p_* Λ(1) ⟶ R⁰π_* Λ(1)` is an isomorphism (`p^*` is an isomorphism onto
`R⁰π_* Λ(1) ≅ Λ_B(1)`). -/
theorem isIso_homology_zero_map_unit_multiplicativeGroup :
    IsIso ((_root_.DerivedCategory.homologyFunctor _ 0).map
      ((R((𝔸(ULift.{u} (Fin 1); B) ↘ B)_*[ModuleCat.{u + 1} Λ])).map
        ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ)
          ((𝔸(ULift.{u} (Fin 1); B).basicOpen (AffineSpace.coord B (ULift.up 0))).ι)).unit.app
            (tateObject Λ 𝔸(ULift.{u} (Fin 1); B) 1)))) :=
  (affineLine_multiplicativeGroup_homology_tateObject Λ B aB).2.1

include aB in
/-- Blueprint `sk-prop-a1-kummer`: The affine line and `𝔾ₘ` with `Λ(1)`-coefficients

*(b), degree one: the Kummer generator.* `R¹π_* Λ(1)` is free of rank one on the Kummer class
`κ(t)` of the coordinate: the section `κ(t) : Λ_B ⟶ (Rπ_* Λ(1))[1]`
(`AlgebraicGeometry.Etale.kummerClassAffineLineDirectImage`) induces an isomorphism
`Λ_B ≅ R¹π_* Λ(1)`, `1 ↦ κ(t)`. -/
theorem isIso_shiftMap_kummerClassAffineLineDirectImage :
    IsIso ((_root_.DerivedCategory.homologyFunctor _ 0).shiftMap
      (kummerClassAffineLineDirectImage Λ B) 0 1 (by norm_num)) :=
  (affineLine_multiplicativeGroup_homology_tateObject Λ B aB).2.2.1

include aB in
/-- Blueprint `sk-prop-a1-kummer`: The affine line and `𝔾ₘ` with `Λ(1)`-coefficients

*(c).* `R^m π_* Λ(1) = 0` for `m ≥ 2`, by the cohomological dimension of affine curves over an
algebraically closed field. -/
theorem isZero_homology_rightDerivedLowerStar_tateObject_basicOpen_of_two_le
    (n : ℤ) (hn : 2 ≤ n) :
    IsZero ((_root_.DerivedCategory.homologyFunctor _ n).obj
      ((R((𝔸(ULift.{u} (Fin 1); B) ↘ B)_*[ModuleCat.{u + 1} Λ])).obj
        ((R(((𝔸(ULift.{u} (Fin 1); B).basicOpen (AffineSpace.coord B (ULift.up 0))).ι)_*[
            ModuleCat.{u + 1} Λ])).obj
          ((L(((𝔸(ULift.{u} (Fin 1); B).basicOpen (AffineSpace.coord B (ULift.up 0))).ι)^*[
            ModuleCat.{u + 1} Λ])).obj (tateObject Λ 𝔸(ULift.{u} (Fin 1); B) 1))))) :=
  (affineLine_multiplicativeGroup_homology_tateObject Λ B aB).2.2.2 n hn

omit [Finite Λ] in
/-- The Tate twist `Λ_X(m)` is concentrated in degree zero, so it lies in `D^{≥ 0}`. -/
instance isGE_tateObject (X : Scheme.{u}) [HasInvertibleExponent Λ X] (m : ℤ) :
    (tateObject Λ X m).IsGE 0 :=
  DerivedCategory.TStructure.t.isGE_of_iso (tateTwistObjectIsoSingleFunctor Λ X m).symm 0

include aB in
/-- Blueprint `sk-prop-a1-kummer`: The affine line and `𝔾ₘ` with `Λ(1)`-coefficients

`Rp_* Λ(1)` has cohomology only in degree zero. -/
theorem isZero_homology_rightDerivedLowerStar_tateObject_affineLine (n : ℤ) (hn : n ≠ 0) :
    IsZero ((_root_.DerivedCategory.homologyFunctor _ n).obj
      ((R((𝔸(ULift.{u} (Fin 1); B) ↘ B)_*[ModuleCat.{u + 1} Λ])).obj
        (tateObject Λ 𝔸(ULift.{u} (Fin 1); B) 1))) := by
  rcases lt_or_gt_of_ne hn with hn | hn
  · have := isGE_rightDerivedLowerStar_obj Λ (𝔸(ULift.{u} (Fin 1); B) ↘ B)
      (tateObject Λ 𝔸(ULift.{u} (Fin 1); B) 1) 0
    exact _root_.DerivedCategory.isZero_of_isGE _ 0 n hn
  · exact isZero_homology_rightDerivedLowerStar_tateObject_affineLine_of_pos Λ B aB n hn

include aB in
/-- Blueprint `sk-prop-a1-kummer`: The affine line and `𝔾ₘ` with `Λ(1)`-coefficients

`Rπ_* Λ(1)` has cohomology only in degrees zero and one. -/
theorem isZero_homology_rightDerivedLowerStar_tateObject_basicOpen (n : ℤ)
    (hn₀ : n ≠ 0) (hn₁ : n ≠ 1) :
    IsZero ((_root_.DerivedCategory.homologyFunctor _ n).obj
      ((R((𝔸(ULift.{u} (Fin 1); B) ↘ B)_*[ModuleCat.{u + 1} Λ])).obj
        ((R(((𝔸(ULift.{u} (Fin 1); B).basicOpen (AffineSpace.coord B (ULift.up 0))).ι)_*[
            ModuleCat.{u + 1} Λ])).obj
          ((L(((𝔸(ULift.{u} (Fin 1); B).basicOpen (AffineSpace.coord B (ULift.up 0))).ι)^*[
            ModuleCat.{u + 1} Λ])).obj (tateObject Λ 𝔸(ULift.{u} (Fin 1); B) 1))))) := by
  rcases lt_or_gt_of_ne hn₀ with hn | hn
  · let j := (𝔸(ULift.{u} (Fin 1); B).basicOpen (AffineSpace.coord B (ULift.up.{u} (0 : Fin 1)))).ι
    have : ((L((j)^*[ModuleCat.{u + 1} Λ])).obj (tateObject Λ 𝔸(ULift.{u} (Fin 1); B) 1)).IsGE 0 :=
      DerivedCategory.TStructure.t.isGE_of_iso (leftDerivedUpperStarTateObjectIso j 1).symm 0
    have := isGE_rightDerivedLowerStar_obj Λ j
      ((L((j)^*[ModuleCat.{u + 1} Λ])).obj (tateObject Λ 𝔸(ULift.{u} (Fin 1); B) 1)) 0
    have := isGE_rightDerivedLowerStar_obj Λ (𝔸(ULift.{u} (Fin 1); B) ↘ B)
      ((R((j)_*[ModuleCat.{u + 1} Λ])).obj
        ((L((j)^*[ModuleCat.{u + 1} Λ])).obj (tateObject Λ 𝔸(ULift.{u} (Fin 1); B) 1))) 0
    exact _root_.DerivedCategory.isZero_of_isGE _ 0 n hn
  · exact isZero_homology_rightDerivedLowerStar_tateObject_basicOpen_of_two_le
      Λ B aB n (by lia)

end Etale

end AlgebraicGeometry
