/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF groups NP, H3
-/
module

public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.SixFunctors.BaseChange.DerivedUnbounded
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Data.ZMod.Basic
import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.Deligne
import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison
import Mathlib.Algebra.CharP.Basic
import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Mates

/-!
# Generic bounded constructibility for an open immersion

Source: literature/blueprint/master/blueprint/sec-smooth-purity/sk-prop-sf-cbc/
`thm-fin-deligne-generic-open.md` (blueprint: thm-fin-deligne-generic-open).

Base changes are expressed using arbitrary Cartesian presentations. The two pullback
squares over `U` present `Y_U` and `X_U`; the two squares over `T` present `Y_T` and `X_T`.
The coefficient ring is the canonical universe lift of the prime field.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private theorem square_horiz
    (Λ : Type (u + 1)) [CommRing Λ]
    {X XU XT Y YU YT : Scheme.{u}}
    {pX : XU ⟶ X} {jU : XU ⟶ YU} {j : X ⟶ Y} {pY : YU ⟶ Y}
    {qX : XT ⟶ XU} {jT : XT ⟶ YT} {qY : YT ⟶ YU}
    (s₁ : CommSq pX jU j pY) (s₂ : CommSq qX jT jU qY)
    (K : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (derivedSquareUpperStarIso (ModuleCat.{u + 1} Λ) (s₂.horiz_comp s₁)).hom.app K ≫
        (leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ) qX pX).hom.app
          ((L((j)^*[ModuleCat.{u + 1} Λ])).obj K) =
      (L((jT)^*[ModuleCat.{u + 1} Λ])).map
          ((leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ) qY pY).hom.app K) ≫
        (derivedSquareUpperStarIso (ModuleCat.{u + 1} Λ) s₂).hom.app
          ((L((pY)^*[ModuleCat.{u + 1} Λ])).obj K) ≫
        (L((qX)^*[ModuleCat.{u + 1} Λ])).map
          ((derivedSquareUpperStarIso (ModuleCat.{u + 1} Λ) s₁).hom.app K) := by
  have h₁ := leftDerivedUpperStarComp_assoc'_app (ModuleCat.{u + 1} Λ) qX pX j (qX ≫ pX) (pX ≫ j)
    ((qX ≫ pX) ≫ j) rfl rfl rfl K
  have h₂ := leftDerivedUpperStarComp_assoc'_app (ModuleCat.{u + 1} Λ) qX jU pY (qX ≫ jU) (pX ≫ j)
    ((qX ≫ pX) ≫ j) rfl s₁.w (by simp only [Category.assoc, s₁.w]) K
  have h₃ := leftDerivedUpperStarComp_assoc'_app (ModuleCat.{u + 1} Λ) jT qY pY (qX ≫ jU) (qY ≫ pY)
    ((qX ≫ pX) ≫ j) s₂.w rfl (by simp only [Category.assoc, s₁.w]) K
  dsimp only [derivedSquareUpperStarIso, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app]
  rw [← cancel_epi ((leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ) jT (qY ≫ pY)
    ((qX ≫ pX) ≫ j) (s₂.horiz_comp s₁).w).hom.app K)]
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc]
  rw [← h₁, reassoc_of% h₃]
  simp only [Iso.hom_inv_id_app_assoc, Functor.map_comp]
  rw [← reassoc_of% h₂, ← Functor.map_comp_assoc, Iso.hom_inv_id_app,
    CategoryTheory.Functor.map_id, Category.id_comp]

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private theorem exchange_horiz
    (Λ : Type (u + 1)) [CommRing Λ]
    {X XU XT Y YU YT : Scheme.{u}}
    {pX : XU ⟶ X} {jU : XU ⟶ YU} {j : X ⟶ Y} {pY : YU ⟶ Y}
    {qX : XT ⟶ XU} {jT : XT ⟶ YT} {qY : YT ⟶ YU}
    (s₁ : CommSq pX jU j pY) (s₂ : CommSq qX jT jU qY)
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (L((qY)^*[ModuleCat.{u + 1} Λ])).map
        ((derivedBaseChangeMap (ModuleCat.{u + 1} Λ) s₁).app K) ≫
      (derivedBaseChangeMap (ModuleCat.{u + 1} Λ) s₂).app
        ((L((pX)^*[ModuleCat.{u + 1} Λ])).obj K) =
    (leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ) qY pY).inv.app
        ((R((j)_*[ModuleCat.{u + 1} Λ])).obj K) ≫
      (derivedBaseChangeMap (ModuleCat.{u + 1} Λ) (s₂.horiz_comp s₁)).app K ≫
      (R((jT)_*[ModuleCat.{u + 1} Λ])).map
        ((leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ) qX pX).hom.app K) := by
  let A := ModuleCat.{u + 1} Λ
  let a := derivedUpperStarLowerStarAdjunction A j
  let b := derivedUpperStarLowerStarAdjunction A jU
  let c := derivedUpperStarLowerStarAdjunction A jT
  let α := TwoSquare.mk _ _ _ _ (derivedSquareUpperStarIso A s₁).hom
  let β := TwoSquare.mk _ _ _ _ (derivedSquareUpperStarIso A s₂).hom
  let γ := TwoSquare.mk _ _ _ _ (derivedSquareUpperStarIso A (s₂.horiz_comp s₁)).hom
  have heq : TwoSquare.hComp α β =
      (γ.whiskerTop (leftDerivedUpperStarComp A qY pY).inv).whiskerBottom
        (leftDerivedUpperStarComp A qX pX).hom := by
    ext M
    dsimp only [TwoSquare.hComp, TwoSquare.whiskerTop, TwoSquare.whiskerBottom,
      TwoSquare.mk, TwoSquare.natTrans, α, β, γ]
    simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
      Functor.associator_hom_app, Functor.associator_inv_app, Category.id_comp,
      Category.comp_id]
    rw [← cancel_epi ((L((jT)^*[A])).map
      ((leftDerivedUpperStarComp A qY pY).hom.app M))]
    simpa only [Category.assoc, ← Functor.map_comp_assoc, Iso.hom_inv_id_app,
      CategoryTheory.Functor.map_id, Category.id_comp, A] using (square_horiz Λ s₁ s₂ M).symm
  have hm := congrArg (fun z ↦ (mateEquiv a c z).app K) heq
  rw [mateEquiv_vcomp a b c, mateEquiv_whiskerTop_whiskerBottom] at hm
  simpa only [TwoSquare.vComp_app, TwoSquare.whiskerRight, TwoSquare.whiskerLeft,
    NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app, Category.assoc,
    derivedBaseChangeMap, derivedBaseChangeSquare, α, β, γ, a, b, c, A] using hm

private theorem boundedConstructible_to_explicit
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] (Y : Scheme.{u})
    (K : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (h : DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) Y K) :
    DerivedCategory.isBoundedConstructible Λ Y K := by
  obtain ⟨⟨⟨a, ha⟩, ⟨b, hb⟩⟩, hc⟩ := h
  have : K.IsGE a := ha
  have : K.IsLE b := hb
  refine ⟨fun i ↦ (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).2
    (hc i), a, max a b, le_max_left _ _, ?_⟩
  intro i hi
  rcases hi with hi | hi
  · exact _root_.DerivedCategory.isZero_of_isGE K a i hi
  · exact _root_.DerivedCategory.isZero_of_isLE K b i ((le_max_right a b).trans_lt hi)

/-- Generic bounded constructibility and universal Noetherian base change for an open
immersion and a constructible prime-field sheaf.
Source: blueprint `sec-smooth-purity/sk-prop-sf-cbc/thm-fin-deligne-generic-open.md`
(blueprint: thm-fin-deligne-generic-open).

Proof:
1. The prime l is a nonzero element of k, hence is invertible on Spec k and S.
   Convert finite-constant-value constructibility to the source library's equivalent
   constructibility predicate on the same sheaf and the same stratifications.
2. Apply the existing source theorem `exists_hasConstructibleDirectImageBaseChangeOn`.
   Its nonempty open U satisfies the assertion for every Noetherian scheme mapping
   into U. Finite type over k makes S Noetherian; its open subscheme U is Noetherian.
   Apply the source assertion to U itself and the given Cartesian presentation.
   Convert its t-structure bounds to a homology support interval [a, max a b], and
   convert constructibility back in each degree.
3. For a Noetherian T over U, apply the source assertion to T -> U -> S and the
   horizontally pasted Cartesian squares. The source theorem supplies invertible
   exchanges for both the square over U and the outer square over S.
4. Associativity of the canonical derived pullback composition isomorphisms proves
   horizontal pasting of the derived square comparisons. The mates correspondence
   carries this equality to horizontal pasting of the actual exchanges. In this
   factorization all composition comparisons and the exchange over U are invertible.
   Cancel them to obtain invertibility of the requested exchange over T -> U.

The geometric source theorem is an existing admitted declaration, reused here without
adding another geometric obligation. This proof establishes the conversion between its
formulation and the present one, including equality of the specified exchange maps.
-/
theorem exists_nonempty_open_isBoundedConstructible_derived_open_pushforward
    (k : Type u) [Field k] (S : Scheme.{u}) [IsIntegral S]
    (aS : S ⟶ Spec (.of k)) [LocallyOfFiniteType aS] [QuasiCompact aS]
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : ℓ ≠ ringChar k)
    (X Y : Scheme.{u}) (aX : X ⟶ S) (aY : Y ⟶ S)
    [LocallyOfFiniteType aX] [QuasiCompact aX]
    [LocallyOfFiniteType aY] [QuasiCompact aY]
    (j : X ⟶ Y) [IsOpenImmersion j] (hj : j ≫ aY = aX)
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))))
    (hF : Scheme.IsConstructibleEtaleModuleSheaf F) :
    ∃ U : S.Opens, Nonempty U ∧
      ∀ (XU YU : Scheme.{u}) (pX : XU ⟶ X) (pY : YU ⟶ Y)
        (bU : YU ⟶ U.toScheme) (jU : XU ⟶ YU),
        IsPullback pY bU aY U.ι →
        IsPullback pX jU j pY →
        DerivedCategory.isBoundedConstructible (ULift.{u + 1} (ZMod ℓ)) YU
          ((R((jU)_*[ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))])).obj
            ((L((pX)^*[ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))])).obj
              ((_root_.DerivedCategory.singleFunctor _ 0).obj F))) ∧
        ∀ (T : Scheme.{u}) [IsNoetherian T] (t : T ⟶ U.toScheme)
          (XT YT : Scheme.{u}) (qX : XT ⟶ XU) (qY : YT ⟶ YU)
          (bT : YT ⟶ T) (jT : XT ⟶ YT),
          IsPullback qY bT bU t →
          ∀ sq : IsPullback qX jT jU qY,
            IsIso ((derivedBaseChangeMap
              (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))) sq.toCommSq).app
                ((L((pX)^*[ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))])).obj
                  ((_root_.DerivedCategory.singleFunctor _ 0).obj F))) := by
  subst aX
  have hprime : ℓ.Prime := Fact.out
  have hchar : (ℓ : k) ≠ 0 :=
    CharP.cast_ne_zero_of_ne_of_prime k hprime hℓ.symm
  have : HasInvertibleExponent (ULift.{u + 1} (ZMod ℓ)) (Spec (.of k)) := by
    refine ⟨ℓ, hprime.pos, ?_, ?_⟩
    · exact CharP.cast_eq_zero _ ℓ
    · simpa using hchar.isUnit.map (Scheme.ΓSpecIso (.of k)).inv.hom
  have : HasInvertibleExponent (ULift.{u + 1} (ZMod ℓ)) S :=
    HasInvertibleExponent.of_hom aS
  have : Scheme.IsConstructibleSheaf F :=
    (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf F).1 hF
  obtain ⟨U, hU, h⟩ := exists_hasConstructibleDirectImageBaseChangeOn
    (ULift.{u + 1} (ZMod ℓ)) aS aY j F
  refine ⟨U, ⟨hU.choose, hU.choose_spec⟩, ?_⟩
  intro XU YU pX pY bU jU hY hX
  have : IsLocallyNoetherian S := LocallyOfFiniteType.isLocallyNoetherian aS
  have : CompactSpace S := QuasiCompact.compactSpace_of_compactSpace aS
  have : IsNoetherian S := ⟨⟩
  have : TopologicalSpace.NoetherianSpace U.toScheme :=
    U.ι.isOpenEmbedding.isInducing.noetherianSpace
  have : CompactSpace U.toScheme := TopologicalSpace.NoetherianSpace.compactSpace _
  have : IsNoetherian U.toScheme := ⟨⟩
  have hUr : Set.range U.ι ⊆ (U : Set S) := by
    rintro _ ⟨x, rfl⟩
    exact x.property
  have hg := h U.toScheme U.ι hUr YU XU pY bU pX jU hY hX
  refine ⟨boundedConstructible_to_explicit _ _ _ hg.1, ?_⟩
  intro T inst t XT YT qX qY bT jT hTY sq
  have htU : Set.range (t ≫ U.ι) ⊆ (U : Set S) := by
    rintro _ ⟨x, rfl⟩
    exact (t x).property
  have htotal := (h T (t ≫ U.ι) htU YT XT (qY ≫ pY) bT (qX ≫ pX) jT
    (hTY.paste_horiz hY) (sq.paste_horiz hX)).2
  let A := ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))
  let K := (_root_.DerivedCategory.singleFunctor _ 0).obj F
  have : IsIso ((derivedBaseChangeMap A hX.toCommSq).app K) := hg.2
  have : IsIso ((derivedBaseChangeMap A (sq.paste_horiz hX).toCommSq).app K) := htotal
  have : IsIso ((L((qY)^*[A])).map
      ((derivedBaseChangeMap A hX.toCommSq).app K) ≫
      (derivedBaseChangeMap A sq.toCommSq).app ((L((pX)^*[A])).obj K)) := by
    rw [exchange_horiz]
    infer_instance
  exact IsIso.of_isIso_comp_left
    ((L((qY)^*[A])).map ((derivedBaseChangeMap A hX.toCommSq).app K)) _

end AlgebraicGeometry.Etale
