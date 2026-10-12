/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusBaseChangeComp
public import WeilConjectures.SixFunctors.BaseChange.DerivedComparison
public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.HigherDirectImage
public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.RestrictScalars

/-!
# The coefficients of the smooth base change theorem

The smooth base change theorem is stated for a sheaf `F` of `Λ`-modules whose geometric stalks
are torsion of orders invertible on the base, while the base-change property
`AlgebraicGeometry.Etale.BaseChangeProperty` is indexed by a fixed coefficient ring. This file
contains the passage between the two.

- In negative degrees both sides of the base-change map vanish, the pullbacks being exact and
  the derived pushforwards preserving complexes concentrated in nonnegative degrees.
- *Filtered torsion*: `F` is the filtered colimit of subsheaves killed by integers `n`
  invertible on `S`
  (`AlgebraicGeometry.Scheme.IsTorsionSheafOfInvertibleOrder.exists_isColimit`); the source
  `p⁻¹ R^q g_*` and the target `R^q h_* e⁻¹` of the base-change map commute with filtered
  colimits (`AlgebraicGeometry.Etale.preservesColimitsOfShape_higherDirectImage`, and `p⁻¹`,
  `e⁻¹` are left adjoints), so it suffices to treat sheaves killed by one such `n`.
- *Change of rings*: a sheaf of `Λ`-modules killed by `n` is a sheaf of `Λ/nΛ`-modules, and
  its base-change map is the one computed over `Λ/nΛ`, so the base-change property over the
  ring `Λ/nΛ`, in which `n = 0`, applies to it.

## Main statements

- `AlgebraicGeometry.Etale.isZero_baseChangeSourceFunctor_obj_of_neg`,
  `AlgebraicGeometry.Etale.isZero_baseChangeTargetFunctor_obj_of_neg`: vanishing in negative
  degrees.
- `AlgebraicGeometry.Etale.baseChangeProperty_of_neg` and
  `AlgebraicGeometry.Etale.universalBaseChangeProperty_of_neg`: the base-change property, and
  its universal form, in negative degrees.
- `AlgebraicGeometry.Etale.isIso_baseChangeHomologyMap_of_forall_nsmul_eq_zero`: reduction to
  sheaves killed by an integer invertible on `S`.
- `AlgebraicGeometry.Etale.isIso_baseChangeHomologyMap_of_nsmul_eq_zero`: the change of rings
  `Λ ↝ Λ/nΛ`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor AlgebraicGeometry.Etale

namespace AlgebraicGeometry

variable (Λ : Type (u + 1)) [CommRing Λ]
  {X S T Y : Scheme.{u}} {p : X ⟶ S} {g : T ⟶ S} {e : Y ⟶ T} {h : Y ⟶ X}

section Identification

/-- The source `F ↦ H^q(p^*(R g_* F[0]))` of the base-change map is `p^*` of the higher direct
image functor `F ↦ R^q g_* F`, the pullback `p^*` being exact. -/
noncomputable def Etale.baseChangeSourceFunctorIso (p : X ⟶ S) (g : T ⟶ S) (q : ℤ) :
    Etale.baseChangeSourceFunctor Λ p g q ≅
      (DerivedCategory.Plus.singleFunctor _ 0 ⋙ R+((g)_*[ModuleCat.{u + 1} Λ]) ⋙
        DerivedCategory.Plus.homologyFunctor _ q) ⋙ (p)^*[ModuleCat.{u + 1} Λ] :=
  Functor.isoWhiskerLeft (DerivedCategory.Plus.singleFunctor _ 0)
    (Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft R+((g)_*[ModuleCat.{u + 1} Λ])
      (((p)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlusHomologyFunctorIso q).symm ≪≫
      (Functor.associator _ _ _).symm) ≪≫
    (Functor.associator _ _ _).symm

/-- The target `F ↦ H^q(R h_*(e^*(F[0])))` of the base-change map is the higher direct image
functor `F ↦ R^q h_* F` precomposed with `e^*`, the pullback `e^*` being exact. -/
noncomputable def Etale.baseChangeTargetFunctorIso (e : Y ⟶ T) (h : Y ⟶ X) (q : ℤ) :
    Etale.baseChangeTargetFunctor Λ e h q ≅
      (e)^*[ModuleCat.{u + 1} Λ] ⋙ (DerivedCategory.Plus.singleFunctor _ 0 ⋙
        R+((h)_*[ModuleCat.{u + 1} Λ]) ⋙ DerivedCategory.Plus.homologyFunctor _ q) :=
  Functor.isoWhiskerLeft (DerivedCategory.Plus.singleFunctor _ 0)
      (Functor.associator _ _ _) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (((e)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlusSingleFunctor 0)
      (R+((h)_*[ModuleCat.{u + 1} Λ]) ⋙ DerivedCategory.Plus.homologyFunctor _ q) ≪≫
    Functor.associator _ _ _

/-- The source `p⁻¹ R^q g_* F` of the base-change map vanishes in negative degrees. -/
lemma Etale.isZero_baseChangeSourceFunctor_obj_of_neg (p : X ⟶ S) (g : T ⟶ S) {q : ℤ}
    (hq : q < 0) (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    IsZero ((Etale.baseChangeSourceFunctor Λ p g q).obj F) :=
  IsZero.of_iso (((p)^*[ModuleCat.{u + 1} Λ]).map_isZero
    (Functor.isZero_homologyFunctor_rightDerivedFunctorPlus_obj_of_isGE _ _ 0 hq))
    ((Etale.baseChangeSourceFunctorIso Λ p g q).app F)

/-- The target `R^q h_* e⁻¹ F` of the base-change map vanishes in negative degrees. -/
lemma Etale.isZero_baseChangeTargetFunctor_obj_of_neg (e : Y ⟶ T) (h : Y ⟶ X) {q : ℤ}
    (hq : q < 0) (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    IsZero ((Etale.baseChangeTargetFunctor Λ e h q).obj F) :=
  IsZero.of_iso (Functor.isZero_homologyFunctor_rightDerivedFunctorPlus_obj_of_isGE _ _ 0 hq)
    ((Etale.baseChangeTargetFunctorIso Λ e h q).app F)

/-- In negative degrees the base-change map is an isomorphism between zero objects. -/
lemma Etale.isIso_baseChangeHomologyMap_of_neg (sq : IsPullback e h g p) {q : ℤ} (hq : q < 0)
    (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    IsIso (Etale.baseChangeHomologyMap Λ sq q F) :=
  ⟨0, (Etale.isZero_baseChangeSourceFunctor_obj_of_neg Λ p g hq F).eq_of_src _ _,
    (Etale.isZero_baseChangeTargetFunctor_obj_of_neg Λ e h hq F).eq_of_src _ _⟩

/-- The base-change property holds in negative degrees for every morphism `p`: the derived
pushforward of a sheaf placed in degree `0` has no cohomology in negative degrees, so both
`p⁻¹ R^q g_* F` and `R^q h_* e⁻¹ F` vanish for `q < 0`
(`AlgebraicGeometry.Etale.isIso_baseChangeHomologyMap_of_neg`). -/
theorem Etale.baseChangeProperty_of_neg (p : X ⟶ S) {q : ℤ} (hq : q < 0) :
    Etale.BaseChangeProperty Λ p q := by
  intro T Y g e h _ _ sq F
  exact Etale.isIso_baseChangeHomologyMap_of_neg Λ sq hq F

/-- The base-change property holds universally in negative degrees, by
`AlgebraicGeometry.Etale.baseChangeProperty_of_neg` applied to every base change of `p`. -/
theorem Etale.universalBaseChangeProperty_of_neg (p : X ⟶ S) {q : ℤ} (hq : q < 0) :
    Etale.UniversalBaseChangeProperty Λ p q :=
  fun _ _ _ _ p' _ ↦ Etale.baseChangeProperty_of_neg Λ p' hq

end Identification

section ChangeOfRings

/-- The derived base-change morphism is the base change morphism of the right derived functor
`R g_*` along the exact functors `p^*` and `e^*`, attached to the underived base-change map. -/
lemma Etale.baseChange_eq_rightDerivedFunctorPlusBaseChange (sq : CommSq e h g p) :
    Etale.baseChange (ModuleCat.{u + 1} Λ) sq =
      Functor.rightDerivedFunctorPlusBaseChange
        (Etale.baseChangeMap (ModuleCat.{u + 1} Λ) sq) := by
  rw [Etale.baseChange_eq_derivedBaseChangeMapPlus]
  exact (Etale.derivedBaseChangeMapPlus_ext _ sq _
    (fun K ↦ Functor.rightDerivedFunctorPlusBaseChange_fac_app _ K)).symm

/-- If `a ≫ f = g ≫ b` with `a` and `b` isomorphisms, then `f` is an isomorphism as soon as
`g` is. -/
lemma Etale.isIso_of_comm {C : Type*} [Category C] {A B A' B' : C} {f : A ⟶ B} {g : A' ⟶ B'}
    (a : A' ⟶ A) (b : B' ⟶ B) [IsIso a] [IsIso b] (w : a ≫ f = g ≫ b) [IsIso g] : IsIso f := by
  have : IsIso (a ≫ f) := by rw [w]; infer_instance
  exact IsIso.of_isIso_comp_left a f

variable {Λ} {Λ' : Type (u + 1)} [CommRing Λ'] (φ : Λ →+* Λ')

/-- Restriction of scalars along `φ : Λ →+* Λ'` and the derived base-change morphism: if the
degree-`q` homology of the base-change morphism over `Λ'` is an isomorphism at a complex `K`,
then so is the degree-`q` homology of the base-change morphism over `Λ` at the restriction of
scalars of `K`. Restriction of scalars commutes with `p^*`, `e^*`
(`AlgebraicGeometry.Etale.upperStarRestrictScalars`), with the derived direct images
(`AlgebraicGeometry.Etale.rightDerivedLowerStarRestrictScalars`) and with the underived
base-change map (`AlgebraicGeometry.Etale.baseChangeMap_restrictScalars`); the pasting and
naturality laws of the base change morphisms of right derived functors identify the two
derived base-change morphisms up to these isomorphisms. -/
lemma Etale.isIso_homologyMap_baseChange_restrictScalars (sq : IsPullback e h g p) (q : ℤ)
    (K : DerivedCategory.Plus (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ')))
    (hK : IsIso ((DerivedCategory.Plus.homologyFunctor _ q).map
      ((Etale.baseChange (ModuleCat.{u + 1} Λ') sq.toCommSq).app K))) :
    IsIso ((DerivedCategory.Plus.homologyFunctor _ q).map
      ((Etale.baseChange (ModuleCat.{u + 1} Λ) sq.toCommSq).app
        ((Sheaf.restrictScalars T.smallEtaleTopology φ).mapDerivedCategoryPlus.obj K))) := by
  rw [Etale.baseChange_eq_rightDerivedFunctorPlusBaseChange] at hK ⊢
  let H := DerivedCategory.Plus.homologyFunctor (Sheaf X.smallEtaleTopology
    (ModuleCat.{u + 1} Λ)) q
  have hA := Functor.rightDerivedFunctorPlusBaseChange_paste
    (G₁ := (g)_*[ModuleCat.{u + 1} Λ']) (γ₁ := Sheaf.restrictScalars S.smallEtaleTopology φ)
    (β₁ := Sheaf.restrictScalars T.smallEtaleTopology φ) (G₂ := (g)_*[ModuleCat.{u + 1} Λ])
    (Iso.refl _).hom (Etale.baseChangeMap (ModuleCat.{u + 1} Λ) sq.toCommSq) K
  have hB := Functor.rightDerivedFunctorPlusBaseChange_paste
    (G₂ := (h)_*[ModuleCat.{u + 1} Λ']) (γ₂ := Sheaf.restrictScalars X.smallEtaleTopology φ)
    (β₂ := Sheaf.restrictScalars Y.smallEtaleTopology φ) (G₃ := (h)_*[ModuleCat.{u + 1} Λ])
    (Etale.baseChangeMap (ModuleCat.{u + 1} Λ') sq.toCommSq) (Iso.refl _).hom K
  have hN := Functor.rightDerivedFunctorPlusBaseChange_naturality
    (Functor.baseChangePaste (Iso.refl _).hom
      (Etale.baseChangeMap (ModuleCat.{u + 1} Λ) sq.toCommSq))
    (Functor.baseChangePaste (Etale.baseChangeMap (ModuleCat.{u + 1} Λ') sq.toCommSq)
      (Iso.refl _).hom)
    (asIso (Etale.upperStarRestrictScalars φ p).natTrans)
    (asIso (Etale.upperStarRestrictScalars φ e).natTrans) (by
      ext M : 2
      simp only [Functor.baseChangePaste, NatTrans.comp_app, Functor.whiskerRight_app,
        Functor.whiskerLeft_app, Functor.associator_hom_app, Functor.associator_inv_app,
        Iso.refl_hom, NatTrans.id_app, Functor.map_id, Category.id_comp, Category.comp_id,
        asIso_hom]
      exact Etale.baseChangeMap_restrictScalars φ sq.toCommSq M) K
  have hρg : IsIso (Functor.rightDerivedFunctorPlusBaseChange
      (G := (g)_*[ModuleCat.{u + 1} Λ']) (γ := Sheaf.restrictScalars S.smallEtaleTopology φ)
      (β := Sheaf.restrictScalars T.smallEtaleTopology φ) (G' := (g)_*[ModuleCat.{u + 1} Λ])
      (Iso.refl _).hom) :=
    Etale.isIso_rightDerivedLowerStarRestrictScalars φ g
  have hρh : IsIso (Functor.rightDerivedFunctorPlusBaseChange
      (G := (h)_*[ModuleCat.{u + 1} Λ']) (γ := Sheaf.restrictScalars X.smallEtaleTopology φ)
      (β := Sheaf.restrictScalars Y.smallEtaleTopology φ) (G' := (h)_*[ModuleCat.{u + 1} Λ])
      (Iso.refl _).hom) :=
    Etale.isIso_rightDerivedLowerStarRestrictScalars φ h
  -- the homology of `res (BC' K)`
  have h₁ : IsIso (H.map ((Sheaf.restrictScalars X.smallEtaleTopology φ).mapDerivedCategoryPlus.map
      ((Functor.rightDerivedFunctorPlusBaseChange
        (Etale.baseChangeMap (ModuleCat.{u + 1} Λ') sq.toCommSq)).app K))) := by
    have w := ((Sheaf.restrictScalars X.smallEtaleTopology φ).mapDerivedCategoryPlusHomologyFunctorIso
      q).hom.naturality ((Functor.rightDerivedFunctorPlusBaseChange
        (Etale.baseChangeMap (ModuleCat.{u + 1} Λ') sq.toCommSq)).app K)
    have : IsIso (((DerivedCategory.Plus.homologyFunctor _ q) ⋙
        Sheaf.restrictScalars X.smallEtaleTopology φ).map
        ((Functor.rightDerivedFunctorPlusBaseChange
          (Etale.baseChangeMap (ModuleCat.{u + 1} Λ') sq.toCommSq)).app K)) := by
      rw [Functor.comp_map]
      infer_instance
    exact Etale.isIso_of_comm _ _ w.symm
  -- the homology of the base change morphism of the second pasting
  have h₂ := congr_arg H.map hB
  simp only [Functor.map_comp] at h₂
  have : IsIso (H.map ((Functor.rightDerivedFunctorPlusBaseChange
      (Functor.baseChangePaste (Etale.baseChangeMap (ModuleCat.{u + 1} Λ') sq.toCommSq)
        (Iso.refl _).hom)).app K)) := by
    have : IsIso (H.map ((Functor.rightDerivedFunctorPlusBaseChange
        (Functor.baseChangePaste (Etale.baseChangeMap (ModuleCat.{u + 1} Λ') sq.toCommSq)
          (Iso.refl _).hom)).app K) ≫
        H.map (((h)_*[ModuleCat.{u + 1} Λ]).rightDerivedFunctorPlus.map
          ((Functor.mapDerivedCategoryPlusCompIso ((e)^*[ModuleCat.{u + 1} Λ'])
            (Sheaf.restrictScalars Y.smallEtaleTopology φ)).hom.app K))) := by
      rw [h₂]
      infer_instance
    exact IsIso.of_isIso_comp_right _ (H.map (((h)_*[ModuleCat.{u + 1} Λ]).rightDerivedFunctorPlus.map
          ((Functor.mapDerivedCategoryPlusCompIso ((e)^*[ModuleCat.{u + 1} Λ'])
            (Sheaf.restrictScalars Y.smallEtaleTopology φ)).hom.app K)))
  -- transport along the naturality square
  have h₃ := congr_arg H.map hN
  simp only [Functor.map_comp] at h₃
  have : IsIso (H.map ((Functor.rightDerivedFunctorPlusBaseChange
      (Functor.baseChangePaste (Iso.refl _).hom
        (Etale.baseChangeMap (ModuleCat.{u + 1} Λ) sq.toCommSq))).app K)) := by
    have : IsIso (H.map ((Functor.rightDerivedFunctorPlusBaseChange
        (Functor.baseChangePaste (Iso.refl _).hom
          (Etale.baseChangeMap (ModuleCat.{u + 1} Λ) sq.toCommSq))).app K) ≫
        H.map (((h)_*[ModuleCat.{u + 1} Λ]).rightDerivedFunctorPlus.map
          ((Functor.mapDerivedCategoryPlusNatIso
            (asIso (Etale.upperStarRestrictScalars φ e).natTrans)).hom.app K))) := by
      rw [h₃]
      infer_instance
    exact IsIso.of_isIso_comp_right _ _
  -- the homology of the base change morphism of the first pasting
  have h₄ := congr_arg H.map hA
  simp only [Functor.map_comp] at h₄
  have : IsIso (H.map ((Functor.mapDerivedCategoryPlusCompIso
      (Sheaf.restrictScalars S.smallEtaleTopology φ) ((p)^*[ModuleCat.{u + 1} Λ])).hom.app
        ((((g)_*[ModuleCat.{u + 1} Λ']).rightDerivedFunctorPlus).obj K)) ≫
      H.map (((p)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlus.map
        ((Functor.rightDerivedFunctorPlusBaseChange (Iso.refl _).hom).app K)) ≫
      H.map ((Functor.rightDerivedFunctorPlusBaseChange
        (Etale.baseChangeMap (ModuleCat.{u + 1} Λ) sq.toCommSq)).app
          ((Sheaf.restrictScalars T.smallEtaleTopology φ).mapDerivedCategoryPlus.obj K))) := by
    rw [← h₄]
    infer_instance
  have := IsIso.of_isIso_comp_left _ _ (self := this)
  exact IsIso.of_isIso_comp_left _ _

end ChangeOfRings

section Torsion

/-- The change of rings `Λ ↝ Λ/nΛ` for the base-change map.

Let `F` be a sheaf of `Λ`-modules on `T_ét` killed by `n`. Then `F` is a sheaf of
`Λ/nΛ`-modules, restriction of scalars along `Λ ⟶ Λ/nΛ` commutes with `p^*`, `e^*` and with the
derived pushforwards (the cohomology of a sheaf of modules does not depend on the coefficient
ring), and identifies the base-change map of `F` over `Λ` with the one over `Λ/nΛ`. Hence the
base-change property `BC(p, Λ/nΛ, q)` makes the base-change map of `F` an isomorphism. -/
theorem Etale.isIso_baseChangeHomologyMap_of_nsmul_eq_zero (sq : IsPullback e h g p)
    [QuasiCompact g] [QuasiSeparated g] (q : ℤ) (n : ℕ)
    (hp : Etale.BaseChangeProperty (Λ ⧸ Ideal.span {(n : Λ)}) p q)
    (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (hF : n • 𝟙 F = 0) :
    IsIso (Etale.baseChangeHomologyMap Λ sq q F) := by
  let φ : Λ →+* Λ ⧸ Ideal.span {(n : Λ)} := Ideal.Quotient.mk _
  let rT := Sheaf.restrictScalars T.smallEtaleTopology φ
  -- `F` is the restriction of scalars of the sheaf of `Λ/nΛ`-modules `F' = Hom_Λ(Λ/nΛ, F)`
  let F' := (sheafCompose T.smallEtaleTopology (ModuleCat.coextendScalars.{u + 1} φ)).obj F
  have : IsIso ((Sheaf.restrictCoextendScalarsAdj T.smallEtaleTopology φ).counit.app F) :=
    Etale.isIso_restrictCoextendScalarsAdj_counit_app (n : Λ) F
      (Etale.natCast_smul_eq_zero_of_nsmul_eq_zero hF)
  suffices IsIso (Etale.baseChangeHomologyMap Λ sq q (rT.obj F')) from
    Etale.isIso_of_comm _ _ (Etale.baseChangeHomologyMap_naturality Λ sq q
      ((Sheaf.restrictCoextendScalarsAdj T.smallEtaleTopology φ).counit.app F)).symm
  -- the base-change map of `F'` over `Λ/nΛ` is an isomorphism, hence so is the one of `res F'`
  have key := Etale.isIso_homologyMap_baseChange_restrictScalars φ sq q
    ((DerivedCategory.Plus.singleFunctor _ 0).obj F') (hp g e h sq F')
  change IsIso ((DerivedCategory.Plus.homologyFunctor _ q).map
    ((Etale.baseChange (ModuleCat.{u + 1} Λ) sq.toCommSq).app
      ((DerivedCategory.Plus.singleFunctor _ 0).obj (rT.obj F'))))
  have w := congr_arg (DerivedCategory.Plus.homologyFunctor _ q).map
    ((Etale.baseChange (ModuleCat.{u + 1} Λ) sq.toCommSq).naturality
      ((rT.mapDerivedCategoryPlusSingleFunctor 0).hom.app F'))
  simp only [Functor.map_comp] at w
  exact Etale.isIso_of_comm _ _ w

/-- *Filtered torsion*: to prove that the base-change map is an isomorphism at a sheaf which is
torsion of orders invertible on `S`, it suffices to do so at the sheaves killed by a single
positive integer `n` invertible on `S`. Such a sheaf is a filtered colimit of sheaves of that
kind, the source and the target of the base-change map commute with filtered colimits, and a
natural transformation between colimit-preserving functors which is an isomorphism on a
diagram is an isomorphism at its colimit. -/
theorem Etale.isIso_baseChangeHomologyMap_of_forall_nsmul_eq_zero (sq : IsPullback e h g p)
    [QuasiCompact g] [QuasiSeparated g] (q : ℤ)
    (H : ∀ n : ℕ, 0 < n → IsUnit (n : Γ(S, ⊤)) →
      ∀ G : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ), n • 𝟙 G = 0 →
        IsIso (Etale.baseChangeHomologyMap Λ sq q G))
    (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    [Scheme.IsTorsionSheafOfInvertibleOrder S F] :
    IsIso (Etale.baseChangeHomologyMap Λ sq q F) := by
  have : QuasiCompact h := MorphismProperty.of_isPullback sq ‹_›
  have : QuasiSeparated h := MorphismProperty.of_isPullback sq ‹_›
  obtain ⟨J, _, _, D, c, hc, rfl, hD⟩ :=
    Scheme.IsTorsionSheafOfInvertibleOrder.exists_isColimit Λ S F
  have := Etale.preservesColimitsOfShape_higherDirectImage Λ g q J
  have := Etale.preservesColimitsOfShape_higherDirectImage Λ h q J
  have : PreservesColimitsOfSize.{0, 0} ((p)^*[ModuleCat.{u + 1} Λ]) :=
    (Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) p).leftAdjoint_preservesColimits
  have : PreservesColimitsOfSize.{0, 0} ((e)^*[ModuleCat.{u + 1} Λ]) :=
    (Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) e).leftAdjoint_preservesColimits
  have : PreservesColimitsOfShape J (Etale.baseChangeSourceFunctor Λ p g q) :=
    preservesColimitsOfShape_of_natIso (Etale.baseChangeSourceFunctorIso Λ p g q).symm
  have : PreservesColimitsOfShape J (Etale.baseChangeTargetFunctor Λ e h q) :=
    preservesColimitsOfShape_of_natIso (Etale.baseChangeTargetFunctorIso Λ e h q).symm
  have : IsIso (Functor.whiskerLeft D (Etale.baseChangeHomologyNatTrans Λ sq q)) := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro j
    obtain ⟨n, hn, hnS, hnj⟩ := hD j
    exact H n hn hnS _ hnj
  exact isIso_app_coconePt_of_preservesColimit D _ c hc

end Torsion

end AlgebraicGeometry
