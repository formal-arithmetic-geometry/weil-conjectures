/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib
public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.HigherDirectImage

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
  (`AlgebraicGeometry.Scheme.IsTorsionModuleSheafOfInvertibleOrder.exists_isColimit`); the source
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
    IsIso (Etale.baseChangeHomologyMap Λ sq q F) :=
  sorry

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
    [Scheme.IsTorsionModuleSheafOfInvertibleOrder S F] :
    IsIso (Etale.baseChangeHomologyMap Λ sq q F) := by
  have : QuasiCompact h := MorphismProperty.of_isPullback sq ‹_›
  have : QuasiSeparated h := MorphismProperty.of_isPullback sq ‹_›
  obtain ⟨J, _, _, D, c, hc, rfl, hD⟩ :=
    Scheme.IsTorsionModuleSheafOfInvertibleOrder.exists_isColimit Λ S F
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
