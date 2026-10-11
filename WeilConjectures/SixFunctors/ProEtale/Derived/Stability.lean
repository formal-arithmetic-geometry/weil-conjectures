/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.Topology.KrullDimension
public import WeilConjectures.SixFunctors.ProEtale.Derived.TorAmplitude
public import WeilConjectures.SixFunctors.ProEtale.Derived.UpperLowerStar
public import WeilConjectures.SixFunctors.ProEtale.Derived.HomComparison
public import WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange
public import WeilConjectures.SixFunctors.Etale.Derived.Stability.DirectImage
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.Linear
public import WeilConjectures.CategoryTheory.Sites.NsmulSheaf

/-!

# Stability of `Dctf` under direct image on the pro-étale site

This file is the pro-étale counterpart of the direct-image part of
`WeilConjectures.SixFunctors.Etale.Derived.Stability`: for `Y` of finite type over a field `k`,
coefficients killed by an integer `N` invertible in `k`, and `f : X ⟶ Y` separated of finite
type, the derived direct image `Rf_* : D(X_proét) ⥤ D(Y_proét)` preserves bounded
constructibility, and for a finite coefficient ring `Λ` and `dim X ≤ d` it moves the Tor
amplitude from `[a, b]` to `[a, b + 2d]`.

## Main statements

- `AlgebraicGeometry.ProEtale.boundedConstructible_rightDerivedLowerStar`,
  `AlgebraicGeometry.ProEtale.torAmplitudeIn_rightDerivedLowerStar`
  (`sk-cor-sf-direct-image-ctf`).
- `ProEtale.boundedConstructible_and_torAmplitudeIn_rightDerivedLowerStar_mapDerivedCategory`
  (`cor-sf-direct-image-ctf-etale-origin`): the case of a complex `ν^* K'` of étale origin.
- `AlgebraicGeometry.ProEtale.boundedConstructible_and_torAmplitudeIn_rightDerivedLowerStar`
  (`cor-sf-direct-image-ctf-proetale`): the case of every bounded constructible complex.

## Implementation notes

The blueprint deduces this corollary from its étale counterpart
`sk-thm-sf-direct-image-tor-amplitude` by writing a bounded constructible pro-étale complex as
`ν^* K'` for an étale complex `K'` (`lem-sf-proetale-constructible-origin`). Here bounded
constructibility on the pro-étale site
(`AlgebraicGeometry.ProEtale.DerivedCategory.boundedConstructible`) is *defined* as étale
origin, so that lemma is built in. The two comparison inputs are `Rf_* ν^* K' ≅ ν^* Rf_* K'`
(`AlgebraicGeometry.ProEtale.rightDerivedLowerStarMapDerivedCategoryObjIso`) and the fact that
`ν^*` preserves and detects Tor amplitude
(`AlgebraicGeometry.ProEtale.DerivedCategory.torAmplitudeIn_mapDerivedCategory_iff`, which needs
the coefficients to be a finite ring `Λ`).

The coefficient category is torsion of order invertible on the base: `N • 𝟙 M = 0` for every
`M : A`, with `(N : k) ≠ 0`. Without this the statements fail, already for
`A = ModuleCat (ZMod p)` and the affine line over a separably closed field of characteristic
`p`, whose `H¹` is infinite by Artin–Schreier theory. Being of finite type over a field is the
base condition of Deligne's finiteness theorem. These are the finite coefficient stages
`A_{E,n}` of the blueprint, where étale-origin bounded constructibility is the right notion.

A dimension bound `dim X ≤ d` is `topologicalKrullDim X ≤ (d : WithBot ℕ∞)`, as in the étale
file.

-/

@[expose] public section
universe u' u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace ProEtale

section Comparison

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]

/-- For `f` quasi-compact and quasi-separated and a bounded below complex `K'` of étale sheaves,
the pro-étale direct image of `ν^* K'` is `ν^* Rf_* K'`: the component at `K'` of the comparison
isomorphism `AlgebraicGeometry.ProEtale.rightDerivedLowerStarComparisonIso'` (blueprint
`prop-weil-pbc-comparison-direct-image`). -/
noncomputable def rightDerivedLowerStarMapDerivedCategoryObjIso
    (K' : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A))
    (hK' : _root_.DerivedCategory.TStructure.t.plus K') :
    (R(ProEtale.lowerStar A f)).obj (D(ν^*(X)[A]).obj K') ≅
      D(ν^*(Y)[A]).obj ((R(Etale.lowerStar A f)).obj K') :=
  ((rightDerivedLowerStarComparisonIso' f A).app ⟨K', hK'⟩).symm ≪≫
    D(ν^*(Y)[A]).mapIso ((Etale.lowerStar A f).rightDerivedFunctorPlusCompatibility.app ⟨K', hK'⟩)

end Comparison

section DirectImage

section Unit

variable {k : Type u} [Field k] (N : ℕ) (hN : (N : k) ≠ 0) {Y : Scheme.{u}}
  (s : Y ⟶ Spec (CommRingCat.of k))

include hN s in
/-- An integer `N` that is nonzero in a field `k` is invertible on a `k`-scheme. -/
lemma isUnit_natCast_of_ne_zero : IsUnit (N : Γ(Y, ⊤)) := by
  simpa using (Ne.isUnit hN).map ((Scheme.ΓSpecIso (.of k)).inv ≫ s.appTop).hom

end Unit

section General

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]
  {FA : A → A → Type (u + 1)} {CA : A → Type (u + 1)}
  [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory.{u + 1} A FA]
  [hA' : ConcreteCategory.FinitelyGeneratedOfMono A]
  {k : Type u} [Field k] (N : ℕ) (hN : (N : k) ≠ 0) (hA : ∀ M : A, N • 𝟙 M = 0)
  {X Y : Scheme.{u}} (s : Y ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType s] [QuasiCompact s]
  (f : X ⟶ Y) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]

include hN hA hA' s

/-- Blueprint `sk-cor-sf-direct-image-ctf`: Direct image preserves bounded constructibility on
the pro-étale site.

Let `Y` be of finite type over a field `k`, let `A` be killed by an integer `N` invertible in
`k` and noetherian, subobjects of finitely generated objects being finitely generated
(`CategoryTheory.ConcreteCategory.FinitelyGeneratedOfMono`, which holds for `ModuleCat Λ` with
`Λ` noetherian), and let `f : X ⟶ Y` be separated of finite type. If `K` is a bounded
constructible complex on `X_proét`, then `Rf_* K` is bounded constructible on `Y_proét`.

Write `K ≅ ν^* K'` for a bounded constructible étale complex `K'`. Then
`Rf_* K ≅ ν^* Rf_* K'` (`AlgebraicGeometry.ProEtale.rightDerivedLowerStarMapDerivedCategoryObjIso`),
and `Rf_* K'` is bounded constructible
(`AlgebraicGeometry.Etale.boundedConstructible_rightDerivedLowerStar`). -/
theorem boundedConstructible_rightDerivedLowerStar
    {K : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)}
    (hbc : DerivedCategory.boundedConstructible A X K) :
    DerivedCategory.boundedConstructible A Y ((R(ProEtale.lowerStar A f)).obj K) := by
  obtain ⟨K', hK', ⟨e⟩⟩ := hbc
  have : NeZero N := ⟨by rintro rfl; exact hN Nat.cast_zero⟩
  exact (DerivedCategory.boundedConstructible A Y).prop_of_iso
    ((R(ProEtale.lowerStar A f)).mapIso e.symm ≪≫
      rightDerivedLowerStarMapDerivedCategoryObjIso A f K' hK'.1.1).symm
    (DerivedCategory.boundedConstructible_comparisonUpperStar_mapDerivedCategory_obj
      (Etale.boundedConstructible_rightDerivedLowerStar A (f ≫ s) s f rfl N
        (_root_.DerivedCategory.nsmul_id_eq_zero_of_forall
          (Sheaf.nsmul_id_eq_zero_of_forall hA) K') (isUnit_natCast_of_ne_zero N hN s) hK'))

end General

section Finite

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
  {k : Type u} [Field k] (N : ℕ) (hN : (N : k) ≠ 0) (hA : ∀ M : ModuleCat.{u + 1} Λ, N • 𝟙 M = 0)
  {X Y : Scheme.{u}} (s : Y ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType s] [QuasiCompact s]
  (f : X ⟶ Y) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]

include hN hA s

/-- Blueprint `cor-sf-direct-image-ctf-etale-origin`: The pro-étale direct image for objects of
étale origin.

Let `Y` be of finite type over a field `k`, let `Λ` be a finite ring killed by an integer `N`
invertible in `k`, let `f : X ⟶ Y` be separated of finite type with `dim X ≤ d`, and let `K'`
be a bounded constructible complex of étale sheaves of `Λ`-modules on `X` of Tor amplitude in
`[a, b]`. Then the pro-étale direct image `Rf_* ν^* K'` is bounded constructible on `Y_proét`
with Tor amplitude in `[a, b + 2d]`.

Indeed `Rf_* ν^* K' ≅ ν^* Rf_* K'`
(`AlgebraicGeometry.ProEtale.rightDerivedLowerStarMapDerivedCategoryObjIso`), where `Rf_* K'` is
bounded constructible with Tor amplitude in `[a, b + 2d]` on the étale site
(`AlgebraicGeometry.Etale.torAmplitudeIn_rightDerivedLowerStar`), and `ν^*` preserves both
properties (`AlgebraicGeometry.ProEtale.DerivedCategory.torAmplitudeIn_mapDerivedCategory_iff`). -/
theorem boundedConstructible_and_torAmplitudeIn_rightDerivedLowerStar_mapDerivedCategory
    (d : ℕ) (hd : topologicalKrullDim X ≤ (d : WithBot ℕ∞)) (a b : ℤ)
    {K' : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hbc : Etale.DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) X K')
    (hta : Etale.DerivedCategory.torAmplitudeIn (ModuleCat.{u + 1} Λ) X a b K') :
    DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) Y
        ((R(ProEtale.lowerStar (ModuleCat.{u + 1} Λ) f)).obj
          (D(ν^*(X)[ModuleCat.{u + 1} Λ]).obj K')) ∧
      DerivedCategory.torAmplitudeIn (ModuleCat.{u + 1} Λ) Y a (b + 2 * (d : ℤ))
        ((R(ProEtale.lowerStar (ModuleCat.{u + 1} Λ) f)).obj
          (D(ν^*(X)[ModuleCat.{u + 1} Λ]).obj K')) := by
  have : NeZero N := ⟨by rintro rfl; exact hN Nat.cast_zero⟩
  have e := rightDerivedLowerStarMapDerivedCategoryObjIso (ModuleCat.{u + 1} Λ) f K' hbc.1.1
  refine ⟨boundedConstructible_rightDerivedLowerStar (ModuleCat.{u + 1} Λ) N hN hA s f
    (DerivedCategory.boundedConstructible_comparisonUpperStar_mapDerivedCategory_obj hbc),
    (DerivedCategory.torAmplitudeIn (ModuleCat.{u + 1} Λ) Y a (b + 2 * (d : ℤ))).prop_of_iso
      e.symm ?_⟩
  exact (DerivedCategory.torAmplitudeIn_mapDerivedCategory_iff _ _ _).2
    (Etale.torAmplitudeIn_rightDerivedLowerStar _ (f ≫ s) s f rfl d hd a b N
      (_root_.DerivedCategory.nsmul_id_eq_zero_of_forall
        (Sheaf.nsmul_id_eq_zero_of_forall hA) K') (isUnit_natCast_of_ne_zero N hN s) hbc hta)

/-- Blueprint `cor-sf-direct-image-ctf-proetale`: The pro-étale direct image for all finite-Tor
objects.

Let `Y` be of finite type over a field `k`, let `Λ` be a finite ring killed by an integer `N`
invertible in `k`, and let `f : X ⟶ Y` be separated of finite type with `dim X ≤ d`. If `K` is a
bounded constructible complex on `X_proét` with Tor amplitude in `[a, b]`, then `Rf_* K` is
bounded constructible on `Y_proét` with Tor amplitude in `[a, b + 2d]`.

The complex `K` is `ν^* K'` for a bounded constructible étale complex `K'`, which has Tor
amplitude in `[a, b]` since `ν^*` detects Tor amplitude
(`AlgebraicGeometry.ProEtale.DerivedCategory.torAmplitudeIn_mapDerivedCategory_iff`); conclude by
the case of objects of étale origin (`cor-sf-direct-image-ctf-etale-origin`). -/
theorem boundedConstructible_and_torAmplitudeIn_rightDerivedLowerStar
    (d : ℕ) (hd : topologicalKrullDim X ≤ (d : WithBot ℕ∞)) (a b : ℤ)
    {K : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ))}
    (hbc : DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) X K)
    (hta : DerivedCategory.torAmplitudeIn (ModuleCat.{u + 1} Λ) X a b K) :
    DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) Y
        ((R(ProEtale.lowerStar (ModuleCat.{u + 1} Λ) f)).obj K) ∧
      DerivedCategory.torAmplitudeIn (ModuleCat.{u + 1} Λ) Y a (b + 2 * (d : ℤ))
        ((R(ProEtale.lowerStar (ModuleCat.{u + 1} Λ) f)).obj K) := by
  obtain ⟨K', hK', ⟨e⟩⟩ := hbc
  have h := boundedConstructible_and_torAmplitudeIn_rightDerivedLowerStar_mapDerivedCategory Λ N
    hN hA s f d hd a b hK' ((DerivedCategory.torAmplitudeIn_mapDerivedCategory_iff a b K').1
      ((DerivedCategory.torAmplitudeIn (ModuleCat.{u + 1} Λ) X a b).prop_of_iso e.symm hta))
  have e' := (R(ProEtale.lowerStar (ModuleCat.{u + 1} Λ) f)).mapIso e
  exact ⟨(DerivedCategory.boundedConstructible _ Y).prop_of_iso e' h.1,
    (DerivedCategory.torAmplitudeIn _ Y a (b + 2 * (d : ℤ))).prop_of_iso e' h.2⟩

/-- Blueprint `sk-cor-sf-direct-image-ctf`: Tor amplitude of the pro-étale direct image.

In the situation of `AlgebraicGeometry.ProEtale.boundedConstructible_rightDerivedLowerStar`,
for a finite ring `Λ`, if `dim X ≤ d` and `K` has Tor amplitude in `[a, b]`, then `Rf_* K` has
Tor amplitude in `[a, b + 2d]`. The shift `2d` is the uniform vanishing of `Rᵖf_*` above twice
the dimension of the source, for torsion coefficients of order invertible on the base. -/
theorem torAmplitudeIn_rightDerivedLowerStar (d : ℕ)
    (hd : topologicalKrullDim X ≤ (d : WithBot ℕ∞)) (a b : ℤ)
    {K : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ))}
    (hbc : DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) X K)
    (hta : DerivedCategory.torAmplitudeIn (ModuleCat.{u + 1} Λ) X a b K) :
    DerivedCategory.torAmplitudeIn (ModuleCat.{u + 1} Λ) Y a (b + 2 * (d : ℤ))
      ((R(ProEtale.lowerStar (ModuleCat.{u + 1} Λ) f)).obj K) :=
  (boundedConstructible_and_torAmplitudeIn_rightDerivedLowerStar Λ N hN hA s f d hd a b hbc
    hta).2

end Finite

end DirectImage

end ProEtale

end AlgebraicGeometry
