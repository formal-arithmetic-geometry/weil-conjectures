/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.ConstructibleSheaf.Defs
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Basic
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Stalk

/-!
# Constructible sheaves with coefficients without nonzero finite objects

A constructible sheaf has finite stalks: by definition its pullbacks to the strata of a
stratification are finite, and the stalk of a pullback is the stalk at the image point
(`AlgebraicGeometry.Etale.upperStarCompSheafFiberIso`). If the coefficient category `A` has
no nonzero objects with finite underlying type, all these stalks vanish, and since the
geometric points of the strata cover `X`, the sheaf itself is zero
(`AlgebraicGeometry.Scheme.IsConstructibleSheaf.isZero_of_isZero_of_finite`).

This applies to modules over an infinite field `K`
(`AlgebraicGeometry.Scheme.IsConstructibleSheaf.isZero`): a nonzero vector `v` gives an
injection `c ↦ c • v` of `K` into the module. In particular, with the coefficients
`ModuleCat.{u + 1} (ULift.{u + 1} (PadicAlgCl l))` of Weil sheaves, every constructible sheaf
is zero.

## Main results

- `AlgebraicGeometry.Scheme.IsConstructibleSheaf.isZero_of_isZero_of_finite`: a constructible
  sheaf with values in a category without nonzero finite objects is zero.
- `AlgebraicGeometry.Scheme.IsConstructibleSheaf.isZero`: a constructible sheaf of modules
  over an infinite field is zero.
-/

@[expose] public section

universe u u' v w

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme

variable {A : Type u'} [Category.{u + 1} A] [Abelian A]
  {FA : A → A → Type (u + 1)} {CA : A → Type (u + 1)}
  [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory.{u + 1} A FA]
  [IsGrothendieckAbelian.{u + 1} A] [(CategoryTheory.forget A).ReflectsIsomorphisms]
  [PreservesFilteredColimitsOfSize.{u + 1, u + 1} (CategoryTheory.forget A)]
  {X : Scheme.{u}} [X.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget A)]

/-- If the coefficient category `A` has no nonzero objects with finite underlying type, every
constructible `A`-valued sheaf on the small étale site of `X` is zero. Its stalks at the
geometric points `Spec Ω ⟶ Y ⟶ X` of the strata `Y` of a stratification are the stalks of
the pullbacks to the strata, which are finite, hence zero; these geometric points cover `X`,
so they form a conservative family. -/
theorem IsConstructibleSheaf.isZero_of_isZero_of_finite
    (hA : ∀ M : A, Finite (ToType M) → IsZero M)
    (F : Sheaf X.smallEtaleTopology A) [IsConstructibleSheaf F] : IsZero F := by
  obtain ⟨S, hS⟩ := IsConstructibleSheaf.exists_stratification (FA := FA) (CA := CA) (F := F)
  let s (p : Σ i : Fin S.n, S.domain i) := (S.domain p.1).algClosurePoint p.2 ≫ S.immersion p.1
  have hs : ⋃ p, Set.range (s p) = Set.univ := by
    refine Set.eq_univ_of_forall fun x ↦ ?_
    obtain ⟨i, hi⟩ := Set.mem_iUnion.1 (S.iUnion_stratum_eq_univ.symm ▸ Set.mem_univ x)
    rw [← S.range_immersion] at hi
    obtain ⟨y, rfl⟩ := hi
    exact Set.mem_iUnion.2 ⟨⟨i, y⟩, default, by simp [s]⟩
  have hfib (p : Σ i : Fin S.n, S.domain i) :
      IsZero (((pointSmallEtale (s p)).ulift.{u + 1}).sheafFiber.obj F) :=
    (hA _ ((hS p.1).finite_sheafFiber _ _)).of_iso
      (((pointSmallEtale (s p)).uliftSheafFiberIso A).app F ≪≫
        ((Etale.upperStarCompSheafFiberIso A (S.immersion p.1) _).app F).symm)
  have : IsIso (0 : F ⟶ F) :=
    (((isConservativeFamilyOfPoints_ulift_pointSmallEtale_of_iUnion_range_eq_univ X s
      hs).jointlyReflectIsomorphisms A).isIso_iff (0 : F ⟶ F)).2 fun ⟨_, ⟨p⟩⟩ ↦
        (hfib p).isIso (hfib p) _
  exact IsZero.of_mono_zero F F

/-- If the coefficient category `A` has no nonzero objects with finite underlying type, the
stalks of a constructible `A`-valued sheaf at all geometric points are zero. -/
theorem IsConstructibleSheaf.isZero_sheafFiber_of_isZero_of_finite
    (hA : ∀ M : A, Finite (ToType M) → IsZero M)
    (F : Sheaf X.smallEtaleTopology A) [IsConstructibleSheaf F]
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ X) :
    IsZero ((pointSmallEtale s).sheafFiber.obj F) :=
  (pointSmallEtale s).sheafFiber.map_isZero (isZero_of_isZero_of_finite hA F)

/-- A constructible sheaf of modules over an infinite field `K` (lifted to `Type (u + 1)`) on
the small étale site is zero, its stalks being finite modules over `K`. This applies to the
coefficients `ModuleCat.{u + 1} (ULift.{u + 1} (PadicAlgCl l))` of Weil sheaves. -/
theorem IsConstructibleSheaf.isZero {K : Type} [Field K] [Infinite K]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} K)))
    [IsConstructibleSheaf F] : IsZero F :=
  isZero_of_isZero_of_finite (fun M _ ↦ ModuleCat.isZero_ulift_of_finite M) F

/-- The stalks of a constructible sheaf of modules over an infinite field `K` (lifted to
`Type (u + 1)`) at all geometric points are zero. -/
theorem IsConstructibleSheaf.isZero_sheafFiber {K : Type} [Field K] [Infinite K]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} K)))
    [IsConstructibleSheaf F] {Ω : Type u} [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ X) :
    IsZero ((pointSmallEtale s).sheafFiber.obj F) :=
  isZero_sheafFiber_of_isZero_of_finite (fun M _ ↦ ModuleCat.isZero_ulift_of_finite M) F s

end AlgebraicGeometry.Scheme
