/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.NearbyCycles.TraitChangeInduction.Slice
public import WeilConjectures.SixFunctors.NearbyCycles.TraitChangeInduction.Coordinates
public import WeilConjectures.SixFunctors.NearbyCycles.RestrictOpens
public import WeilConjectures.SixFunctors.NearbyCycles.ProperTraitChange
public import WeilConjectures.SixFunctors.NearbyCycles.TraitCompactification
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ClosedPointsDetection
public import WeilConjectures.Compactification.AffineCharts
import WeilConjectures.Tactic.ExactModProofs

/-!

# Deligne's induction for the change of strictly henselian trait

This file proves `NearbyCyclesModel.TraitChangeInvariance T m` for every `m`
(`NearbyCyclesModel.traitChangeInvariance`), i.e. SGA 4½, [Th. finitude], Prop. 3.7, with
coefficients a finite ring `T`, by induction on the dimension `m` of the affine spaces into
which the total space locally embeds.

1. **Proper models** (`NearbyCyclesModel.traitChangeInvariance_of_isProper`). The exchange is a
   morphism of complexes of étale origin on the special fibre `X'`, a scheme of finite type over
   the separably closed field `κ`. Its global cohomology `Rp₂_*` is invertible by step (B)
   (`NearbyCyclesModel.Hom.isIso_map_pullbackExchange_app_of_isProper_trait`), and it is invertible
   after pullback to the slice over the generic point of every coordinate line of every chart
   (step (A), `NearbyCyclesModel.Hom.exists_isIso_map_pullbackExchange_slice`, using the induction
   hypothesis). Every non-closed point of `X'` lies over such a generic point
   (`AlgebraicGeometry.AffineSpace.exists_isGenericPoint_reindex_of_not_isClosed`), so the
   closed-point criterion
   (`ProEtale.CondensedRing.isIso_of_isIso_leftDerivedUpperStar_map_of_not_isClosed`) applies.
2. **Charts** (`NearbyCyclesModel.traitChangeInvariance_of_isImmersion`): a model with an
   immersion into `𝔸(ι; S₁)` is open in its closure in `ℙ(ι; S₁)`, a proper model locally embedding
   into `𝔸(ι; S₁)` (`AlgebraicGeometry.Compactification.ofIsImmersionAffineSpace`), and the exchange
   is invertible once it is for the compactification
   (`NearbyCyclesModel.Hom.isIso_pullbackExchange_app_of_compactification`).
3. **General models**: invertibility of the exchange is local on the total space
   (`NearbyCyclesModel.Hom.isIso_toGeneric_pullbackExchange_app_of_restrictOpens`).

-/

@[expose] public section

universe u

open CategoryTheory Limits IsLocalRing

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel

open Scheme

variable (T : Type) [TopologicalSpace T] [CommRing T] [IsTopologicalRing T] [DiscreteTopology T]
  [Finite T]

variable {R₁ R₂ : Type u} [CommRing R₁] [IsDomain R₁] [IsDiscreteValuationRing R₁]
  [IsStrictlyHenselianLocalRing R₁] [CommRing R₂] [IsDomain R₂] [IsDiscreteValuationRing R₂]
  [IsStrictlyHenselianLocalRing R₂] {ι : R₁ →+* R₂} [IsLocalHom ι]
  {Ω₁ Ω₂ : Type u} [Field Ω₁] [IsAlgClosed Ω₁] [Field Ω₂] [IsAlgClosed Ω₂]
  {a₁ : R₁ →+* Ω₁} {a₂ : R₂ →+* Ω₂} {c : Ω₁ →+* Ω₂}
  {κ : Type u} [Field κ] [IsSepClosed κ] {b₂ : R₂ →+* κ}
  {X X' Y Y' : Scheme.{u}} {M : NearbyCyclesModel X X'} {N : NearbyCyclesModel Y Y'}
  {f : X ⟶ Y} {f' : X' ⟶ Y'}

/-- **The witnesses of the closed-point criterion** (SGA 4½, [Th. finitude], proof of 3.7,
step (A)). In the situation of `NearbyCyclesModel.TraitChangeInvariance` in chart dimension `m`,
assuming it in smaller chart dimension, every non-closed point `x` of the special fibre `X'` of
`M` is in the image of a morphism `h : W ⟶ X'` along which the pullback of the exchange of
`φ.toGeneric` is invertible: choose a chart `V ⟶ 𝔸(ι; S₁)` of `N` around the image of `x`, a
coordinate sending `x` to the generic point of `𝔸¹_κ`
(`AlgebraicGeometry.AffineSpace.exists_isGenericPoint_reindex_of_not_isClosed`), and slice the
restriction of `φ` to `V` along it (`NearbyCyclesModel.Hom.exists_isIso_map_pullbackExchange_slice`,
`NearbyCyclesModel.Hom.isIso_leftDerivedUpperStar_map_pullbackExchange_app_of_restrictOpens`). -/
theorem Hom.exists_isIso_map_pullbackExchange_of_not_isClosed {m : ℕ}
    (ih : ∀ m' < m, TraitChangeInvariance.{u} T m') (hι : Function.Injective ι)
    (hun : maximalIdeal R₂ = (maximalIdeal R₁).map ι)
    (p : ℕ) [Fact p.Prime] (hp : ∀ n : ℕ, (n : ResidueField R₁) = 0 → p ∣ n)
    (hpT : IsUnit (p : T)) (ha₁ : Function.Injective a₁) (ha₂ : Function.Injective a₂)
    (halg₁ : letI := a₁.toAlgebra; Algebra.IsAlgebraic R₁ Ω₁)
    (halg₂ : letI := a₂.toAlgebra; Algebra.IsAlgebraic R₂ Ω₂) (hc : c.comp a₁ = a₂.comp ι)
    (hb₂ : RingHom.ker b₂ = maximalIdeal R₂) (φ : M.Hom N f f') (q₁ : N.total ⟶ Spec (.of R₁))
    [LocallyOfFiniteType q₁] [QuasiCompact q₁] [IsSeparated q₁]
    (hm : q₁.LocallyEmbedsInAffineSpace m) (g₁ : N.generic ⟶ Spec (.of Ω₁))
    (hNj : IsPullback N.j g₁ q₁ (Spec.map (CommRingCat.ofHom a₁))) (p₁ : Y' ⟶ Spec (.of κ))
    (hNi : IsPullback N.i p₁ q₁ (Spec.map (CommRingCat.ofHom (b₂.comp ι))))
    (q₂ : M.total ⟶ Spec (.of R₂)) (g₂ : M.generic ⟶ Spec (.of Ω₂))
    (hMj : IsPullback M.j g₂ q₂ (Spec.map (CommRingCat.ofHom a₂))) (p₂ : X' ⟶ Spec (.of κ))
    (hMi : IsPullback M.i p₂ q₂ (Spec.map (CommRingCat.ofHom b₂)))
    (hφ : IsPullback φ.total q₂ q₁ (Spec.map (CommRingCat.ofHom ι)))
    (hgen : φ.generic ≫ g₁ = g₂ ≫ Spec.map (CommRingCat.ofHom c)) (hs : f' ≫ p₁ = p₂)
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology N.generic) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj T) N.generic)))
    (hK : DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} (ULift.{u + 1} T)) N.generic
      ((finiteCoefficientDerivedEquivalence N.generic T).functor.obj K))
    (x : X') (hx : ¬ IsClosed ({x} : Set X')) :
    ∃ (W : Scheme.{u}) (h : W ⟶ X') (w : W), h w = x ∧
      IsIso ((L((h)^*⟦Profinite.continuousMapRingObj T⟧)).map
        ((φ.toGeneric.pullbackExchange (Profinite.continuousMapRingObj T)).app K)) :=
  sorry

/-- **Proper models** (SGA 4½, [Th. finitude], proof of 3.7). In the situation of
`NearbyCyclesModel.TraitChangeInvariance` with `q₁` proper, assuming the invariance in smaller
chart dimension, the exchange is invertible: its global cohomology is invertible by step (B), and
it is invertible over every non-closed point of the special fibre by step (A)
(`NearbyCyclesModel.Hom.exists_isIso_map_pullbackExchange_of_not_isClosed`); conclude with the
closed-point criterion. -/
theorem traitChangeInvariance_of_isProper {m : ℕ}
    (ih : ∀ m' < m, TraitChangeInvariance.{u} T m') (hι : Function.Injective ι)
    (hun : maximalIdeal R₂ = (maximalIdeal R₁).map ι)
    (p : ℕ) [Fact p.Prime] (hp : ∀ n : ℕ, (n : ResidueField R₁) = 0 → p ∣ n)
    (hpT : IsUnit (p : T)) (ha₁ : Function.Injective a₁) (ha₂ : Function.Injective a₂)
    (halg₁ : letI := a₁.toAlgebra; Algebra.IsAlgebraic R₁ Ω₁)
    (halg₂ : letI := a₂.toAlgebra; Algebra.IsAlgebraic R₂ Ω₂) (hc : c.comp a₁ = a₂.comp ι)
    (hb₂ : RingHom.ker b₂ = maximalIdeal R₂) (φ : M.Hom N f f') (q₁ : N.total ⟶ Spec (.of R₁))
    [IsProper q₁] (hm : q₁.LocallyEmbedsInAffineSpace m) (g₁ : N.generic ⟶ Spec (.of Ω₁))
    (hNj : IsPullback N.j g₁ q₁ (Spec.map (CommRingCat.ofHom a₁))) (p₁ : Y' ⟶ Spec (.of κ))
    (hNi : IsPullback N.i p₁ q₁ (Spec.map (CommRingCat.ofHom (b₂.comp ι))))
    (q₂ : M.total ⟶ Spec (.of R₂)) (g₂ : M.generic ⟶ Spec (.of Ω₂))
    (hMj : IsPullback M.j g₂ q₂ (Spec.map (CommRingCat.ofHom a₂))) (p₂ : X' ⟶ Spec (.of κ))
    (hMi : IsPullback M.i p₂ q₂ (Spec.map (CommRingCat.ofHom b₂)))
    (hφ : IsPullback φ.total q₂ q₁ (Spec.map (CommRingCat.ofHom ι)))
    (hgen : φ.generic ≫ g₁ = g₂ ≫ Spec.map (CommRingCat.ofHom c)) (hs : f' ≫ p₁ = p₂)
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology N.generic) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj T) N.generic)))
    (hK : DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} (ULift.{u + 1} T)) N.generic
      ((finiteCoefficientDerivedEquivalence N.generic T).functor.obj K)) :
    IsIso ((φ.toGeneric.pullbackExchange (Profinite.continuousMapRingObj T)).app K) :=
  sorry

/-- **Deligne's induction** (SGA 4½, [Th. finitude], Prop. 3.7, coefficients a finite ring): the
invariance of nearby cycles under change of strictly henselian trait holds in every chart
dimension. By strong induction on `m`: invertibility is local on the total space
(`NearbyCyclesModel.Hom.isIso_toGeneric_pullbackExchange_app_of_restrictOpens`), so one may assume
an immersion `N ⟶ 𝔸(ι; S₁)` with `|ι| ≤ m`; the closure in `ℙ(ι; S₁)` is a proper model locally
embedding into `𝔸(ι; S₁)` (`AlgebraicGeometry.Compactification.ofIsImmersionAffineSpace`,
`AlgebraicGeometry.Compactification.locallyEmbedsInAffineSpace_ofIsImmersionAffineSpace`), to
which one reduces (`NearbyCyclesModel.Hom.isIso_pullbackExchange_app_of_compactification`), and
the proper case is `NearbyCyclesModel.traitChangeInvariance_of_isProper`. -/
theorem traitChangeInvariance (m : ℕ) : TraitChangeInvariance.{u} T m :=
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel
