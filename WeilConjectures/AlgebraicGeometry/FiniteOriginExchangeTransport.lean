/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ChosenCartesianSquare
public import WeilConjectures.AlgebraicGeometry.Fixed.FixedEtaleOriginWitness
public import WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange

/-!
# Finite-origin transport of proper exchange
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor
open AlgebraicGeometry

namespace AlgebraicGeometry.ProEtale

/-- Finite discrete coefficients transport an isomorphic étale exchange to the corresponding
pro-étale exchange.  The comparison identity is recorded together with invertibility of the
exchange at `ν_X^* L`, and every retained étale-origin witness of `K` whose antecedent is
(isomorphic to) the same `L` gives invertibility of the exchange at `K`. -/
theorem finiteOriginExchangeTransport
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] [TopologicalSpace Λ] [DiscreteTopology Λ]
    {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y}
    (sq : ChosenCartesianSquare g' f' f g) [IsProper f]
    [QuasiCompact f'] [QuasiSeparated f']
    (L : DerivedCategory.Plus
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    [IsIso ((Etale.baseChange (ModuleCat.{u + 1} Λ) sq.toCommSq).app L)] :
    IsIso ((ProEtale.derivedBaseChangeMap (ModuleCat.{u + 1} Λ) sq.toCommSq).app
      ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} Λ) X).mapDerivedCategory.obj
        (DerivedCategory.Plus.ι.obj L))) ∧
      (D(ν^*(Y')[ModuleCat.{u + 1} Λ]).map
          (DerivedCategory.Plus.ι.map
            ((Etale.baseChange (ModuleCat.{u + 1} Λ) sq.toCommSq).app L)) ≫
        (ProEtale.baseChangeTargetComparisonIso g' f' Λ).hom.app L =
        (ProEtale.baseChangeSourceComparisonIso f g Λ).hom.app L ≫
          (ProEtale.derivedBaseChangeMap (ModuleCat.{u + 1} Λ) sq.toCommSq).app
            ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} Λ) X).mapDerivedCategory.obj
              (DerivedCategory.Plus.ι.obj L))) ∧
      (∀ (K : DerivedCategory.Plus
        (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)))
        (w : Scheme.FixedEtaleOriginWitness X Λ K) (_e : w.complex ≅ L),
        IsIso ((ProEtale.derivedBaseChangeMap (ModuleCat.{u + 1} Λ) sq.toCommSq).app K.obj)) := by
  have hsq : IsPullback g' f' f g :=
    IsPullback.of_iso_pullback sq.toCommSq sq.isoPullback sq.hom_fst sq.hom_snd
  have hcomp := ProEtale.comparison_derivedBaseChangeMap Λ hsq L
  have hmap : IsIso ((comparisonUpperStar (ModuleCat.{u + 1} Λ) Y').mapDerivedCategory.map
      (DerivedCategory.Plus.ι.map
        ((Etale.baseChange (ModuleCat.{u + 1} Λ) hsq.toCommSq).app L))) := inferInstance
  have hiso : IsIso ((ProEtale.derivedBaseChangeMap (ModuleCat.{u + 1} Λ)
      hsq.toCommSq).app
      ((comparisonUpperStar (ModuleCat.{u + 1} Λ) X).mapDerivedCategory.obj
        (DerivedCategory.Plus.ι.obj L))) := by
    exact ((MorphismProperty.isomorphisms _).arrow_mk_iso_iff
      (Arrow.isoMk ((ProEtale.baseChangeSourceComparisonIso f g Λ).app L)
        ((ProEtale.baseChangeTargetComparisonIso g' f' Λ).app L) hcomp.symm)).1 hmap
  have hfirst : IsIso ((ProEtale.derivedBaseChangeMap (ModuleCat.{u + 1} Λ)
      sq.toCommSq).app
      ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} Λ) X).mapDerivedCategory.obj
        (DerivedCategory.Plus.ι.obj L))) := by
    simpa using hiso
  refine ⟨hfirst, ?_, ?_⟩
  · simpa using hcomp
  · intro K w e
    let eK : (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} Λ) X).mapDerivedCategory.obj
        (DerivedCategory.Plus.ι.obj L) ≅ K.obj :=
      ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} Λ) X).mapDerivedCategory.mapIso
        (DerivedCategory.Plus.ι.mapIso e.symm)) ≪≫ w.iso
    rw [← NatTrans.isIso_app_iff_of_iso _ eK]
    exact hfirst

end AlgebraicGeometry.ProEtale
