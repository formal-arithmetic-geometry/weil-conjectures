/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OriginalCoefficientRefinementExchange
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.OpenImmersion

/-! # Affine localization of proper closed exchange

Source: Stacks Project, Tag 07A7, localization of the canonical exchange mate.
(blueprint: lem-sp-original-coefficient-closed-exchange-affine-local)
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

/-- Invertibility of proper closed exchange is local on the target.
Source: Stacks Project, Tag 07A7, and the localization calculation of the current
blueprint, def-exchange-projection.
(blueprint: lem-sp-original-coefficient-closed-exchange-affine-local)

Proof plan: pull the affine-open cover of the target and the complementary open
back along the proper and closed maps.  Properness, closedness and quasi-compactness
are obtained with `MorphismProperty.of_isPullback`; the range identity uses
`Scheme.Pullback.range_snd` and `IsPullback.isoPullback_inv_snd`.  The unit pulls
back along section rings, and constructibility pulls back along the proper map.
The remaining mate-coherence step identifies the arbitrary pullback square in
`condensed_closed_exchange_affine_descent` with the canonical affine square, then
uses the exact-single and total-derived comparisons and cover conservativity.
This final transport is left as the named theorem below because its proof requires
the open-restriction mate coherence interface. -/
theorem originalCoefficientClosedExchangeAffineLocal
    (ell : ℕ)
    (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj R] [IsCommMonObj R]
    (haff : ∀ (Y : Scheme.{u}) [IsAffine Y], IsUnit (ell : Γ(Y, ⊤)) →
      ∀ (X C : Scheme.{u}) (f : X ⟶ Y) [IsProper f]
        (i : C ⟶ Y) [IsClosedImmersion i],
        (∃ (U : Scheme.{u}) (j : U ⟶ Y),
          IsOpenImmersion j ∧ QuasiCompact j ∧
            Set.range i.base = (Set.range j.base)ᶜ) →
        ∀ (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
          (condensedRingObj R X)),
          IsConstructibleModuleObject (condensedRingObj R X) M →
          IsIso ((refinementAmbientExchange R
      (g' := pullback.fst f i) (f' := pullback.snd f i)
      (f := f) (g := i)
      { w := pullback.condition
        isoPullback := Iso.refl _
        hom_fst := Category.id_comp _
        hom_snd := Category.id_comp _ }).app
      ((DerivedCategory.singleFunctor _ 0).obj M)))
    (S : Scheme.{u}) (hell : IsUnit (ell : Γ(S, ⊤)))
    {X Y C : Scheme.{u}} (s : Y ⟶ S)
    (f : X ⟶ Y) [IsProper f] (i : C ⟶ Y) [IsClosedImmersion i]
    (hc : ∃ (U : Scheme.{u}) (j : U ⟶ Y),
      IsOpenImmersion j ∧ QuasiCompact j ∧ Set.range i.base = (Set.range j.base)ᶜ)
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj R X))
    (hM : IsConstructibleModuleObject (condensedRingObj R X) M) :
    IsIso ((refinementAmbientExchange R
      (g' := pullback.fst f i) (f' := pullback.snd f i)
      (f := f) (g := i)
      { w := pullback.condition
        isoPullback := Iso.refl _
        hom_fst := Category.id_comp _
        hom_snd := Category.id_comp _ }).app
      ((DerivedCategory.singleFunctor _ 0).obj M)) := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
