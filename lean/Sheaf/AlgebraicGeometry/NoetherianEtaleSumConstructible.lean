/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q05
-/
module

public import Sheaf.AlgebraicGeometry.FiniteLocallyClosedStratification
public import Sheaf.CategoryTheory.LocallyConstantFiniteTypeModules
public import Sheaf.CategoryTheory.RingedSiteModules
public import Mathlib.RingTheory.Noetherian.Defs
public import WeilConjectures.ConstructibleSheaf.Defs
public import WeilConjectures.SixFunctors.Etale.LowerShriek.EtaleMap
import WeilConjectures.AlgebraicGeometry.EtaleStratifiedFinite
import WeilConjectures.AlgebraicGeometry.EtaleLowerShriekBaseChangeModules
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FiniteEtale

/-!
# Constructibility of etale sum extension with Noetherian coefficients

Source: Stacks Project, Etale Cohomology, Tag 03S8, lemma-jshriek-constructible (3)
(blueprint: lem-per-noetherian-etale-sum-constructible).

The conclusion spells out the node's finite locally closed stratification criterion.
The coefficient ring and the finite-type coefficient module can have infinite underlying sets.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- The sum extension of a constant finitely generated module along an etale map between
quasi-compact quasi-separated schemes is locally constant of finite type on the members
of a finite locally closed stratification.
Source: Stacks Project, Tag 03S8, lemma-jshriek-constructible (3)
(blueprint: lem-per-noetherian-etale-sum-constructible).

Proof:
1. Apply `lem-weil-pbc-etale-stratified-finite` to obtain a finite constructible locally
   closed stratification on which the base change of `j` is finite etale.
2. On each stratum apply `lem-weil-pbc-etale-shriek-base-change-modules` and
   `lemma-constructible-pullback-constant`. The restriction of the sum extension identifies
   with the sum extension of the constant module along that finite etale base change.
3. Apply `lem-weil-pbc-etale-shriek-star-finite-modules` to replace this sum extension
   by the finite etale direct image of the same constant module.
4. The constant sheaf is locally constant of finite type because `M` is finitely generated.
   Apply `lem-per-finite-etale-pushforward-finite-type`; its local trivializations transfer
   across the preceding isomorphisms to give the required restrictions.
5. Assemble these restrictions on the finitely many disjoint locally closed strata,
   which cover `X`, as in `def-constructible-stratification`. The empty stratification
   handles empty `X`; zero modules handle strata with empty inverse image. Neither the
   ring nor the module has been assumed finite as a set. -/
theorem exists_noetherian_etale_sum_constructible
    {X U : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
    [CompactSpace U] [QuasiSeparatedSpace U] (j : U ⟶ X) [Etale j]
    (R : Type (u + 1)) [CommRing R] [IsNoetherianRing R]
    (M : ModuleCat.{u + 1} R) [Module.Finite R M] :
    ∃ S : FiniteLocallyClosedStratification X, ∀ i : Fin S.n,
      IsFiniteLocallyConstantSheaf
        ((Etale.upperStar (ModuleCat.{u + 1} R) (S.immersion i)).obj
          ((Etale.etaleLowerShriek (ModuleCat.{u + 1} R) j inferInstance).obj
            ((constantSheaf U.smallEtaleTopology (ModuleCat.{u + 1} R)).obj M))) := by
  sorry

end AlgebraicGeometry.Scheme
