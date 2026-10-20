/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NK
-/
module

public import Sheaf.AlgebraicGeometry.DerivedCategories
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
public import Sheaf.AlgebraicGeometry.BaseChangeInverseImageIso
public import Sheaf.AlgebraicGeometry.BaseChangeMapAbelianAndSets
public import Sheaf.AlgebraicGeometry.ExactUnboundedExchange
public import Sheaf.AlgebraicGeometry.CumulativeUniversalBaseChangeProperty

/-!
# The unbounded cumulative universal base-change property

Source: literature/blueprint/master/blueprint/sec-smooth-purity/
`sk-prop-sf-kunneth-ordinary/def-kun-bc-property.md`, node `def-kun-bc-property`,
order 1669 (blueprint: def-kun-bc-property).

For a morphism of schemes, this definition requires the unbounded derived exchange map
for every base change, every quasi-compact quasi-separated morphism over the new base,
and every sheaf of `Z/nZ`-modules, to be an isomorphism in every integer
degree at most the prescribed bound.  The pullbacks are the canonical scheme pullbacks.
-/

@[expose] public section

universe u

open CategoryTheory
open CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

/-- The cumulative universal base-change property `BC(f,n,q₀)` from the blueprint.
For every base change `S' ⟶ S` of `f`, every quasi-compact and quasi-separated
`g : T ⟶ S'`, and every sheaf `F` of `ULift (ZMod n)`-modules,
the cohomology map of the unbounded exchange from
`D(f') Rg_* F[0]` to `Rh_* D(e) F[0]` is an isomorphism in each integer degree
`q ≤ q₀`. Here `f'` and the two projections are formed by the canonical pullbacks.
A `ZMod n`-module sheaf is precisely an abelian sheaf annihilated by `n`: its scalar
action is the unique action induced by integer multiplication. The `ULift` only
implements the coefficient universe convention. No invertibility of `n` is assumed.
Source: literature/blueprint/master/blueprint/sec-smooth-purity/
`sk-prop-sf-kunneth-ordinary/def-kun-bc-property.md`, node `def-kun-bc-property`,
order 1669 (blueprint: def-kun-bc-property). -/
noncomputable def UnboundedCumulativeUniversalBaseChangeProperty {X S : Scheme.{u}}
    (f : X ⟶ S) (n : ℕ) (_hn : 0 < n) (q₀ : ℕ) : Prop :=
  ∀ (S' : Scheme.{u}) (a : S' ⟶ S) (T : Scheme.{u}) (g : T ⟶ S')
    [QuasiCompact g] [QuasiSeparated g]
    (F : Sheaf T.smallEtaleTopology
      (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod n))))
    (q : ℤ),
    q ≤ (q₀ : ℤ) →
      IsIso ((DerivedCategory.homologyFunctor
        (Sheaf (pullback f a).smallEtaleTopology
          (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod n)))) q).map
        ((exactDerivedBaseChangeMap
          (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod n)))
          (IsPullback.of_hasPullback (pullback.snd f a) g).flip.toCommSq).app
          ((DerivedCategory.singleFunctor
            (Sheaf T.smallEtaleTopology
              (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod n)))) 0).obj F)))

end AlgebraicGeometry.Etale
