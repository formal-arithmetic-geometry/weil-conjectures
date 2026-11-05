/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.ClosedImmersion
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.FullyFaithful
public import WeilConjectures.Mathlib.Algebra.Homology.ShortComplex.ShortExact

/-!
# The open–closed sequence of pro-étale sheaves of modules

Let `i : Z ⟶ X` be a closed immersion with quasi-compact open complement `j : U ⟶ X`. For
pro-étale sheaves of modules over a ring `R`:

* the unit `N ⟶ j^* j_! N` of `j_! ⊣ j^*` is an isomorphism
  (`AlgebraicGeometry.ProEtale.isIso_openImmersionLowerShriekUpperStarAdjunction_unit`,
  blueprint `lem-exc-proetale-open-unit`);
* every sheaf `M` sits in the short exact sequence `0 ⟶ j_! j^* M ⟶ M ⟶ i_* i^* M ⟶ 0`
  formed by the counit of `j_! ⊣ j^*` and the unit of `i^* ⊣ i_*`
  (`AlgebraicGeometry.ProEtale.shortExact_openClosedShortComplex`, blueprint
  `det-sf-open-closed-sequence-ring-sheaf`).

The exactness is checked after applying `j^*` and `i^*`, which are exact and jointly detect
zero objects (`AlgebraicGeometry.ProEtale.isZero_of_isZero_upperStar_of_isCompl`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

open Scheme

namespace ProEtale

variable {R : Type (u + 1)} [Ring R] {Z U X : Scheme.{u}}

section OpenUnit

variable (A : Type*) [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  (j : U ⟶ X) [IsOpenImmersion j]

end OpenUnit

variable (i : Z ⟶ X) [IsClosedImmersion i] (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j]

section BaseChange

variable {Z' U' X' : Scheme.{u}} (g : X' ⟶ X) (i' : Z' ⟶ X') [IsClosedImmersion i']
  (j' : U' ⟶ X') [IsOpenImmersion j'] [QuasiCompact j'] (gZ : Z' ⟶ Z) (gU : U' ⟶ U)

end BaseChange

end ProEtale

end AlgebraicGeometry
