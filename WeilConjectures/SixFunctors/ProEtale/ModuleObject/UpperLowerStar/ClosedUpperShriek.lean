/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Adjunction.Triple
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionEssImage
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.OpenClosed
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.ClosedImmersion
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Finite

/-!
# Sections with support and the exceptional inverse image along a closed immersion

Let `Λ` be a commutative condensed ring, `i : Z ⟶ X` a closed immersion and `j : U ⟶ X` an open
immersion onto the complement of its range. On module objects over `Λ_X = condensedRingObj Λ X`,
the sections with support in `Z` form the kernel

`Γ_Z N = ker(N ⟶ j_* j^* N)`

of the unit of `j^* ⊣ j_*` (`ProEtale.CondensedRing.sectionsWithSupport`), and
`i^!₀ N = i^* Γ_Z N` (`ProEtale.CondensedRing.closedUpperShriek`). It is right adjoint to the
pushforward `i_*` (`ProEtale.CondensedRing.lowerStarClosedUpperShriekAdjunction`). This is the
module-object counterpart of
`WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ClosedImmersion`, used for
blueprint `sk-lem-formal-closed-support`.

The adjunction is the composite of two adjunctions: a morphism `i_* P ⟶ N` is killed by the unit
`N ⟶ j_* j^* N` (since `j^* i_* P = 0`), so factors uniquely through `Γ_Z N`; and `Γ_Z N`,
which vanishes on `U`, is `i_* i^* Γ_Z N` (`i_*` is fully faithful with essential image the
module objects vanishing on `U`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]

section Definition

variable {Z U X : Scheme.{u}} (i : Z ⟶ X) (j : U ⟶ X)

/-- The counit `j^* j_* ⟶ 𝟭` of `j^* ⊣ j_*` on module objects along an open immersion is an
isomorphism: in the adjoint triple `j_! ⊣ j^* ⊣ j_*` the unit of the first adjunction is an
isomorphism. -/
lemma isIso_upperStarLowerStarAdjunction_counit_of_isOpenImmersion [IsOpenImmersion j] :
    IsIso (upperStarLowerStarAdjunction Λ j).counit :=
  (Adjunction.Triple.mk (openImmersionLowerShriekUpperStarAdjunction Λ j)
    (upperStarLowerStarAdjunction Λ j)).isIso_unit_iff_isIso_counit.1
    (inferInstance : IsIso (openImmersionLowerShriekUpperStarAdjunction Λ j).unit)

attribute [local instance] isIso_upperStarLowerStarAdjunction_counit_of_isOpenImmersion

end Definition

section Adjunction

variable {Z U X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] (j : U ⟶ X) [IsOpenImmersion j]
  [QuasiCompact j]

end Adjunction

end AlgebraicGeometry.ProEtale.CondensedRing
