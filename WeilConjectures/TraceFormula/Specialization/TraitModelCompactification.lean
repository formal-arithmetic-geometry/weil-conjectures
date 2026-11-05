/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.FlatDescent
public import Mathlib.RingTheory.LaurentSeries
public import WeilConjectures.Compactification.NagataCompactification
public import WeilConjectures.TraceFormula.Specialization.NearbyDualizingMap

/-!

# Compactification of trait models over the base

Let `S = Spec k'⟦t⟧` be the trait. Its generic point is the open immersion
`Spec K ⟶ S` with `K = Frac k'⟦t⟧ = k'⟦t⟧[1/t]` (`AlgebraicGeometry.traitGenericSpec`), through
which the geometric generic point `Spec Ω ⟶ S` factors by a faithfully flat morphism.

Every trait model `M` of `X` over the base (`NearbyCyclesModel.IsTraitModelOfBase`) is an open
sub-model of a trait model over the base with proper total space, proper `X̄` and proper special
fibre `X̄'` (`NearbyCyclesModel.IsTraitModelOfBase.exists_isProper_openSubmodel`). Construction:
let `X̄` be a Nagata compactification of `X` over `k` and `Z = X̄ ×_k S`; the morphism
`F = (e, q) : 𝒳 ⟶ Z` is an open immersion over the generic point of `S`, by fpqc descent
(Stacks 02L3) from the geometric generic fibre. A compactification of `F` which is an isomorphism
over the generic fibre `Z_K` (`AlgebraicGeometry.exists_isProper_isPullback_of_isOpenImmersion`)
is the total space of the required model; its geometric generic fibre is `X̄ ×_k Spec Ω`.

-/

@[expose] public section

universe u

open CategoryTheory Limits MorphismProperty

namespace AlgebraicGeometry

section TraitGeneric

variable (k' : Type u) [Field k']

/-- The field of fractions of `k'⟦t⟧` is its localization away from `t`. -/
instance isLocalization_away_X_fractionRing_powerSeries :
    IsLocalization.Away (PowerSeries.X : PowerSeries k') (FractionRing (PowerSeries k')) :=
  IsLocalization.isLocalization_of_algEquiv (M := Submonoid.powers PowerSeries.X)
    (FractionRing.algEquiv (PowerSeries k') (LaurentSeries k')).symm

/-- The generic point `Spec K ⟶ Spec k'⟦t⟧` of the trait, `K = Frac k'⟦t⟧`: an open immersion. -/
noncomputable def traitGenericSpec : Spec (.of (FractionRing (PowerSeries k'))) ⟶ trait k' :=
  Spec.map (CommRingCat.ofHom (algebraMap (PowerSeries k') (FractionRing (PowerSeries k'))))

instance : IsOpenImmersion (traitGenericSpec k') :=
  IsOpenImmersion.of_isLocalization (PowerSeries.X : PowerSeries k')

/-- The geometric generic point `Spec Ω ⟶ Spec K` over the generic point of the trait. -/
noncomputable def traitGenericPointToSpec :
    Spec (.of (traitGenericField k')) ⟶ Spec (.of (FractionRing (PowerSeries k'))) :=
  Spec.map (CommRingCat.ofHom
    (algebraMap (FractionRing (PowerSeries k')) (traitGenericField k')))

@[reassoc]
lemma traitGenericPointToSpec_traitGenericSpec :
    traitGenericPointToSpec k' ≫ traitGenericSpec k' = traitGenericPoint k' := by
  rw [traitGenericPointToSpec, traitGenericSpec, traitGenericPoint, ← Spec.map_comp,
    ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq]

end TraitGeneric

namespace ProEtale.CondensedRing.NearbyCyclesModel

variable {k : Type u} [Field k] {k' : Type u} [Field k'] [Algebra k k']

end ProEtale.CondensedRing.NearbyCyclesModel

end AlgebraicGeometry
