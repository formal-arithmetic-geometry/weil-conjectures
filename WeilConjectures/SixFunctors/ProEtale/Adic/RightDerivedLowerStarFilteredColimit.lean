/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.CategoryTheory.Limits.Constructions.Filtered
public import WeilConjectures.SixFunctors.ProEtale.Adic.ForgetAbRightDerivedLowerStar

/-!
# Higher direct images commute with filtered colimits and direct sums

For a quasi-compact quasi-separated morphism of schemes `f : X ⟶ Y`, the higher direct images
`Rᵠf_*` of abelian sheaves on the small pro-étale sites commute with filtered colimits and with
direct sums (`AlgebraicGeometry.ProEtale.preservesColimitsOfShape_rightDerived_lowerStar`,
`AlgebraicGeometry.ProEtale.preservesColimitsOfShape_discrete_rightDerived_lowerStar`). This is
the complement of the blueprint node `sk-cor-pe-bounded-continuity` (for the constant ring sheaf
`ℤ`); only the filtered colimit statement, the case of complexes concentrated in degree `0` of
the blueprint node `det-pe-bounded-continuity-direct-image`, is stated here and not proved.

We deduce that `f_*` itself commutes with filtered colimits and direct sums
(`AlgebraicGeometry.ProEtale.preservesColimitsOfShape_lowerStar`,
`AlgebraicGeometry.ProEtale.preservesColimitsOfShape_discrete_lowerStar`) and that filtered
colimits and direct sums of `f_*`-acyclic sheaves are `f_*`-acyclic
(`AlgebraicGeometry.ProEtale.rightAcyclic_lowerStar_of_isColimit`,
`AlgebraicGeometry.ProEtale.rightAcyclic_lowerStar_of_isColimit_discrete`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.ProEtale

open Scheme

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]

/-- **Higher direct images commute with filtered colimits** (blueprint
`det-pe-bounded-continuity-direct-image`, sub-node of `sk-cor-pe-bounded-continuity`, in the case
of complexes concentrated in degree `0` and of the ring sheaf `ℤ`): for a quasi-compact
quasi-separated morphism `f` and a filtered diagram `(Kᵢ)` of abelian sheaves on `X_proét`, the
canonical map `colim Rᵠf_* Kᵢ ⟶ Rᵠf_* (colim Kᵢ)` is an isomorphism. Proof sketch:
`Rᵠf_* M` is the sheafification of `V ↦ Hᵠ(X ×_Y V, M)`, and for affine `V` the scheme
`X ×_Y V` is quasi-compact and quasi-separated, so that its cohomology is computed by a
hypercovering by affine weakly contractible objects, whose sections commute with filtered
colimits. -/
theorem preservesColimitsOfShape_rightDerived_lowerStar (J : Type) [SmallCategory J]
    [IsFiltered J] (q : ℕ) :
    PreservesColimitsOfShape J (((f)_*[Ab.{u + 1}]).rightDerived q) := by
  sorry

/-- **Higher direct images commute with direct sums**: for a quasi-compact
quasi-separated morphism `f`, each `Rᵠf_*` on abelian sheaves on `X_proét` commutes with direct
sums: a direct sum is the filtered colimit of its finite subsums, and `Rᵠf_*` preserves
finite direct sums, being additive, and filtered colimits
(`AlgebraicGeometry.ProEtale.preservesColimitsOfShape_rightDerived_lowerStar`). -/
theorem preservesColimitsOfShape_discrete_rightDerived_lowerStar (B : Type) (q : ℕ) :
    PreservesColimitsOfShape (Discrete B) (((f)_*[Ab.{u + 1}]).rightDerived q) :=
  have := preservesColimitsOfShape_rightDerived_lowerStar f (Finset (Discrete B)) q
  preservesColimitsOfShape_discrete_of_preservesFiniteCoproducts _

/-- For a quasi-compact quasi-separated morphism `f`, the pushforward `f_*` of abelian sheaves on
the small pro-étale sites commutes with direct sums. -/
theorem preservesColimitsOfShape_discrete_lowerStar (B : Type) :
    PreservesColimitsOfShape (Discrete B) (f)_*[Ab.{u + 1}] :=
  have := preservesColimitsOfShape_discrete_rightDerived_lowerStar f B 0
  preservesColimitsOfShape_of_natIso ((f)_*[Ab.{u + 1}]).rightDerivedZeroIsoSelf

/-- For a quasi-compact quasi-separated morphism `f`, a direct sum of `f_*`-acyclic abelian
sheaves is `f_*`-acyclic. -/
lemma rightAcyclic_lowerStar_of_isColimit_discrete {B : Type}
    {D : Discrete B ⥤ Sheaf (ProEt.topology X) Ab.{u + 1}} {c : Cocone D} (hc : IsColimit c)
    (hD : ∀ j, ((f)_*[Ab.{u + 1}]).rightAcyclic (D.obj j)) :
    ((f)_*[Ab.{u + 1}]).rightAcyclic c.pt := fun q ↦
  have := preservesColimitsOfShape_discrete_rightDerived_lowerStar f B (q + 1)
  (isColimitOfPreserves (((f)_*[Ab.{u + 1}]).rightDerived (q + 1)) hc).isZero_pt
    (Functor.isZero _ fun j ↦ hD j q)

/-- For a quasi-compact quasi-separated morphism `f`, the pushforward `f_*` of abelian sheaves on
the small pro-étale sites commutes with filtered colimits. -/
theorem preservesColimitsOfShape_lowerStar (J : Type) [SmallCategory J] [IsFiltered J] :
    PreservesColimitsOfShape J (f)_*[Ab.{u + 1}] :=
  have := preservesColimitsOfShape_rightDerived_lowerStar f J 0
  preservesColimitsOfShape_of_natIso ((f)_*[Ab.{u + 1}]).rightDerivedZeroIsoSelf

/-- For a quasi-compact quasi-separated morphism `f`, a filtered colimit of `f_*`-acyclic abelian
sheaves is `f_*`-acyclic. -/
lemma rightAcyclic_lowerStar_of_isColimit {J : Type} [SmallCategory J] [IsFiltered J]
    {D : J ⥤ Sheaf (ProEt.topology X) Ab.{u + 1}} {c : Cocone D} (hc : IsColimit c)
    (hD : ∀ j, ((f)_*[Ab.{u + 1}]).rightAcyclic (D.obj j)) :
    ((f)_*[Ab.{u + 1}]).rightAcyclic c.pt := fun q ↦
  have := preservesColimitsOfShape_rightDerived_lowerStar f J (q + 1)
  (isColimitOfPreserves (((f)_*[Ab.{u + 1}]).rightDerived (q + 1)) hc).isZero_pt
    (Functor.isZero _ fun j ↦ hD j q)

end AlgebraicGeometry.ProEtale
