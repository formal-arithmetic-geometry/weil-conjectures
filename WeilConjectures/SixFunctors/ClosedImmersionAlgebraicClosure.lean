/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.TwoColimit.Filtered
public import WeilConjectures.SixFunctors.ClosedImmersionStages
public import WeilConjectures.SixFunctors.Etale.Derived.AlgebraicClosureLowerStar

/-!
# The closed-immersion unit at the coefficient stage `ℚ̄_ℓ`

Blueprint `def-weil-algebraically-closed-coefficients` defines `Dᵇc(Y, ℚ̄_ℓ)` as the category `𝒞_Y`
whose objects are pairs `(E, K)` with `E ⊆ ℚ̄_ℓ` a finite extension of `ℚ_ℓ` and
`K ∈ Dᵇc(Y, E)`, and whose morphisms are

`Hom((E, K), (E', K')) = colim_{L ⊇ E, E'} Hom_{Dᵇc(Y, L)}(K ⊗_E L, K' ⊗_{E'} L)`.

This is `AlgebraicGeometry.Etale.DerivedCategoryBoundedConstructibleAlgebraicClosure`, the
common-stage category (`CategoryTheory.TwoColimitData.Obj`) of the directed system of rational
stages `D_comp(Y_ét, E)` (`AlgebraicGeometry.Etale.algebraicClosureStageData`), with transition
functors `K ↦ K ⊗_E L` realised by derived coextension of scalars along `𝒪_E → 𝒪_L`
(`AlgebraicGeometry.Etale.rationalStageTransition`), restricted to the objects of `Dᵇc(Y, E)`.

For a closed immersion `i : Z ⟶ X`, `Ri_*` commutes with the transition functors compatibly with
their composition (`AlgebraicGeometry.Etale.rationalLowerStarTransitionIso_hexagon`), so it induces
`i_* : Dᵇc(Z, ℚ̄_ℓ) ⥤ Dᵇc(X, ℚ̄_ℓ)`
(`AlgebraicGeometry.Etale.algebraicClosureLowerStar`). Its action on morphisms is the filtered
colimit of the bijections given by the rational stage
(`AlgebraicGeometry.Etale.full_boundedConstructibleRationalLowerStar`), hence it is fully faithful:
blueprint `prop-sf-closed-unit-all-stages` at the stage `ℚ̄_ℓ`.

## Implementation notes

The morphisms of `𝒞_Y` are taken in the rational stages `D_comp(Y_ét, L)`, of which `Dᵇc(Y, L)` is
a full subcategory, so they are the blueprint's morphisms. The transition functors are
coextension of scalars, which for the finite free `𝒪_E`-algebra `𝒪_L` is the base change
`− ⊗_{𝒪_E} 𝒪_L` up to the inverse different, an invertible `𝒪_L`-module.
-/

@[expose] public section

universe u

open CategoryTheory

namespace PadicAlgCl

variable (l : ℕ) [Fact l.Prime] (E : Type) [Field E] [Algebra E (PadicAlgCl l)] [Algebra ℚ_[l] E]
  [IsScalarTower ℚ_[l] E (PadicAlgCl l)]

/-- The prime `ℓ` lies in the maximal ideal of `𝒪_E`. -/
lemma natCast_mem_maximalIdeal_integers :
    ((l : ℕ) : integers l E) ∈ IsLocalRing.maximalIdeal (integers l E) := by
  have hl : ‖(l : ℚ_[l])‖₊ < 1 := by
    rw [← NNReal.coe_lt_coe, coe_nnnorm, Padic.norm_p]
    exact inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : l.Prime).one_lt)
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  rintro ⟨u, hu⟩
  have h := u.mul_inv
  rw [hu] at h
  set y : integers l E := ((u⁻¹ : (integers l E)ˣ) : integers l E)
  have hy : valuationOfAlgebra l E (y : E) ≤ 1 := y.2
  have h' : valuationOfAlgebra l E (((l : ℕ) : integers l E) * (y : E)) = 1 := by
    simpa using congrArg (fun z : integers l E ↦ valuationOfAlgebra l E (z : E)) h
  rw [map_mul] at h'
  have hl' : valuationOfAlgebra l E (((l : ℕ) : integers l E) : E) = ‖(l : ℚ_[l])‖₊ := by
    rw [← valuationOfAlgebra_algebraMap l E]
    simp
  rw [hl'] at h'
  have : ‖(l : ℚ_[l])‖₊ * valuationOfAlgebra l E (y : E) < 1 :=
    lt_of_le_of_lt (mul_le_of_le_one_right' hy) hl
  exact this.ne h'

end PadicAlgCl

namespace AlgebraicGeometry.Etale

open PadicAlgCl PadicAlgCl.FiniteSubext

variable (l : ℕ) [Fact l.Prime]

instance : IsDirected (FiniteSubext l) (· ≤ ·) := ⟨exists_ge⟩

/-- The small étale site of a scheme is essentially small. Instance search does not find this
in the presence of the imports of this file. -/
local instance (X : Scheme.{u}) : EssentiallySmall.{u + 1} X.Etale :=
  have : LocallySmall.{u + 1} X.Etale :=
    @locallySmall_of_univLE X.Etale _ (@univLE_of_max.{u, u + 1} UnivLE.self)
  essentiallySmall_of_small_of_locallySmall _

/-- The exponent of the residue field of `𝒪_E` is invertible on `X` when `ℓ` is. -/
lemma hasInvertibleExponent_residueField {X : Scheme.{u}} (hl : IsUnit ((l : ℕ) : Γ(X, ⊤)))
    (E : FiniteSubext l) :
    HasInvertibleExponent (Shrink.{u + 1} (integers l E.field) ⧸
      maximalIdealShrink.{0, u} l E.field) X :=
  ⟨⟨l, (Fact.out : l.Prime).pos, by
    rw [← map_natCast (Ideal.Quotient.mk _), Ideal.Quotient.eq_zero_iff_mem,
      maximalIdealShrink, ← map_natCast (shrinkRingEquiv l E.field)]
    exact Ideal.mem_map_of_mem _ (natCast_mem_maximalIdeal_integers l E.field), hl⟩⟩

/-- The directed system of rational coefficient stages `D_comp(Y_ét, E)`, `E ⊆ ℚ̄_ℓ` finite over
`ℚ_ℓ`, with the transition functors `K ↦ K ⊗_E L`. -/
noncomputable def algebraicClosureStageData (Y : Scheme.{u}) : TwoColimitData (FiniteSubext l) where
  C E := DerivedCategoryDerivedCompleteRational Y.smallEtaleTopology l E.field
  T h := rationalStageTransition Y h
  comp h h' := rationalStageTransitionComp Y h h'
  cocycle h h' h'' := rationalStageTransitionComp_cocycle Y h h' h''

/-- Blueprint `def-weil-algebraically-closed-coefficients`: the coefficient stage
`Dᵇc(Y, ℚ̄_ℓ)`, the category of pairs `(E, K)` with `K ∈ Dᵇc(Y, E)`, morphisms being represented
over a common finite extension `L ⊇ E, E'` of `ℚ_ℓ` after the transition functors `− ⊗_E L`. -/
abbrev DerivedCategoryBoundedConstructibleAlgebraicClosure (Y : Scheme.{u}) :=
  (algebraicClosureStageData l Y).Obj
    (fun E ↦ DerivedCategory.boundedConstructibleRational l E.field Y)

variable {l} {Z X : Scheme.{u}}

/-- The direct image `Rf_*` as a morphism of the directed systems of rational stages. -/
noncomputable def algebraicClosureLowerStarMorphism (f : Z ⟶ X) :
    (algebraicClosureStageData l Z).Morphism (algebraicClosureStageData l X) where
  F E := rationalStageLowerStar f E
  κ h := rationalLowerStarTransitionIso f h
  hexagon h h' := rationalLowerStarTransitionIso_hexagon f h h'

variable (i : Z ⟶ X) [IsClosedImmersion i] {k : Type u} [Field k] (aX : X ⟶ Spec (.of k))
  [LocallyOfFiniteType aX] [QuasiCompact aX] (hl : IsUnit ((l : ℕ) : Γ(X, ⊤)))

include aX hl in
/-- Blueprint `prop-sf-closed-unit-all-stages`, stage `ℚ̄_ℓ`: the direct image
`i_* : Dᵇc(Z, ℚ̄_ℓ) ⥤ Dᵇc(X, ℚ̄_ℓ)` along a closed immersion, induced by the direct images at the
rational stages `E`. -/
noncomputable def algebraicClosureLowerStar :
    DerivedCategoryBoundedConstructibleAlgebraicClosure l Z ⥤
      DerivedCategoryBoundedConstructibleAlgebraicClosure l X :=
  (algebraicClosureLowerStarMorphism i).functor (fun E _ hK ↦
    have := hasInvertibleExponent_residueField l hl E
    Etale.boundedConstructibleRational_rightDerivedLowerStar_of_isClosedImmersion i aX l
      E.field hK)

instance (E : FiniteSubext l) : ((algebraicClosureLowerStarMorphism (l := l) i).F E).Full :=
  inferInstanceAs (Etale.rightDerivedLowerStarDerivedCompleteRational l E.field i).Full

instance (E : FiniteSubext l) : ((algebraicClosureLowerStarMorphism (l := l) i).F E).Faithful :=
  inferInstanceAs (Etale.rightDerivedLowerStarDerivedCompleteRational l E.field i).Faithful

/-- Blueprint `prop-sf-closed-unit-all-stages`, stage `ℚ̄_ℓ`: `i_*` is fully faithful on
`Dᵇc(-, ℚ̄_ℓ)`. Its action on morphisms is the filtered colimit over the finite extensions `L` of
the bijections given by the rational stages
(`AlgebraicGeometry.Etale.full_rightDerivedLowerStarDerivedCompleteRational`). -/
instance full_algebraicClosureLowerStar : (algebraicClosureLowerStar i aX hl).Full := by
  unfold algebraicClosureLowerStar
  infer_instance

instance faithful_algebraicClosureLowerStar : (algebraicClosureLowerStar i aX hl).Faithful := by
  unfold algebraicClosureLowerStar
  infer_instance

/-- Blueprint `prop-sf-closed-unit-all-stages`, the unit at the stage `ℚ̄_ℓ`: for any right
adjoint `Ri^!` of `i_* : Dᵇc(Z, ℚ̄_ℓ) ⥤ Dᵇc(X, ℚ̄_ℓ)`, the unit `Q ⟶ Ri^! i_* Q` is an
isomorphism. -/
theorem isIso_unit_app_algebraicClosureLowerStar
    {G : DerivedCategoryBoundedConstructibleAlgebraicClosure l X ⥤
      DerivedCategoryBoundedConstructibleAlgebraicClosure l Z}
    (adj : algebraicClosureLowerStar i aX hl ⊣ G)
    (Q : DerivedCategoryBoundedConstructibleAlgebraicClosure l Z) :
    IsIso (adj.unit.app Q) :=
  inferInstance

end AlgebraicGeometry.Etale
