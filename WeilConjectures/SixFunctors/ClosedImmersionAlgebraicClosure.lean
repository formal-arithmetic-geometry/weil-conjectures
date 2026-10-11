/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.TwoColimit.Filtered
public import WeilConjectures.SixFunctors.ClosedImmersionStages
public import WeilConjectures.SixFunctors.Etale.Derived.AlgebraicClosureBaseChange
public import WeilConjectures.SixFunctors.Etale.Derived.AlgebraicClosureLowerStar

/-!
# The closed-immersion unit at the coefficient stage `ℚ̄_ℓ`

Blueprint `def-weil-algebraically-closed-coefficients` defines `Dᵇc(Y, ℚ̄_ℓ)` as the category `𝒞_Y`
whose objects are pairs `(E, K)` with `E ⊆ ℚ̄_ℓ` a finite extension of `ℚ_ℓ` and
`K ∈ Dᵇc(Y, E)`, and whose morphisms are

`Hom((E, K), (E', K')) = colim_{L ⊇ E, E'} Hom_{Dᵇc(Y, L)}(K ⊗_E L, K' ⊗_{E'} L)`.

This is `AlgebraicGeometry.Etale.DerivedCategoryBoundedConstructibleAlgebraicClosure`, the
common-stage category (`CategoryTheory.TwoColimitData.Obj`) of the directed system
`AlgebraicGeometry.Etale.boundedConstructibleAlgebraicClosureStageData`: the full subcategories
`Dᵇc(Y, E)` of the rational stages `D_comp(Y_ét, E)`, with the scalar-extension functors
`− ⊗_E L` of blueprint `def-weil-rationalization-karoubi` as transition functors
(`AlgebraicGeometry.Etale.rationalBaseChangeTransition`: derived base change `− ⊗_{𝒪_E} 𝒪_L` of
integral representatives, followed by rationalization; no completion is needed, `𝒪_L` being finite
free over `𝒪_E`). Their composition isomorphisms are transported
(`CategoryTheory.TwoColimitData.transportIso`) from those of the isomorphic functors induced by
derived coextension of scalars (`AlgebraicGeometry.Etale.rationalBaseChangeTransitionIso`), for
which the coherence is proved by mate calculus. That `− ⊗_E L` preserves `Dᵇc` is
`AlgebraicGeometry.Etale.boundedConstructibleRational_rationalBaseChangeTransition`.

For a closed immersion `i : Z ⟶ X`, `Ri_*` commutes with the transition functors compatibly with
their composition (`AlgebraicGeometry.Etale.rationalLowerStarTransitionIso_hexagon`) and preserves
`Dᵇc`, so it induces `i_* : Dᵇc(Z, ℚ̄_ℓ) ⥤ Dᵇc(X, ℚ̄_ℓ)`
(`AlgebraicGeometry.Etale.algebraicClosureLowerStar`). Its action on morphisms is the filtered
colimit of the bijections given by the rational stages
(`AlgebraicGeometry.Etale.full_boundedConstructibleRationalLowerStar`), hence it is fully faithful:
blueprint `prop-sf-closed-unit-all-stages` at the stage `ℚ̄_ℓ`.
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

/-- The directed system of the rational stages `D_comp(Y_ét, E)` with the blueprint's
scalar-extension functors `− ⊗_E L` (`AlgebraicGeometry.Etale.rationalBaseChangeTransition`,
induced by derived base change `− ⊗_{𝒪_E} 𝒪_L` of integral representatives) as transition
functors, the composition isomorphisms being transported along
`AlgebraicGeometry.Etale.rationalBaseChangeTransitionIso`. -/
noncomputable abbrev baseChangeStageData (Y : Scheme.{u}) : TwoColimitData (FiniteSubext l) :=
  (algebraicClosureStageData l Y).transportIso (fun h ↦ rationalBaseChangeTransition Y h)
    (fun h ↦ rationalBaseChangeTransitionIso Y h)

/-- Unfinished (the remaining part of the first clause of blueprint
`prop-weil-pbc-scalar-extension`): the reductions modulo `𝔪_Lⁿ⁺¹` of the derived base change
`K ⊗_{𝒪_E} 𝒪_L` of an object of `Dᵇc(Y, 𝒪_E)` are bounded constructible of uniform Tor
amplitude. See the pull request for the attempts made. -/
theorem reductions_rightDerivedBaseChange (Y : Scheme.{u}) {E L : FiniteSubext l} (h : E ≤ L)
    (K : _root_.DerivedCategory
      (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} (Shrink.{u + 1} (integers l E.field)))))
    (hK : DerivedCategory.boundedConstructibleIntegral (maximalIdealShrink l E.field) Y K) :
    ∃ a b : ℤ, ∀ n : ℕ,
      DerivedCategory.boundedConstructible (ModuleCat.{u + 1} (Shrink.{u + 1} (integers l L.field)))
          Y ((reductionModIdeal _ Y (maximalIdealShrink l L.field ^ (n + 1))).obj
            ((sheafBaseChangeTransition Y h).rightDerivedFunctor.obj K)) ∧
        DerivedCategory.torAmplitudeIn (ModuleCat.{u + 1} (Shrink.{u + 1} (integers l L.field)))
          Y a b ((reductionModIdeal _ Y (maximalIdealShrink l L.field ^ (n + 1))).obj
            ((sheafBaseChangeTransition Y h).rightDerivedFunctor.obj K)) :=
  sorry

/-- Derived base change `− ⊗_{𝒪_E} 𝒪_L` maps `Dᵇc(Y, 𝒪_E)` into `Dᵇc(Y, 𝒪_L)`: derived
completeness is preserved, the base change being isomorphic to the derived coextension of
scalars, and the reductions are `reductions_rightDerivedBaseChange`. -/
theorem boundedConstructibleIntegral_rightDerivedBaseChange (Y : Scheme.{u})
    {E L : FiniteSubext l} (h : E ≤ L)
    (K : _root_.DerivedCategory
      (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} (Shrink.{u + 1} (integers l E.field)))))
    (hK : DerivedCategory.boundedConstructibleIntegral (maximalIdealShrink l E.field) Y K) :
    DerivedCategory.boundedConstructibleIntegral (maximalIdealShrink l L.field) Y
      ((sheafBaseChangeTransition Y h).rightDerivedFunctor.obj K) :=
  ⟨DerivedCategory.derivedComplete_of_iso ((derivedBaseChangeTransitionIso Y h).app K).symm
    (derivedCompleteIntegral_rightDerivedFunctor_coextendScalars l (incl h) (incl_compat h) Y hK.1),
    reductions_rightDerivedBaseChange l Y h K hK⟩

/-- The first clause of blueprint `prop-weil-pbc-scalar-extension`: the scalar-extension functor
`− ⊗_E L` maps `Dᵇc(Y, E)` into `Dᵇc(Y, L)`. An integral representative `K'` of `K` is carried
to the integral representative `K' ⊗_{𝒪_E} 𝒪_L` of `K ⊗_E L`. -/
theorem boundedConstructibleRational_rationalBaseChangeTransition (Y : Scheme.{u})
    {E L : FiniteSubext l} (h : E ≤ L)
    (K : DerivedCategoryDerivedCompleteRational Y.smallEtaleTopology l E.field)
    (hK : DerivedCategory.boundedConstructibleRational l E.field Y K) :
    DerivedCategory.boundedConstructibleRational l L.field Y
      ((rationalBaseChangeTransition Y h).obj K) := by
  obtain ⟨K', hK', ⟨e⟩⟩ := hK
  exact ⟨(integralBaseChangeTransition Y h).obj K',
    boundedConstructibleIntegral_rightDerivedBaseChange l Y h _ hK',
    ⟨((Localization.Lifting.iso
      (Rationalization.Q (nonZeroDivisors (Shrink.{u + 1} (integers l E.field)))
        (DerivedCategoryDerivedCompleteIntegral Y.smallEtaleTopology l E.field))
      (Rationalization.W (nonZeroDivisors (Shrink.{u + 1} (integers l E.field)))
        (DerivedCategoryDerivedCompleteIntegral Y.smallEtaleTopology l E.field))
      (integralBaseChangeTransition Y h ⋙
        Rationalization.Q (nonZeroDivisors (Shrink.{u + 1} (integers l L.field)))
          (DerivedCategoryDerivedCompleteIntegral Y.smallEtaleTopology l L.field))
      (rationalBaseChangeTransition Y h)).app K').symm ≪≫ (rationalBaseChangeTransition Y h).mapIso e⟩⟩

/-- The directed system of the categories `Dᵇc(Y, E)`, `E ⊆ ℚ̄_ℓ` finite over `ℚ_ℓ`, with the
transition functors `K ↦ K ⊗_E L` (`boundedConstructibleRational_rationalBaseChangeTransition`). -/
noncomputable def boundedConstructibleAlgebraicClosureStageData (Y : Scheme.{u}) :
    TwoColimitData (FiniteSubext l) :=
  (baseChangeStageData l Y).restrict
    (fun E ↦ DerivedCategory.boundedConstructibleRational l E.field Y)
    (fun h K hK ↦ boundedConstructibleRational_rationalBaseChangeTransition l Y h K hK)

/-- Blueprint `def-weil-algebraically-closed-coefficients`: the coefficient stage
`Dᵇc(Y, ℚ̄_ℓ) = 𝒞_Y`, the category of pairs `(E, K)` with `K ∈ Dᵇc(Y, E)`, whose morphisms
`(E, K) ⟶ (E', K')` are `colim_{L ⊇ E, E'} Hom_{Dᵇc(Y, L)}(K ⊗_E L, K' ⊗_{E'} L)`. -/
abbrev DerivedCategoryBoundedConstructibleAlgebraicClosure (Y : Scheme.{u}) :=
  (boundedConstructibleAlgebraicClosureStageData l Y).Obj (fun _ ↦ ⊤)

variable {l} {Z X : Scheme.{u}}

/-- The direct image `Rf_*` as a morphism of the directed systems of rational stages. -/
noncomputable def algebraicClosureLowerStarMorphism (f : Z ⟶ X) :
    (algebraicClosureStageData l Z).Morphism (algebraicClosureStageData l X) where
  F E := rationalStageLowerStar f E
  κ h := rationalLowerStarTransitionIso f h
  hexagon h h' := rationalLowerStarTransitionIso_hexagon f h h'

variable (i : Z ⟶ X) [IsClosedImmersion i] {k : Type u} [Field k] (aX : X ⟶ Spec (.of k))
  [LocallyOfFiniteType aX] [QuasiCompact aX] (hl : IsUnit ((l : ℕ) : Γ(X, ⊤)))

instance (E : FiniteSubext l) : ((algebraicClosureLowerStarMorphism (l := l) i).F E).Full :=
  inferInstanceAs (Etale.rightDerivedLowerStarDerivedCompleteRational l E.field i).Full

instance (E : FiniteSubext l) : ((algebraicClosureLowerStarMorphism (l := l) i).F E).Faithful :=
  inferInstanceAs (Etale.rightDerivedLowerStarDerivedCompleteRational l E.field i).Faithful

include i aX hl in
/-- The direct image `Ri_*` as a morphism of the directed systems of the categories `Dᵇc(-, E)`. -/
noncomputable def boundedConstructibleAlgebraicClosureLowerStarMorphism :
    (boundedConstructibleAlgebraicClosureStageData l Z).Morphism
      (boundedConstructibleAlgebraicClosureStageData l X) :=
  TwoColimitData.Morphism.restrict (D := baseChangeStageData l Z)
    (D' := baseChangeStageData l X)
    (Q := fun E ↦ DerivedCategory.boundedConstructibleRational l E.field Z)
    (hT := fun h K hK ↦ boundedConstructibleRational_rationalBaseChangeTransition l Z h K hK)
    (Φ := TwoColimitData.Morphism.transportIso (fun h ↦ rationalBaseChangeTransition Z h)
      (fun h ↦ rationalBaseChangeTransitionIso Z h) (algebraicClosureLowerStarMorphism (l := l) i)
      (fun h ↦ rationalBaseChangeTransition X h) (fun h ↦ rationalBaseChangeTransitionIso X h))
    (Q' := fun E ↦ DerivedCategory.boundedConstructibleRational l E.field X)
    (hT' := fun h K hK ↦ boundedConstructibleRational_rationalBaseChangeTransition l X h K hK)
    (hF := fun E _ hK ↦
    have := hasInvertibleExponent_residueField l hl E
    Etale.boundedConstructibleRational_rightDerivedLowerStar_of_isClosedImmersion i aX l
      E.field hK)

instance (E : FiniteSubext l) :
    ((boundedConstructibleAlgebraicClosureLowerStarMorphism i aX hl).F E).Full := by
  unfold boundedConstructibleAlgebraicClosureLowerStarMorphism
  exact @TwoColimitData.Morphism.full_restrict_F _ _ _ _ _ _ _ _ _ _
    (fun E ↦ inferInstanceAs ((algebraicClosureLowerStarMorphism (l := l) i).F E).Full) E

instance (E : FiniteSubext l) :
    ((boundedConstructibleAlgebraicClosureLowerStarMorphism i aX hl).F E).Faithful := by
  unfold boundedConstructibleAlgebraicClosureLowerStarMorphism
  exact @TwoColimitData.Morphism.faithful_restrict_F _ _ _ _ _ _ _ _ _ _
    (fun E ↦ inferInstanceAs ((algebraicClosureLowerStarMorphism (l := l) i).F E).Faithful) E

/-- Blueprint `prop-sf-closed-unit-all-stages`, stage `ℚ̄_ℓ`: the direct image
`i_* : Dᵇc(Z, ℚ̄_ℓ) ⥤ Dᵇc(X, ℚ̄_ℓ)` along a closed immersion, induced by the direct images
`i_* : Dᵇc(Z, E) ⥤ Dᵇc(X, E)` at the rational stages. -/
noncomputable def algebraicClosureLowerStar :
    DerivedCategoryBoundedConstructibleAlgebraicClosure l Z ⥤
      DerivedCategoryBoundedConstructibleAlgebraicClosure l X :=
  (boundedConstructibleAlgebraicClosureLowerStarMorphism i aX hl).functor fun _ _ _ ↦ trivial

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
