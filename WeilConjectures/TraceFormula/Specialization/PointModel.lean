/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.NearbyCycles.BoundedConstructibleExchange
public import WeilConjectures.TraceFormula.Specialization.NearbyCycles
public import WeilConjectures.TraceFormula.Specialization.TraitDirectImageUnit
public import WeilConjectures.TraceFormula.Specialization.TraitHigherDirectImage
public import WeilConjectures.CategoryTheory.DerivedCategory.AdjunctionUnitSingle

/-!

# Nearby cycles of the trait itself

The trait `S = Spec k'⟦t⟧` is a model of the base point `Spec k` with special fibre `Spec k'`
(`ProEtale.CondensedRing.traitModel`): its geometric generic fibre `Spec Ω` maps to `Spec k`.
Its nearby cycles `Ψ_s` on bounded constructible complexes
(`ProEtale.CondensedRing.traitSpecialization`) are the target of the dualizing maps
`θ_X : Ψ_X ω_X ⟶ ω_{X'}`, which are read through the specialization unit `σ_s : ℚ̄_ℓ ⟶ Ψ_s ℚ̄_ℓ`
(`ProEtale.CondensedRing.traitSpecializationUnit`).

## Implementation notes

Nothing uses these declarations yet. They are the base point of the compact-support exchange
`ν_{a_X}` of the structure map `a_X : X ⟶ Spec k`, which builds the dualizing maps `θ_X` from the
exceptional exchange `β_{a_X}` (`ProEtale.CondensedRing.dualizingExchange` takes `σ_s` as a
parameter). Reading `θ_X` through `σ_s⁻¹` needs `σ_s` to be an isomorphism. This is the point
case of blueprint `det-sp-constant-family-vanishing` and is not formalised: it needs the
pro-étale computation `i^* Rj_* ℚ̄_ℓ ≅ ℚ̄_ℓ` over the strictly henselian trait.

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (k : Type u) [Field k] (k' : Type u) [Field k'] [Algebra k k']

/-- The trait `S = Spec k'⟦t⟧` as a model of the base point `Spec k` with special fibre
`Spec k'`: the geometric generic point `Spec Ω ⟶ S`, the closed point `Spec k' ⟶ S`, and the
structure map `Spec Ω ⟶ Spec k`. -/
noncomputable def traitModel : NearbyCyclesModel (point k).left (point k').left where
  total := trait k'
  generic := Spec (.of (traitGenericField k'))
  j := traitGenericPoint k'
  i := traitClosedPoint k'
  ε := Spec.map (CommRingCat.ofHom ((algebraMap (PowerSeries k') (traitGenericField k')).comp
    (algebraMap k (PowerSeries k'))))

/-- The trait is a model of finite type over itself. -/
theorem isTraitModel_traitModel : (traitModel k k').IsTraitModel := by
  have : IsIso (point k').hom := inferInstanceAs (IsIso (𝟙 _))
  exact ⟨⟨𝟙 _, 𝟙 _, inferInstance, inferInstance, inferInstance,
    IsPullback.of_vert_isIso ⟨by simp [traitModel]⟩,
    IsPullback.of_vert_isIso ⟨by simp [traitModel]⟩⟩⟩

variable {ℓ : ℕ} [Fact ℓ.Prime] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
  [IsSepClosed k'] [Fact (ringChar k').Prime] [Fact (ringChar k' ≠ ℓ)]

/-- The nearby cycles `Ψ_s : Dᵇc(Spec k) ⥤ Dᵇc(Spec k')` of the trait. -/
noncomputable def traitSpecialization :
    Dᵇc((point k).left)⟦Profinite.padicAlgClRingObj ℓ⟧ ⥤
      Dᵇc((point k').left)⟦Profinite.padicAlgClRingObj ℓ⟧ :=
  NearbyCyclesModel.boundedConstructibleNearbyCycles
    ((traitModel k k').preservesBoundedConstructible_of_isTraitModel (ℓ := ℓ)
      (isTraitModel_traitModel k k'))

/-- The specialization unit `σ_s : ℚ̄_ℓ ⟶ Ψ_s ℚ̄_ℓ` of the trait. -/
noncomputable def traitSpecializationUnit :
    𝟙_ _ ⟶ (traitSpecialization k k' (ℓ := ℓ)).obj (𝟙_ _) :=
  NearbyCyclesModel.boundedConstructibleUnit ℓ _

/-- For the strictly henselian trait `S = Spec k'⟦t⟧`, the specialization unit
`σ_s : ℚ̄_ℓ ⟶ Ψ_s ℚ̄_ℓ = i^* Rj_* ℚ̄_ℓ` is an isomorphism: the cohomology of the geometric
generic point of `S` is that of its closed point. This is the case `Y = Spec k'`, `L = ℚ̄_ℓ` of
blueprint `det-sp-constant-family-vanishing`. -/
theorem isIso_traitSpecializationUnit : IsIso (traitSpecializationUnit k k' (ℓ := ℓ)) :=
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
