/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Specialization.NearbyDualityGlobal
public import WeilConjectures.TraceFormula.Specialization.TraitModelOfGenericBase
public import WeilConjectures.TraceFormula.Specialization.TraitNearbyFiniteness

/-!

# The trait as a model of a generic base point

Let `S = Spec k'⟦t⟧` be the strictly henselian trait, `η = Spec Frac k'⟦t⟧` its generic point and
`ι : η ⟶ Spec F` a morphism to the spectrum of a field `F`. The trait is a model of the base point
`Spec F` with special fibre `Spec k'` (`ProEtale.CondensedRing.traitModelOfGenericBase`): its
geometric generic fibre `Spec Ω` maps to `Spec F` through `Spec Ω ⟶ η ⟶ Spec F`. It is a trait
model over the generic base `(F, Spec F)`
(`ProEtale.CondensedRing.isTraitModelOfGenericBase_traitModelOfGenericBase`). This is the analogue
for models over a generic base of the trait model of the base point
(`ProEtale.CondensedRing.traitModel`), which needs `F` to map into `k'⟦t⟧`.

* Its nearby cycles preserve bounded constructible complexes
  (`ProEtale.CondensedRing.preservesBoundedConstructible_traitModelOfGenericBase`): the pullback
  `Lε^* K` to `Spec Ω` is bounded constructible, and the nearby functor `Li^* Rj_*` of the trait
  carries bounded constructible complexes on `Spec Ω` to bounded constructible complexes
  (`ProEtale.CondensedRing.boundedConstructible_traitNearby_singleFunctor_obj`, by dévissage).
  Unlike `NearbyCyclesModel.preservesBoundedConstructible_of_isTraitModel`, this does not need `ε`
  to factor through the total space.
* Its specialization unit `σ : ℚ̄_ℓ ⟶ Ψ ℚ̄_ℓ` is an isomorphism
  (`ProEtale.CondensedRing.isIso_traitGenericSpecializationUnit`), as it only involves `j` and `i`.
* Its nearby cycles are monoidal (`NearbyCyclesModel.exists_monoidal_traitGenericSpecialization`),
  and its duality map with dualizing map `σ⁻¹` is an isomorphism
  (`NearbyCyclesModel.isIso_nearbyDualityMap_traitModelOfGenericBase`).

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory MonoidalClosed

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

-- `Dᵇc` is monoidal through `ObjectProperty.fullMonoidalSubcategory` everywhere, so that the
-- monoidal structures of concrete statements and of instantiated abstract ones agree syntactically.
attribute [-instance] monoidalCategory_boundedConstructible
  ObjectProperty.instMonoidalCategoryStructFullSubcategory

section Model

variable (F : Type u) [Field F] {k' : Type u} [Field k']
  (ι : Spec (.of (FractionRing (PowerSeries k'))) ⟶ Spec (.of F))

/-- The trait `S = Spec k'⟦t⟧` as a model of the base point `Spec F` with special fibre
`Spec k'`, for a morphism `ι : η ⟶ Spec F` from the generic point of the trait: the geometric
generic point `Spec Ω ⟶ S`, the closed point `Spec k' ⟶ S`, and the identification
`Spec Ω ⟶ η ⟶ Spec F`. -/
noncomputable def traitModelOfGenericBase :
    NearbyCyclesModel (point F).left (point k').left where
  total := trait k'
  generic := Spec (.of (traitGenericField k'))
  j := traitGenericPoint k'
  i := traitClosedPoint k'
  ε := traitGenericPointToSpec k' ≫ ι

/-- The trait is a model of finite type over itself, along the identities. -/
theorem isTraitModelOver_traitModelOfGenericBase :
    (traitModelOfGenericBase F ι).IsTraitModelOver (𝟙 _) (𝟙 _) := by
  have : IsIso (point k').hom := inferInstanceAs (IsIso (𝟙 _))
  exact ⟨inferInstance, inferInstance, inferInstance,
    IsPullback.of_vert_isIso ⟨by simp [traitModelOfGenericBase]⟩,
    IsPullback.of_vert_isIso ⟨by simp [traitModelOfGenericBase]⟩⟩

/-- The trait is a model of finite type over itself. -/
theorem isTraitModel_traitModelOfGenericBase : (traitModelOfGenericBase F ι).IsTraitModel :=
  (isTraitModelOver_traitModelOfGenericBase F ι).isTraitModel

/-- The trait is a trait model of `Spec F` over the generic base `(F, Spec F)`: its generic fibre
`S ×_S η = η` is identified with `Spec F ×_F η = η`. -/
theorem isTraitModelOfGenericBase_traitModelOfGenericBase :
    (traitModelOfGenericBase F ι).IsTraitModelOfGenericBase (point F) ι (𝟙 _) (𝟙 _) := by
  refine ⟨isTraitModelOver_traitModelOfGenericBase F ι, ?_⟩
  have : IsIso (point F).hom := inferInstanceAs (IsIso (𝟙 _))
  let w : pullback (𝟙 (trait k')) (traitGenericSpec k') ⟶ pullback (point F).hom ι :=
    pullback.lift (pullback.snd _ _ ≫ ι) (pullback.snd _ _) (by simp)
  have hw : w ≫ pullback.snd _ _ = pullback.snd _ _ := pullback.lift_snd _ _ _
  have : IsIso (w ≫ pullback.snd _ _) := by
    rw [hw]
    infer_instance
  have : IsIso w := IsIso.of_isIso_comp_right w (pullback.snd _ _)
  refine ⟨w, inferInstance, hw, ?_⟩
  rw [pullback.lift_fst]
  exact (NearbyCyclesModel.genericFibreInclusion_snd_assoc _ _ _ _ ι).trans (Category.id_comp _)

end Model

section BoundedConstructible

variable (F : Type u) [Field F] {k' : Type u} [Field k'] [IsSepClosed k']
  (ι : Spec (.of (FractionRing (PowerSeries k'))) ⟶ Spec (.of F)) (ℓ : ℕ) [Fact ℓ.Prime]

/-- **Finiteness for the trait as a model of a generic base point**: the nearby cycles
`Ψ = Li^* Rj_* Lε^*` of `ProEtale.CondensedRing.traitModelOfGenericBase` preserve bounded
constructible complexes. `Lε^* K` is bounded constructible on `Spec Ω`, and the nearby functor
`Li^* Rj_*` of the trait carries the constructible sheaves on `Spec Ω` placed in degree `0` to
bounded constructible complexes
(`ProEtale.CondensedRing.boundedConstructible_traitNearby_singleFunctor_obj`), hence all bounded
constructible complexes by dévissage. -/
theorem preservesBoundedConstructible_traitModelOfGenericBase :
    (traitModelOfGenericBase F ι).PreservesBoundedConstructible (Profinite.padicAlgClRingObj ℓ) :=
  fun K hK ↦ boundedConstructible_obj_of_forall_singleFunctor
    (Φ := R((traitGenericPoint k')_*⟦Profinite.padicAlgClRingObj ℓ⟧) ⋙
      L((traitClosedPoint k')^*⟦Profinite.padicAlgClRingObj ℓ⟧))
    (fun _ hF ↦ boundedConstructible_traitNearby_singleFunctor_obj k' hF)
    (boundedConstructible_leftDerivedUpperStar_obj_of_scheme _ _ K hK)

variable [Fact (ringChar F).Prime] [Fact (ringChar F ≠ ℓ)] [Fact (ringChar k').Prime]
  [Fact (ringChar k' ≠ ℓ)]

/-- The nearby cycles `Ψ_s : Dᵇc(Spec F) ⥤ Dᵇc(Spec k')` of the trait as a model of the generic
base point `Spec F`. -/
noncomputable def traitGenericSpecialization :
    Dᵇc((point F).left)⟦Profinite.padicAlgClRingObj ℓ⟧ ⥤
      Dᵇc((point k').left)⟦Profinite.padicAlgClRingObj ℓ⟧ :=
  NearbyCyclesModel.boundedConstructibleNearbyCycles
    (preservesBoundedConstructible_traitModelOfGenericBase F ι ℓ)

/-- The specialization unit `σ_s : ℚ̄_ℓ ⟶ Ψ_s ℚ̄_ℓ` of the trait as a model of the generic base
point `Spec F`. -/
noncomputable def traitGenericSpecializationUnit :
    𝟙_ _ ⟶ (traitGenericSpecialization F ι ℓ).obj (𝟙_ _) :=
  NearbyCyclesModel.boundedConstructibleUnit ℓ _

omit [Fact (ringChar F).Prime] [Fact (ringChar k').Prime] in
/-- The specialization unit `σ_s : ℚ̄_ℓ ⟶ Ψ_s ℚ̄_ℓ = i^* Rj_* ℚ̄_ℓ` of the trait as a model of the
generic base point is an isomorphism: it only involves the inclusions `j` and `i`, as for the
trait model of the base point (`ProEtale.CondensedRing.isIso_traitSpecializationUnit`). -/
theorem isIso_traitGenericSpecializationUnit :
    IsIso (traitGenericSpecializationUnit F ι ℓ) := by
  have h : UpperStarInvertsLowerStarUnit (Profinite.padicAlgClRingObj ℓ) (traitGenericPoint k')
      (traitClosedPoint k') :=
    ⟨isIso_upperStar_traitClosedPoint_map_unit_app _ k',
      isZero_upperStar_traitClosedPoint_obj_rightDerived _ k'⟩
  have : IsIso ((ObjectProperty.ι _).map (traitGenericSpecializationUnit F ι ℓ)) :=
    (traitModelOfGenericBase F ι).isIso_unit_of_upperStarInvertsLowerStarUnit _ h
  exact isIso_of_fully_faithful (ObjectProperty.ι _) _

omit [Fact (ringChar F).Prime] [Fact (ringChar k').Prime] in
instance : IsIso (traitGenericSpecializationUnit F ι ℓ) :=
  isIso_traitGenericSpecializationUnit F ι ℓ

end BoundedConstructible

namespace NearbyCyclesModel

section Monoidal

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  (F : Type u) [Field F] {k' : Type u} [Field k'] [IsSepClosed k']
  (ι : Spec (.of (FractionRing (PowerSeries k'))) ⟶ Spec (.of F))

/-- The unit map of the lax monoidal structure of the nearby cycles of the trait as a model of the
generic base point is invertible: after restriction to the closed point, the unit
`Λ_S ⟶ Rη̄_* Lη̄^* Λ_S` is invertible
(`ProEtale.CondensedRing.isIso_upperStar_traitClosedPoint_map_derivedUnit_app_unit`). -/
lemma isIso_nearbyCyclesLaxMonoidal_ε_traitModelOfGenericBase :
    IsIso (@Functor.LaxMonoidal.ε _ _ _ _ _ _ ((traitModelOfGenericBase F ι).nearbyCycles Λ)
      ((traitModelOfGenericBase F ι).nearbyCyclesLaxMonoidal Λ)) := by
  have h : IsIso (L(((traitModelOfGenericBase F ι).i)^*⟦Λ⟧).map
      ((derivedUpperStarLowerStarAdjunction Λ (traitModelOfGenericBase F ι).j).unit.app
        (𝟙_ _))) :=
    isIso_upperStar_traitClosedPoint_map_derivedUnit_app_unit Λ k'
  exact Adjunction.isIso_ε_comp_rightAdjointLaxMonoidal L(((traitModelOfGenericBase F ι).ε)^*⟦Λ⟧)
    L(((traitModelOfGenericBase F ι).i)^*⟦Λ⟧)
    (derivedUpperStarLowerStarAdjunction Λ (traitModelOfGenericBase F ι).j)

/-- The tensor maps of the nearby cycles of the trait as a model of the generic base point are
invertible at `(A, B)` if `Lε^* A` is a finite direct sum of shifts of the unit
(`ProEtale.CondensedRing.isIso_upperStar_map_lowerStarTensorMap'_of_shiftDecomposition`). -/
lemma isIso_tensorMap_traitModelOfGenericBase
    (A B : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology (point F).left) Ab.{u + 1})
      (condensedRingObj Λ (point F).left)))
    (hA : Nonempty (ShiftDecomposition (𝟙_ _)
      (L(((traitModelOfGenericBase F ι).ε)^*⟦Λ⟧).obj A))) :
    IsIso ((traitModelOfGenericBase F ι).tensorMap Λ A B) := by
  have h := isIso_upperStar_map_lowerStarTensorMap'_of_shiftDecomposition Λ k'
    (V := L(((traitModelOfGenericBase F ι).ε)^*⟦Λ⟧).obj B) hA.some
  unfold tensorMap
  rw [Functor.map_comp]
  exact IsIso.comp_isIso' inferInstance (IsIso.comp_isIso' h inferInstance)

end Monoidal

variable (ℓ : ℕ) [Fact ℓ.Prime] (F : Type u) [Field F] [Fact (ringChar F).Prime]
  [Fact (ringChar F ≠ ℓ)] {k' : Type u} [Field k'] [Fact (ringChar k').Prime]
  [Fact (ringChar k' ≠ ℓ)] [IsSepClosed k']
  (ι : Spec (.of (FractionRing (PowerSeries k'))) ⟶ Spec (.of F))

omit [Fact (ringChar F).Prime] in
/-- **The nearby cycles of the trait are monoidal on the generic base point**: the nearby cycles
`Ψ_S : Dᵇc(Spec F) ⥤ Dᵇc(Spec k')` of the trait as a model of the generic base point `Spec F` are
a monoidal functor with tensor maps the lax tensor maps of nearby cycles
(`boundedConstructibleTensorMap`). The tensor maps are invertible as `Lε^* A` is a finite direct
sum of shifts of the unit on the geometric generic point `Spec Ω`
(`nonempty_shiftDecomposition_of_boundedConstructible`,
`NearbyCyclesModel.isIso_tensorMap_traitModelOfGenericBase`), and the unit map is invertible
(`NearbyCyclesModel.isIso_nearbyCyclesLaxMonoidal_ε_traitModelOfGenericBase`). -/
theorem exists_monoidal_traitGenericSpecialization :
    ∃ L : (boundedConstructibleNearbyCycles
        (preservesBoundedConstructible_traitModelOfGenericBase F ι ℓ)).Monoidal,
      ∀ A B, (letI := L; Functor.LaxMonoidal.μ (boundedConstructibleNearbyCycles
          (preservesBoundedConstructible_traitModelOfGenericBase F ι ℓ)) A B) =
        boundedConstructibleTensorMap
          (preservesBoundedConstructible_traitModelOfGenericBase F ι ℓ) A B := by
  have hμ (A B : Dᵇc((point F).left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
      IsIso ((traitModelOfGenericBase F ι).tensorMap (Profinite.padicAlgClRingObj ℓ) A.obj
        B.obj) :=
    isIso_tensorMap_traitModelOfGenericBase _ F ι A.obj B.obj
      (nonempty_shiftDecomposition_of_boundedConstructible ℓ (K := traitGenericField k') _
        (boundedConstructible_leftDerivedUpperStar_obj_of_scheme _ _ _ A.property))
  exact ⟨boundedConstructibleNearbyCyclesMonoidal _ hμ
      (isIso_nearbyCyclesLaxMonoidal_ε_traitModelOfGenericBase _ F ι),
    boundedConstructibleNearbyCyclesMonoidal_μ _ hμ _⟩

/-- **The duality map of the trait as a model of the generic base point**: with the lax tensor map
of its nearby cycles and the inverse of the specialization unit as dualizing map, the duality map
`δ_{S,N} : Ψ_S RHom(N, ℚ̄_ℓ) ⟶ RHom(Ψ_S N, ℚ̄_ℓ)` is an isomorphism for every bounded
constructible `N` on `Spec F`: `Ψ_S` is monoidal
(`NearbyCyclesModel.exists_monoidal_traitGenericSpecialization`), `N` is dualizable
(`ProEtale.CondensedRing.nonempty_hasLeftDual_point`), monoidal functors commute with duals
(`CategoryTheory.Verdier.isIso_nearbyDualityMap_of_monoidal`), and the dualizing map `σ_s⁻¹`
differs from the inverse of the unit map of `Ψ_S` by an automorphism of the unit. This is the
analogue of `NearbyCyclesModel.isIso_nearbyDualityMap_traitModel`. -/
theorem isIso_nearbyDualityMap_traitModelOfGenericBase
    (N : Dᵇc((point F).left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    IsIso (Verdier.nearbyDualityMap
      (boundedConstructibleTensorMap
        (preservesBoundedConstructible_traitModelOfGenericBase F ι ℓ))
      (inv (traitGenericSpecializationUnit F ι ℓ)) N) := by
  obtain ⟨L, hμ⟩ := exists_monoidal_traitGenericSpecialization ℓ F ι
  obtain ⟨hN⟩ := nonempty_hasLeftDual_point ℓ (k := F) N
  let := L
  have h := Verdier.isIso_nearbyDualityMap_of_monoidal (boundedConstructibleNearbyCycles
    (preservesBoundedConstructible_traitModelOfGenericBase F ι ℓ)) (ᘁN) N
  have e₁ : (fun A B ↦ Functor.LaxMonoidal.μ (boundedConstructibleNearbyCycles
      (preservesBoundedConstructible_traitModelOfGenericBase F ι ℓ)) A B) =
      boundedConstructibleTensorMap
        (preservesBoundedConstructible_traitModelOfGenericBase F ι ℓ) :=
    funext₂ hμ
  rw [e₁] at h
  have e₂ : inv (traitGenericSpecializationUnit F ι ℓ) =
      Functor.OplaxMonoidal.η (boundedConstructibleNearbyCycles
        (preservesBoundedConstructible_traitModelOfGenericBase F ι ℓ)) ≫
        (Functor.LaxMonoidal.ε (boundedConstructibleNearbyCycles
          (preservesBoundedConstructible_traitModelOfGenericBase F ι ℓ)) ≫
          inv (traitGenericSpecializationUnit F ι ℓ)) := by
    rw [Functor.Monoidal.η_ε_assoc]
  rw [e₂, ← Verdier.nearbyDualityMap_comp_ihom_map]
  infer_instance

end NearbyCyclesModel

end AlgebraicGeometry.ProEtale.CondensedRing
