/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Specialization.NearbyDualizingGenericBaseUnique
public import WeilConjectures.TraceFormula.Specialization.NearbyDualityGenericBaseSlice
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.DualizingFieldChange.Basic
public import WeilConjectures.SixFunctors.NearbyCycles.AutAction

/-!

# Re-basing a trait model over a generic base to the generic point of the trait

Let `M` be a trait model of `X₁` over the generic base `(F, X₁, ι : η ⟶ Spec F)`, `η` the generic
point of the strictly henselian trait `S = Spec k'⟦t⟧`. Its geometric generic fibre maps to the base
change `X₁,η = X₁ ×_F η` (`NearbyCyclesModel.genericBaseChange`), and `M` with this new
identification `ε'` is a trait model of `X₁,η` over the generic base `(η, X₁,η, 𝟙)`
(`NearbyCyclesModel.IsTraitModelOfGenericBase.rebase`,
`NearbyCyclesModel.IsTraitModelOfGenericBase.isTraitModelOfGenericBase_rebase`). The identity of
`M` is a morphism of models `M' ⟶ M` over the projection `π : X₁,η ⟶ X₁`
(`NearbyCyclesModel.IsTraitModelOfGenericBase.rebaseHom`), whose pullback exchange
`Ψ_M ⟶ Ψ_{M'} π^*` (`NearbyCyclesModel.IsTraitModelOfGenericBase.rebaseExchange`) is invertible.

**The dualizing maps and re-basing**
(`NearbyCyclesModel.NearbyDualizingDataOfGenericBase.θ_eq_rebase_of_isProper`): for a proper model
with full generic fibre and proper `X₁`, the dualizing map of `M` over `F` is that of `M'` over
`η` composed with the comparison `φ : π^* ω_{X₁} ⟶ ω_{X₁,η}` of the dualizing complexes
(`ProEtale.CondensedRing.dualizingComplexBaseChange`, the mate of proper base change):
`θ_M = α ≫ Ψ_{M'}(φ) ≫ θ_{M'}`.

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

namespace NearbyCyclesModel

variable {F : Type u} [Field F] {k' : Type u} [Field k'] {X₁ : Over (Spec (.of F))}
  {X' : Over (Spec (.of k'))} {ι : Spec (.of (FractionRing (PowerSeries k'))) ⟶ Spec (.of F)}
  {M : NearbyCyclesModel X₁.left X'.left} {q : M.total ⟶ trait k'}
  {g : M.generic ⟶ Spec (.of (traitGenericField k'))}

section SpecialId

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  {T₁ T₂ T₀ : Scheme.{u}} {M₀ : NearbyCyclesModel T₁ T₀} {N₀ : NearbyCyclesModel T₂ T₀}
  {f₀ : T₁ ⟶ T₂}

/-- The pullback exchange `Ψ_N A ⟶ Ψ_M (Lf^* A)` of a morphism of models `φ : M ⟶ N` over `f` and
the identity of the special fibre, through `L(𝟙)^* ≅ 𝟭`. -/
noncomputable def Hom.specialIdExchange (φ : M₀.Hom N₀ f₀ (𝟙 T₀))
    (A : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology T₂) Ab.{u + 1})
      (condensedRingObj Λ T₂))) :
    (N₀.nearbyCycles Λ).obj A ⟶ (M₀.nearbyCycles Λ).obj ((L((f₀)^*⟦Λ⟧)).obj A) :=
  (leftDerivedUpperStarId Λ T₀).inv.app _ ≫ (φ.pullbackExchange Λ).app A

/-- The exchange `NearbyCyclesModel.Hom.specialIdExchange` is natural. -/
@[reassoc]
lemma Hom.specialIdExchange_naturality (φ : M₀.Hom N₀ f₀ (𝟙 T₀))
    {A A' : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology T₂) Ab.{u + 1})
      (condensedRingObj Λ T₂))} (a : A ⟶ A') :
    φ.specialIdExchange Λ A ≫ (M₀.nearbyCycles Λ).map ((L((f₀)^*⟦Λ⟧)).map a) =
      (N₀.nearbyCycles Λ).map a ≫ φ.specialIdExchange Λ A' := by
  have h₁ := (leftDerivedUpperStarId Λ T₀).inv.naturality ((N₀.nearbyCycles Λ).map a)
  have h₂ := (φ.pullbackExchange Λ).naturality a
  dsimp only [Functor.comp_obj, Functor.comp_map, Functor.id_obj, Functor.id_map] at h₁ h₂
  simp only [Hom.specialIdExchange, Category.assoc]
  rw [← h₂]
  exact ((reassoc_of% h₁) _).symm

end SpecialId

variable (X₁ ι) in
/-- The base change `X₁,η = X₁ ×_F η` of the base of a generic base, as a scheme over the generic
point `η` of the trait. -/
noncomputable def genericBaseChange : Over (Spec (.of (FractionRing (PowerSeries k')))) :=
  Over.mk (pullback.snd X₁.hom ι)

instance [LocallyOfFiniteType X₁.hom] : LocallyOfFiniteType (genericBaseChange X₁ ι).hom :=
  inferInstanceAs (LocallyOfFiniteType (pullback.snd X₁.hom ι))

instance [QuasiCompact X₁.hom] : QuasiCompact (genericBaseChange X₁ ι).hom :=
  inferInstanceAs (QuasiCompact (pullback.snd X₁.hom ι))

instance [IsSeparated X₁.hom] : IsSeparated (genericBaseChange X₁ ι).hom :=
  inferInstanceAs (IsSeparated (pullback.snd X₁.hom ι))

/-- The base change `X₁,η` of a proper base is proper. -/
lemma isProper_toPoint_genericBaseChange [IsProper (toPoint X₁).left] :
    IsProper (toPoint (genericBaseChange X₁ ι)).left := by
  rw [toPoint_left]
  have : IsProper X₁.hom := by rw [← toPoint_left]; infer_instance
  exact inferInstanceAs (IsProper (pullback.snd X₁.hom ι))

variable (X₁ ι) in
/-- The base change square `X₁,η ⟶ X₁` over `ι : η ⟶ Spec F`. -/
lemma isPullback_genericBaseChange :
    IsPullback (pullback.fst X₁.hom ι) (toPoint (genericBaseChange X₁ ι)).left
      (toPoint X₁).left ι := by
  rw [toPoint_left, toPoint_left]
  exact IsPullback.of_hasPullback _ _

namespace IsTraitModelOfGenericBase

/-- The geometric generic fibre of a trait model over the generic base lies over `ι`. -/
lemma ε_comp_hom (h : M.IsTraitModelOfGenericBase X₁ ι q g) :
    M.ε ≫ X₁.hom = (g ≫ traitGenericPointToSpec k') ≫ ι := by
  obtain ⟨u, -, hu₁, hu₂⟩ := h.exists_openImmersion
  rw [← hu₁, Category.assoc, pullback.condition, ← Category.assoc, hu₂, Category.assoc]

/-- The **re-based model**: the model `M` with the identification `ε' : 𝒳_Ω ⟶ X₁ ×_F η` of its
geometric generic fibre, a model of the base change `X₁,η` of the base. -/
noncomputable def rebase (h : M.IsTraitModelOfGenericBase X₁ ι q g) :
    NearbyCyclesModel (genericBaseChange X₁ ι).left X'.left where
  total := M.total
  generic := M.generic
  j := M.j
  i := M.i
  ε := pullback.lift M.ε (g ≫ traitGenericPointToSpec k') h.ε_comp_hom

/-- **The re-based model is a trait model over the generic base `(η, X₁,η, 𝟙)`.** -/
theorem isTraitModelOfGenericBase_rebase (h : M.IsTraitModelOfGenericBase X₁ ι q g) :
    h.rebase.IsTraitModelOfGenericBase (genericBaseChange X₁ ι) (𝟙 _) q g := by
  sorry

/-- The identity of `M` as a morphism of models `M' ⟶ M` from the re-based model, over the
projection `π : X₁,η ⟶ X₁` and the identity of the special fibre. -/
noncomputable def rebaseHom (h : M.IsTraitModelOfGenericBase X₁ ι q g) :
    h.rebase.Hom M (pullback.fst X₁.hom ι) (𝟙 X'.left) where
  total := 𝟙 _
  generic := 𝟙 _
  comm_j := by simp [rebase]
  comm_i := by simp [rebase]
  comm_ε := by simp [rebase]

variable (ℓ : ℕ) [Fact ℓ.Prime] [Fact (ringChar F).Prime] [Fact (ringChar F ≠ ℓ)]
  [IsSepClosed k'] [Fact (ringChar k').Prime] [Fact (ringChar k' ≠ ℓ)]
  [LocallyOfFiniteType X₁.hom] [QuasiCompact X₁.hom] [IsSeparated X₁.hom]
  [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom] [IsSeparated X'.hom]

/-- The **re-basing exchange** `Ψ_M ⟶ Ψ_{M'} π^*` on bounded constructible complexes: the pullback
exchange of `NearbyCyclesModel.IsTraitModelOfGenericBase.rebaseHom`, through `L𝟙^* ≅ 𝟭` on the
special fibre. -/
noncomputable def rebaseExchange (h : M.IsTraitModelOfGenericBase X₁ ι q g) :
    boundedConstructibleNearbyCycles (h.preservesBoundedConstructible (ℓ := ℓ)) ⟶
      boundedConstructibleUpperStarOfMap ℓ (X := X₁) (Y := genericBaseChange X₁ ι)
          (pullback.fst X₁.hom ι) ⋙
        boundedConstructibleNearbyCycles
          (h.isTraitModelOfGenericBase_rebase.preservesBoundedConstructible (ℓ := ℓ)) where
  app A := ObjectProperty.homMk
    (h.rebaseHom.specialIdExchange (Profinite.padicAlgClRingObj ℓ) A.obj)
  naturality _ _ f := ObjectProperty.hom_ext _
    (h.rebaseHom.specialIdExchange_naturality (Profinite.padicAlgClRingObj ℓ) f.hom).symm

end IsTraitModelOfGenericBase

namespace NearbyDualizingDataOfGenericBase

variable {ℓ : ℕ} [Fact ℓ.Prime] [Fact (ringChar F).Prime] [Fact (ringChar F ≠ ℓ)]
  [IsSepClosed k'] [Fact (ringChar k').Prime] [Fact (ringChar k' ≠ ℓ)]
  [LocallyOfFiniteType X₁.hom] [QuasiCompact X₁.hom] [IsSeparated X₁.hom]
  [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom] [IsSeparated X'.hom]

/-- **The dualizing maps and re-basing to the generic point of the trait**: for a proper trait model
`M` over the generic base `(F, X₁, ι)` with `X₁` proper and full generic fibre, the dualizing map
`θ_M` is the composite of the re-basing exchange `Ψ_M ω_{X₁} ⟶ Ψ_{M'} π^* ω_{X₁}`, of `Ψ_{M'}` of
the comparison `φ : π^* ω_{X₁} ⟶ ω_{X₁,η}` of the dualizing complexes along `ι` (for the inverse
of the unit isomorphism of the monoidal functor `ι^*`), and of the dualizing map `θ_{M'}` of the
re-based model over `η`. -/
theorem θ_eq_rebase_of_isProper (D : NearbyDualizingDataOfGenericBase k' ℓ)
    [IsProper (toPoint X₁).left] [IsProper (toPoint X').left]
    (h : M.IsTraitModelOfGenericBase X₁ ι q g) [IsProper q]
    (hgen : IsPullback M.ε g X₁.hom (traitGenericPointToSpec k' ≫ ι)) :
    haveI := isProper_toPoint_genericBaseChange (X₁ := X₁) (ι := ι)
    D.θ h = (h.rebaseExchange ℓ).app (dualizingComplex ℓ X₁) ≫
      (boundedConstructibleNearbyCycles
          (h.isTraitModelOfGenericBase_rebase.preservesBoundedConstructible (ℓ := ℓ))).map
        (dualizingComplexBaseChange ℓ
          (inv (Functor.LaxMonoidal.ε (boundedConstructibleUpperStarOfMap ℓ
            (X := point F) (Y := point (FractionRing (PowerSeries k'))) ι)))
          (isPullback_genericBaseChange X₁ ι)) ≫
      D.θ h.isTraitModelOfGenericBase_rebase := by
  sorry

end NearbyDualizingDataOfGenericBase

end NearbyCyclesModel

end AlgebraicGeometry.ProEtale.CondensedRing
