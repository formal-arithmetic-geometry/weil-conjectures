/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Submission.WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.ProperNoetherianBase
public import Submission.WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.WeaklyEtale
public import Submission.WeilConjectures.TraceFormula.Specialization.NearbyDualizingMap
public import Submission.WeilConjectures.TraceFormula.Specialization.NearbyKunnethGlobal
public import Submission.WeilConjectures.SixFunctors.NearbyCycles.PushforwardExchangeSquare

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-!

# The proper exchange of a proper trait model over the base

Let `M` be a trait model of a `k`-scheme `X` over the base (`NearbyCyclesModel.IsTraitModelOfBase`)
with proper total space, whose geometric generic fibre is all of `X ×_k Spec Ω`. The proper
exchange `χ_a : Ψ_S Ra_* ⟶ Ra'_* Ψ_M` of the structure morphism `a : X ⟶ Spec k`
(`NearbyCyclesModel.IsTraitModelOfBase.pushforwardExchange`) is an isomorphism on bounded
constructible complexes (`NearbyCyclesModel.IsTraitModelOfBase.isIso_pushforwardExchange_app`).
The proof works on the ambient derived categories
(`NearbyCyclesModel.IsTraitModelOfBase.isIso_pushforwardExchange_app_ambient`) and then restricts
to `Dᵇc` through `NearbyCyclesModel.Hom.boundedConstructiblePushforwardExchange_app_hom`.

The proof compares `χ_a` with the proper exchange of the model `M` of its geometric generic fibre
over the trait as a model of `Spec Ω` (`NearbyCyclesModel.IsTraitModelOver.toTraitGeneric`,
invertible by blueprint `det-sp-nearby-cycles-exchanges` (2),
`NearbyCyclesModel.IsTraitModelOver.isIso_pushforwardExchange_toTraitGeneric_app`): by the square
law of the pullback exchanges, the two differ by `Ψ_S` of the base change morphism
`Lε^* Ra_* ⟶ Rg_* Lε^*` of the cartesian square of generic fibres, which is invertible by proper
base change (blueprint `sk-thm-sfb-proper-base-change`,
`ProEtale.CondensedRing.isIso_baseChangeMap_app_padicAlgCl_of_isProper`), and
by pullback exchanges along identities (`NearbyCyclesModel.pushforwardExchange_square_aux`).

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

/-! ### Restriction to bounded constructible complexes -/

namespace NearbyCyclesModel

section Restricted

variable (ℓ : ℕ) [Fact ℓ.Prime] {k k' : Type u} [Field k]
  [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)] [Field k'] [Fact (ringChar k').Prime]
  [Fact (ringChar k' ≠ ℓ)]
  {X Y : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  {X' Y' : Over (Spec (.of k'))} [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom]
  [IsSeparated X'.hom] [LocallyOfFiniteType Y'.hom] [QuasiCompact Y'.hom] [IsSeparated Y'.hom]
  {M : NearbyCyclesModel X.left X'.left} {N : NearbyCyclesModel Y.left Y'.left}
  {f : X ⟶ Y} {f' : X' ⟶ Y'}

/-- A component of the restricted pushforward exchange is invertible if the corresponding
component of the ambient pushforward exchange is. -/
lemma Hom.isIso_boundedConstructiblePushforwardExchange_app (φ : M.Hom N f.left f'.left)
    (hM : M.PreservesBoundedConstructible (Profinite.padicAlgClRingObj ℓ))
    (hN : N.PreservesBoundedConstructible (Profinite.padicAlgClRingObj ℓ))
    (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (hK : IsIso ((φ.pushforwardExchange (Profinite.padicAlgClRingObj ℓ)).app K.obj)) :
    IsIso ((φ.boundedConstructiblePushforwardExchange ℓ hM hN).app K) := by
  rw [← ObjectProperty.isIso_hom_iff, Hom.boundedConstructiblePushforwardExchange_app_hom]
  exact hK

end Restricted

end NearbyCyclesModel

/-! ### The proper exchange of a proper trait model -/

namespace NearbyCyclesModel

/-- The model `M` of the geometric generic fibre (`NearbyCyclesModel.toGeneric`, with `ε = 𝟙`)
maps to `M` over `ε`, by the identities of the total space and of the geometric generic fibre. -/
@[simps]
def toGenericSelfHom {X X' : Scheme.{u}} (M : NearbyCyclesModel X X') :
    M.toGeneric.Hom M M.ε (𝟙 X') where
  total := 𝟙 _
  generic := 𝟙 _
  comm_j := by simp
  comm_i := by simp
  comm_ε := by simp

variable (k : Type u) [Field k] (k' : Type u) [Field k'] [Algebra k k']

/-- The trait as a model of its geometric generic point maps to the trait as a model of the base
point `Spec k`, over `Spec Ω ⟶ Spec k`, by identities. -/
@[simps]
noncomputable def traitGenericModelHom :
    (traitGenericModel k').Hom (traitModel k k') (traitModel k k').ε (𝟙 (point k').left) where
  total := 𝟙 _
  generic := 𝟙 _
  comm_j := by simp [traitModel, traitGenericModel]
  comm_i := by simp [traitModel, traitGenericModel]
  comm_ε := by simp [traitModel, traitGenericModel]

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]

/-- The pullback exchange of `NearbyCyclesModel.toGenericSelfHom` is invertible: all its
squares are identities. -/
instance isIso_pullbackExchange_toGenericSelfHom {X X' : Scheme.{u}}
    (M : NearbyCyclesModel X X') : IsIso ((toGenericSelfHom M).pullbackExchange Λ) := by
  have : L(((toGenericSelfHom M).total)^*⟦Λ⟧).IsEquivalence :=
    Functor.isEquivalence_of_iso (leftDerivedUpperStarId Λ _).symm
  have : L(((toGenericSelfHom M).generic)^*⟦Λ⟧).IsEquivalence :=
    Functor.isEquivalence_of_iso (leftDerivedUpperStarId Λ _).symm
  have := isIso_mateEquiv_of_isEquivalence (derivedUpperStarLowerStarAdjunction Λ M.j)
    (derivedUpperStarLowerStarAdjunction Λ M.toGeneric.j)
    (pullbackSquareComparison Λ (toGenericSelfHom M).commSq_j).hom
  unfold Hom.pullbackExchange
  infer_instance

/-- The pullback exchange of `NearbyCyclesModel.traitGenericModelHom` is invertible: all its
squares are identities. -/
instance isIso_pullbackExchange_traitGenericModelHom :
    IsIso ((traitGenericModelHom k k').pullbackExchange Λ) := by
  have : L(((traitGenericModelHom k k').total)^*⟦Λ⟧).IsEquivalence :=
    Functor.isEquivalence_of_iso (leftDerivedUpperStarId Λ _).symm
  have : L(((traitGenericModelHom k k').generic)^*⟦Λ⟧).IsEquivalence :=
    Functor.isEquivalence_of_iso (leftDerivedUpperStarId Λ _).symm
  have := isIso_mateEquiv_of_isEquivalence
    (derivedUpperStarLowerStarAdjunction Λ (traitModel k k').j)
    (derivedUpperStarLowerStarAdjunction Λ (traitGenericModel k').j)
    (pullbackSquareComparison Λ (traitGenericModelHom k k').commSq_j).hom
  unfold Hom.pullbackExchange
  infer_instance

variable {k k'} (ℓ : ℕ) [Fact ℓ.Prime]
  {X : Over (Spec (.of k))} {X' : Over (Spec (.of k'))} {M : NearbyCyclesModel X.left X'.left}
  {q : M.total ⟶ trait k'} {g : M.generic ⟶ Spec (.of (traitGenericField k'))}

set_option hygiene false in
/-- The condensed field `ℚ̄_ℓ`. -/
local notation "𝐐" => Profinite.padicAlgClRingObj ℓ

set_option maxHeartbeats 800000 in
-- the square law of the exchanges is instantiated on the ambient derived categories
/-- **Proper exchange for a proper trait model over the base**, on the ambient derived
categories: if the total space of the trait model `M` over the base is proper over the trait and
its geometric generic fibre is all of `X ×_k Spec Ω`, the proper exchange
`χ_a : Ψ_S Ra_* K ⟶ Ra'_* Ψ_M K` of the structure morphism `a : X ⟶ Spec k` is invertible at
every bounded constructible `K` (for proper `X`). By the square law
`NearbyCyclesModel.pushforwardExchange_square_aux`, it agrees, up to invertible pullback
exchanges along identities and base change along identities, with the proper exchange of the
model of the geometric generic fibre (blueprint `det-sp-nearby-cycles-exchanges` (2)) composed
with `Ψ_S` of the proper base change morphism of the square of generic fibres. -/
theorem IsTraitModelOfBase.isIso_pushforwardExchange_app_ambient
    [Fact (ringChar k ≠ ℓ)] [IsSepClosed k'] [Fact (ringChar k').Prime] [Fact (ringChar k' ≠ ℓ)]
    (h : M.IsTraitModelOfBase k q g) [IsProper q] [IsProper (toPoint X).left]
    (hgen : IsPullback M.ε g X.hom (traitGenericPoint k' ≫ traitToBase k k'))
    (A : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X.left) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X.left)))
    (hA : boundedConstructible _ A) :
    IsIso ((h.toTrait.pushforwardExchange (Profinite.padicAlgClRingObj ℓ)).app A) := by
  have hM := h.isTraitModelOver
  obtain ⟨e, he, -⟩ := h.exists_comp_ε
  have hb : M.ε ≫ (toPoint X).left = g ≫ (traitModel k k').ε := h.toTrait.comm_ε.symm
  have hs : 𝟙 X'.left ≫ (toPoint X').left = X'.hom ≫ 𝟙 (point k').left := by simp
  have hSQ := fun C ↦ Hom.pullbackExchange_square 𝐐 (toGenericSelfHom M) h.toTrait
    hM.toTraitGeneric (traitGenericModelHom k k')
    (by simp [IsTraitModelOfBase.toTrait]) (by simp [IsTraitModelOfBase.toTrait]) hb hs C
  have hgen' : IsPullback M.ε g (toPoint X).left (traitModel k k').ε := by
    have e₀ : (traitModel k k').ε = traitGenericPoint k' ≫ traitToBase k k' :=
      (traitModel_j_traitToBase k k').symm
    rw [e₀, toPoint_left]
    exact hgen
  have key := pushforwardExchange_square_aux
    (derivedUpperStarLowerStarAdjunction 𝐐 (toPoint X).left)
    (derivedUpperStarLowerStarAdjunction 𝐐 g)
    (derivedUpperStarLowerStarAdjunction 𝐐 (toPoint X').left)
    (derivedUpperStarLowerStarAdjunction 𝐐 X'.hom)
    ((toGenericSelfHom M).pullbackExchange 𝐐) ((traitGenericModelHom k k').pullbackExchange 𝐐)
    (h.toTrait.pullbackExchange 𝐐) (hM.toTraitGeneric.pullbackExchange 𝐐)
    (h.toTrait.pushforwardExchange 𝐐) (hM.toTraitGeneric.pushforwardExchange 𝐐)
    (h.toTrait.map_pushforwardExchange_app_comp_counit_app 𝐐)
    (hM.toTraitGeneric.map_pushforwardExchange_app_comp_counit_app 𝐐)
    (pullbackSquareComparison 𝐐 ⟨hb⟩).hom (pullbackSquareComparison 𝐐 ⟨hs⟩).hom
    (baseChangeMap 𝐐 ⟨hb⟩) (baseChangeMap 𝐐 ⟨hs⟩)
    (Adjunction.exchangeRight_app_comp_counit' _ _ _ _ rfl)
    (Adjunction.exchangeRight_app_comp_counit' _ _ _ _ rfl) hSQ A
  have : IsNoetherian (point k).left := inferInstanceAs (IsNoetherian (Spec (.of k)))
  have pbc := isIso_baseChangeMap_app_padicAlgCl_of_isProper ℓ
    (𝟙 (point k).left) (traitGenericPoint k' ≫ traitToBase k' k') ⟨hb⟩ hgen' A hA
  -- the base change morphisms are invertible
  have : IsIso (baseChangeMap 𝐐 ⟨hs⟩) := by
    have : WeaklyEtale (𝟙 X'.left) := MorphismProperty.id_mem _ _
    have : WeaklyEtale (𝟙 (point k').left) := MorphismProperty.id_mem _ _
    have hsq : IsPullback (𝟙 X'.left) X'.hom (toPoint X').left (𝟙 (point k').left) := by
      rw [toPoint_left]
      exact IsPullback.of_id_fst
    exact isIso_baseChangeMap_of_weaklyEtale 𝐐 hsq
  -- the proper exchange of the model of the geometric generic fibre is invertible
  have hC₀ : boundedConstructible _ (L((e)^*⟦𝐐⟧).obj A) :=
    boundedConstructible_leftDerivedUpperStar_obj_of_scheme _ e _ hA
  have h₀ := hM.isIso_pushforwardExchange_toTraitGeneric_app (ℓ := ℓ) (L((e)^*⟦𝐐⟧).obj A) hC₀
  have iso : L((M.ε)^*⟦𝐐⟧).obj A ≅ L((M.j)^*⟦𝐐⟧).obj (L((e)^*⟦𝐐⟧).obj A) :=
    (eqToIso (congrArg (fun f : M.generic ⟶ X.left ↦ L((f)^*⟦𝐐⟧)) he.symm)).app A ≪≫
      (leftDerivedUpperStarComp 𝐐 M.j e).app A
  have hχgen : IsIso ((hM.toTraitGeneric.pushforwardExchange 𝐐).app (L((M.ε)^*⟦𝐐⟧).obj A)) :=
    NatTrans.isIso_app_of_iso' _ iso
  have := isIso_pullbackExchange_traitGenericModelHom k k' 𝐐
  have hcomp : IsIso (L((𝟙 (point k').left)^*⟦𝐐⟧).map
      ((h.toTrait.pushforwardExchange 𝐐).app A) ≫ (baseChangeMap 𝐐 ⟨hs⟩).app _ ≫
        R((X'.hom)_*⟦𝐐⟧).map (((toGenericSelfHom M).pullbackExchange 𝐐).app A)) := by
    rw [key]
    exact IsIso.comp_isIso' (NatIso.isIso_app_of_isIso _ _)
      (IsIso.comp_isIso' (Functor.map_isIso _ _) hχgen)
  have : IsIso (L((𝟙 (point k').left)^*⟦𝐐⟧).map ((h.toTrait.pushforwardExchange 𝐐).app A)) :=
    IsIso.of_isIso_comp_right _ ((baseChangeMap 𝐐 ⟨hs⟩).app _ ≫
      R((X'.hom)_*⟦𝐐⟧).map (((toGenericSelfHom M).pullbackExchange 𝐐).app A))
  have : L((𝟙 (point k').left)^*⟦𝐐⟧).IsEquivalence :=
    Functor.isEquivalence_of_iso (leftDerivedUpperStarId 𝐐 _).symm
  exact isIso_of_reflects_iso _ L((𝟙 (point k').left)^*⟦𝐐⟧)

/-- **Proper exchange for a proper trait model over the base**: if `X` is proper over `k`, the
total space of the trait model `M` over the base is proper over the trait and its geometric
generic fibre is all of `X ×_k Spec Ω`, the proper exchange `χ_a : Ψ_S Ra_* ⟶ Ra'_* Ψ_M` of the
structure morphism is an isomorphism on bounded constructible complexes
(`NearbyCyclesModel.IsTraitModelOfBase.isIso_pushforwardExchange_app_ambient`, restricted by
`NearbyCyclesModel.Hom.isIso_boundedConstructiblePushforwardExchange_app`). -/
theorem IsTraitModelOfBase.isIso_pushforwardExchange_app [Fact (ringChar k).Prime]
    [Fact (ringChar k ≠ ℓ)] [IsSepClosed k'] [Fact (ringChar k').Prime] [Fact (ringChar k' ≠ ℓ)]
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom] [IsSeparated X'.hom]
    (h : M.IsTraitModelOfBase k q g) [IsProper q] [IsProper (toPoint X).left]
    (hgen : IsPullback M.ε g X.hom (traitGenericPoint k' ≫ traitToBase k k'))
    (K : Dᵇc(X.left)⟦𝐐⟧) : IsIso ((h.pushforwardExchange ℓ).app K) := by
  -- rewriting first makes the instances of the goal those of the restriction lemma
  have e1 : h.pushforwardExchange ℓ = Hom.boundedConstructiblePushforwardExchange
      (f := toPoint X) (f' := toPoint X') ℓ h.toTrait (h.preservesBoundedConstructible ℓ)
      (preservesBoundedConstructible_traitModel ℓ) := rfl
  rw [e1]
  exact Hom.isIso_boundedConstructiblePushforwardExchange_app (f := toPoint X)
    (f' := toPoint X') ℓ h.toTrait _ _ K
    (h.isIso_pushforwardExchange_app_ambient ℓ hgen K.obj K.property)

end NearbyCyclesModel

end AlgebraicGeometry.ProEtale.CondensedRing
