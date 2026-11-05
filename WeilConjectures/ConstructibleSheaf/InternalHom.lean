/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Algebra.Category.ModuleCat.IhomComparison
public import WeilConjectures.CategoryTheory.Sites.ConstantSheafMonoidal
public import WeilConjectures.ConstructibleSheaf.Monoidal
public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Conservative
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.InternalHom

/-!
# The internal hom of finite locally constant sheaves

Let `Λ` be a commutative ring. For sheaves of `Λ`-modules on the small étale site of a scheme
`X`:

- the constant sheaf functor preserves internal homs out of finitely presented modules
  (`AlgebraicGeometry.Etale.isIso_ihomComparison_constantSheaf_app`): it is monoidal and exact;
- for `Λ` noetherian, the internal hom `[L, M]` of two finite locally constant sheaves is finite
  locally constant (`AlgebraicGeometry.Scheme.IsFiniteLocallyConstantSheaf.ihom`, blueprint
  `lem-pur-lisse-morphism-rigidity`, clause (1)): on a common trivialising cover, pullback
  commuting with internal homs, it is the constant sheaf at `Hom_Λ(P, Q)` for finitely generated,
  hence finitely presented, modules `P` and `Q`.

We also record two local criteria along an étale cover: a morphism of sheaves whose pullbacks to
the members of an étale cover are isomorphisms is an isomorphism
(`AlgebraicGeometry.Etale.isIso_of_isIso_upperStar_map_of_cover`), and finiteness of a sheaf is
étale local (`AlgebraicGeometry.Scheme.IsFiniteSheaf.of_cover`).
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory Functor.LaxMonoidal

namespace AlgebraicGeometry

open Scheme

variable {X : Scheme.{u}}

/-- A geometric point of `X` lifts to a member of an étale cover of `X`. -/
lemma Scheme.Cover.exists_comp_eq_of_isSepClosed (𝒰 : Cover.{u} etalePrecoverage X)
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ X) :
    ∃ (i : 𝒰.I₀) (t : Spec (.of Ω) ⟶ 𝒰.X i), t ≫ 𝒰.f i = s := by
  obtain ⟨i, v, hv⟩ := 𝒰.exists_eq (s.base (IsLocalRing.closedPoint Ω))
  have : Etale (𝒰.f i) := 𝒰.map_prop i
  obtain ⟨t, -⟩ := pointSmallEtaleFiberObjToPreimage_surjective s rfl (Scheme.Etale.mk (𝒰.f i))
    ⟨v, hv.trans (congrArg s.base (Subsingleton.elim _ _))⟩
  exact ⟨i, t.left, Over.w t⟩

section General

variable {A : Type*} [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]

/-- **Isomorphy is étale local**: a morphism of étale sheaves whose pullbacks to the members of
an étale cover are isomorphisms is an isomorphism. -/
lemma Etale.isIso_of_isIso_upperStar_map_of_cover (𝒰 : Cover.{u} etalePrecoverage X)
    {F G : Sheaf X.smallEtaleTopology A} (φ : F ⟶ G)
    (h : ∀ i, IsIso ((Etale.upperStar A (𝒰.f i)).map φ)) : IsIso φ := by
  have : ∀ i, Etale (𝒰.f i) := 𝒰.map_prop
  refine Etale.isIso_of_isIso_localizationRestriction A _ 𝒰.f ?_ fun i ↦ ?_
  · refine Set.eq_univ_of_forall fun x ↦ ?_
    obtain ⟨i, y, hy⟩ := 𝒰.exists_eq x
    exact Set.mem_iUnion.2 ⟨i, y, hy⟩
  · let r := Etale.upperStarIsoLocalizationRestriction A (𝒰.f i) inferInstance
    have h' := r.hom.naturality φ
    rw [← cancel_epi (r.inv.app _), Iso.inv_hom_id_app_assoc] at h'
    rw [← h']
    have := h i
    infer_instance

variable {FA : A → A → Type (u + 1)} {CA : A → Type (u + 1)}
  [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory.{u + 1} A FA]

/-- **Finiteness is étale local**: if the pullbacks of `G` to the members of an étale cover are
finite, so is `G`. -/
theorem Scheme.IsFiniteSheaf.of_cover (𝒰 : Cover.{u} etalePrecoverage X)
    (G : Sheaf X.smallEtaleTopology A)
    [∀ i, IsFiniteSheaf (FA := FA) (CA := CA) ((Etale.upperStar A (𝒰.f i)).obj G)] :
    IsFiniteSheaf (FA := FA) (CA := CA) G where
  isFinitelyGenerated_sheafFiber Ω _ _ s := by
    obtain ⟨i, t, rfl⟩ := 𝒰.exists_comp_eq_of_isSepClosed s
    exact (IsFiniteSheaf.isFinitelyGenerated_sheafFiber (FA := FA) (CA := CA)
      (F := (Etale.upperStar A (𝒰.f i)).obj G) Ω t).of_iso
      ((Etale.upperStarCompSheafFiberIso A (𝒰.f i) t).app G)

end General

variable {Λ : Type (u + 1)} [CommRing Λ]

/-- The constant sheaf at a finitely generated module is finite: its stalks are the module. -/
lemma Scheme.isFiniteSheaf_constantSheaf (H : ModuleCat.{u + 1} Λ) [Module.Finite Λ H] :
    IsFiniteSheaf ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj H) where
  isFinitelyGenerated_sheafFiber Ω _ _ s := by
    have : PreservesFilteredColimitsOfSize.{u, u}
        (CategoryTheory.forget (ModuleCat.{u + 1} Λ)) :=
      preservesFilteredColimitsOfSize_shrink.{u, u + 1, u, u + 1} _
    exact ((ModuleCat.isFinitelyGenerated_iff H).2 inferInstance).of_iso
      ((pointSmallEtale s).sheafFiberConstantSheafIso H).symm

end AlgebraicGeometry
