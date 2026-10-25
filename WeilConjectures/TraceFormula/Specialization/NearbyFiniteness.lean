/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.NearbyCycles.BoundedConstructible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleDevissage
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Localizing
public import WeilConjectures.TraceFormula.Specialization.TraitModel

/-!

# Deligne's finiteness theorem for nearby cycles

Let `M` be a model of finite type over the strictly henselian trait `S = Spec k'⟦t⟧`
(`NearbyCyclesModel.IsTraitModel`), `k'` separably closed of characteristic `p ≠ ℓ`, with total
space `𝒳`, geometric generic fibre `j : 𝒳_η̄ ⟶ 𝒳` and special fibre `i : X' ⟶ 𝒳`. Deligne's
finiteness theorem (SGA 4½, [Th. finitude], Thm. 3.2) says that the geometric nearby cycles
`Li^* Rj_* Lj^*` carry bounded constructible `ℚ̄_ℓ`-complexes on `𝒳` to bounded constructible
complexes on `X'` (`NearbyCyclesModel.boundedConstructible_geometricNearbyCycles_obj`). Hence the
nearby cycles `Ψ = Li^* Rj_* Lε^*` of a model whose identification factors as `ε = j ≫ e` through
the total space preserve bounded constructible complexes
(`NearbyCyclesModel.preservesBoundedConstructible_of_exists_comp`): `Lε^* ≅ Lj^* Le^*`, and the
pullback `Le^*` preserves bounded constructible complexes.

The statement for complexes is reduced, by dévissage along the truncation triangles
(`ProEtale.boundedConstructible_obj_of_forall_singleFunctor`), to constructible sheaves placed in
degree `0`, the form in which SGA 4½ states it.

## Unfinished input

The theorem for a constructible sheaf
(`NearbyCyclesModel.boundedConstructible_geometricNearbyCycles_singleFunctor`) is `sorry`ed: it is
Deligne's theorem for torsion coefficients (SGA 4½, [Th. finitude], Thm. 3.2, resting on the
generic constructibility theorem 1.9 and on the reduction to the strict henselization of a curve),
passed to `ℚ̄_ℓ`-coefficients through `𝒪_E`-lattices, derived completeness and the Milnor sequence
(Bhatt–Scholze, *The pro-étale topology for schemes*, §6.8). The dévissage also uses that bounded
constructible complexes on the special fibre form a triangulated subcategory
(`ProEtale.isTriangulated_boundedConstructible`, `sorry`ed on the branch).

-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

namespace NearbyCyclesModel

variable {ℓ : ℕ} [Fact ℓ.Prime] {k' : Type u} [Field k'] {X : Scheme.{u}}
  {X' : Over (Spec (.of k'))}

/-- The special fibre of a model of finite type over the trait is a noetherian scheme: it is of
finite type over the field `k'`. -/
lemma isNoetherian_of_isTraitModel {M : NearbyCyclesModel X X'.left} (hM : M.IsTraitModel) :
    IsNoetherian X'.left := by
  obtain ⟨q, g, _, _, _, -, hi⟩ := hM.exists_isPullback
  have : LocallyOfFiniteType X'.hom :=
    MorphismProperty.of_isPullback (P := @LocallyOfFiniteType) hi ‹_›
  have : QuasiCompact X'.hom := MorphismProperty.of_isPullback (P := @QuasiCompact) hi ‹_›
  have : IsLocallyNoetherian X'.left := LocallyOfFiniteType.isLocallyNoetherian X'.hom
  have : CompactSpace X'.left := QuasiCompact.compactSpace_of_compactSpace X'.hom
  exact ⟨⟩

variable [IsSepClosed k'] [Fact (ringChar k').Prime] [Fact (ringChar k' ≠ ℓ)]

/-- **Deligne's finiteness theorem for nearby cycles, for a constructible sheaf** (SGA 4½,
[Th. finitude], Thm. 3.2; for `ℚ̄_ℓ`-coefficients through `𝒪_E`-lattices and passage to the
limit, Bhatt–Scholze, *The pro-étale topology for schemes*, §6.8): for a model `M` of finite
type over the strictly henselian trait `Spec k'⟦t⟧` (`k'` separably closed, `ℓ ≠ char k'`) and a
constructible sheaf `F` of `ℚ̄_ℓ`-modules on its total space `𝒳`, the geometric nearby cycles
`Li^* Rj_* Lj^* F` of `F` are a bounded constructible complex on the special fibre. -/
theorem boundedConstructible_geometricNearbyCycles_singleFunctor
    (M : NearbyCyclesModel X X'.left) (hM : M.IsTraitModel)
    (F : Mod (Sheaf (Scheme.ProEt.topology M.total) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) M.total))
    (hF : IsConstructibleModuleObject _ F) :
    boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X'.left)
      ((L((M.j)^*⟦Profinite.padicAlgClRingObj ℓ⟧) ⋙ R((M.j)_*⟦Profinite.padicAlgClRingObj ℓ⟧) ⋙
        L((M.i)^*⟦Profinite.padicAlgClRingObj ℓ⟧)).obj
          ((DerivedCategory.singleFunctor _ 0).obj F)) :=
  sorry

/-- **Deligne's finiteness theorem for nearby cycles** (SGA 4½, [Th. finitude], Thm. 3.2; for
`ℚ̄_ℓ`-coefficients, Bhatt–Scholze §6.8): for a model `M` of finite type over the strictly
henselian trait `Spec k'⟦t⟧`, the geometric nearby cycles `Li^* Rj_* Lj^*` carry bounded
constructible complexes on the total space `𝒳` to bounded constructible complexes on the special
fibre. This is reduced to constructible sheaves
(`NearbyCyclesModel.boundedConstructible_geometricNearbyCycles_singleFunctor`) by dévissage along
the truncation triangles. -/
theorem boundedConstructible_geometricNearbyCycles_obj
    (M : NearbyCyclesModel X X'.left) (hM : M.IsTraitModel)
    {B : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology M.total) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) M.total))}
    (hB : boundedConstructible _ B) :
    boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X'.left)
      ((L((M.j)^*⟦Profinite.padicAlgClRingObj ℓ⟧) ⋙ R((M.j)_*⟦Profinite.padicAlgClRingObj ℓ⟧) ⋙
        L((M.i)^*⟦Profinite.padicAlgClRingObj ℓ⟧)).obj B) := by
  have := isNoetherian_of_isTraitModel hM
  have : (boundedConstructible
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X'.left)).IsTriangulated :=
    isTriangulated_boundedConstructible (ℓ := ℓ) _ _
  exact boundedConstructible_obj_of_forall_singleFunctor _
    (fun F hF ↦ boundedConstructible_geometricNearbyCycles_singleFunctor M hM F hF) hB

/-- The derived pullbacks along equal morphisms agree on objects. -/
lemma nonempty_leftDerivedUpperStar_obj_iso_of_eq (Λ : Sheaf (coherentTopology Profinite.{u})
    Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ] {Y Z : Scheme.{u}} {a b : Y ⟶ Z} (h : a = b)
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
      (condensedRingObj Λ Z))) :
    Nonempty ((L((a)^*⟦Λ⟧)).obj K ≅ (L((b)^*⟦Λ⟧)).obj K) := by
  subst h
  exact ⟨Iso.refl _⟩

/-- **Deligne's finiteness theorem for the nearby cycles of a model** (SGA 4½, [Th. finitude],
Thm. 3.2; for `ℚ̄_ℓ`-coefficients, Bhatt–Scholze §6.8): over the strictly henselian trait
`Spec k'⟦t⟧`, the nearby cycles `Ψ = Li^* Rj_* Lε^*` of a model of finite type whose
identification factors as `ε = j ≫ e` through the total space preserve bounded constructible
complexes: `Lε^* A ≅ Lj^* Le^* A`, the pullback `Le^* A` is bounded constructible, and the
geometric nearby cycles `Li^* Rj_* Lj^*` preserve bounded constructible complexes
(`NearbyCyclesModel.boundedConstructible_geometricNearbyCycles_obj`). -/
theorem preservesBoundedConstructible_of_exists_comp (M : NearbyCyclesModel X X'.left)
    (hM : M.IsTraitModel) (hε : ∃ e : M.total ⟶ X, M.j ≫ e = M.ε) :
    M.PreservesBoundedConstructible (Profinite.padicAlgClRingObj ℓ) := by
  obtain ⟨e, he⟩ := hε
  intro K hK
  have hB := boundedConstructible_leftDerivedUpperStar_obj_of_scheme
    (Profinite.padicAlgClRingObj ℓ) e K hK
  have i₁ := (nonempty_leftDerivedUpperStar_obj_iso_of_eq (Profinite.padicAlgClRingObj ℓ)
    he.symm K).some
  have i₂ := (leftDerivedUpperStarComp (Profinite.padicAlgClRingObj ℓ) M.j e).app K
  exact (boundedConstructible _).prop_of_iso
    ((L((M.i)^*⟦Profinite.padicAlgClRingObj ℓ⟧)).mapIso
      ((R((M.j)_*⟦Profinite.padicAlgClRingObj ℓ⟧)).mapIso (i₁ ≪≫ i₂)).symm)
    (boundedConstructible_geometricNearbyCycles_obj M hM hB)

end NearbyCyclesModel

end AlgebraicGeometry.ProEtale.CondensedRing
