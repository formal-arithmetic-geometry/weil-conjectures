/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.ConstructibleSheaf.Defs
public import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper
public import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.FiniteCancellation
import WeilConjectures.ConstructibleSheaf.Monoidal
import WeilConjectures.Mathlib.CategoryTheory.Limits.Shapes.Products
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Conservative
import WeilConjectures.SixFunctors.OpenClosed.Vanishing

/-!
# Higher direct images out of a finite disjoint union, and proper base change

- `AlgebraicGeometry.Etale.isConstructibleSheaf_homology_rightDerivedLowerStar_sigma`: for
  `v : ∐ₐ Yₐ ⟶ B` with finitely many summands, `Rᵠv_* G` is constructible as soon as every
  `Rᵠ(ιₐ ≫ v)_*(ιₐ^* G)` is, since `G ≅ ⨁ₐ ιₐ_* ιₐ^* G` and each summand inclusion `ιₐ` is a
  closed immersion.
- `AlgebraicGeometry.Etale.upperStarHomologyRightDerivedLowerStarIsoOfIsProper`: proper base
  change for the higher direct images `Rᵠf_* F` of a sheaf of modules over a finite ring.
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

/-- The inclusion of a summand of a finite disjoint union of schemes is a closed immersion. -/
instance Scheme.isClosedImmersion_sigmaι {σ : Type u} [Finite σ] (Y : σ → Scheme.{u})
    (a : σ) : IsClosedImmersion (Sigma.ι Y a) := by
  refine IsClosedImmersion.of_isPreimmersion _ ?_
  have : Set.range (Sigma.ι Y a) = sigmaMk Y '' Set.range (Sigma.mk a) := by
    ext x
    simp [sigmaMk_mk]
  rw [this]
  exact (sigmaMk Y).isClosedMap _ isClosed_range_sigmaMk

namespace Etale

variable {Λ : Type (u + 1)} [CommRing Λ]

/-- **Proper base change for higher direct images.** For a cartesian square `g ≫ f = f ≫ g`
with `f` proper and a sheaf `F` of modules over a finite ring, `g^* Rᵠf_* F ≅ Rᵠf_*(g^* F)`,
by the proper base change theorem
(`AlgebraicGeometry.Etale.isIso_baseChange_of_isProper_of_torsionHomology`). -/
noncomputable def upperStarHomologyRightDerivedLowerStarIsoOfIsProper [Finite Λ]
    {X' X Y' Y : Scheme.{u}}
    {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y} (sq : IsPullback g' f' f g) [IsProper f]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℤ) :
    (g)^*[ModuleCat.{u + 1} Λ].obj ((_root_.DerivedCategory.homologyFunctor _ q).obj
      ((R((f)_*[ModuleCat.{u + 1} Λ])).obj ((_root_.DerivedCategory.singleFunctor _ 0).obj F))) ≅
    (_root_.DerivedCategory.homologyFunctor _ q).obj
      ((R((f')_*[ModuleCat.{u + 1} Λ])).obj
        ((_root_.DerivedCategory.singleFunctor _ 0).obj ((g')^*[ModuleCat.{u + 1} Λ].obj F))) :=
  let K := (DerivedCategory.Plus.singleFunctor _ 0).obj F
  have := Etale.isIso_baseChange_of_isProper_of_torsionHomology Λ sq K
    (Etale.DerivedCategory.Plus.moduleTorsionHomology_of_isTorsion Λ X isAddTorsion_of_finite K)
  (g)^*[ModuleCat.{u + 1} Λ].mapIso ((_root_.DerivedCategory.homologyFunctor _ q).mapIso
      (((f)_*[ModuleCat.{u + 1} Λ]).rightDerivedFunctorPlusCompatibility.app K).symm) ≪≫
    ((g)^*[ModuleCat.{u + 1} Λ].mapDerivedCategoryPlusHomologyFunctorIso q).app _ ≪≫
    (DerivedCategory.Plus.homologyFunctor _ q).mapIso
      (asIso ((Etale.derivedBaseChangeMapPlus (ModuleCat.{u + 1} Λ) sq.toCommSq).app K)) ≪≫
    (DerivedCategory.Plus.homologyFunctor _ q).mapIso
      (((f')_*[ModuleCat.{u + 1} Λ]).rightDerivedFunctorPlus.mapIso
        (((g')^*[ModuleCat.{u + 1} Λ].mapDerivedCategoryPlusSingleFunctor 0).app F)) ≪≫
    (_root_.DerivedCategory.homologyFunctor _ q).mapIso
      (((f')_*[ModuleCat.{u + 1} Λ]).rightDerivedFunctorPlusCompatibility.app _)

/-- A morphism of étale sheaves which becomes an isomorphism after pullback along every member of
a jointly surjective family of étale morphisms is an isomorphism. -/
lemma isIso_of_forall_isIso_upperStar_map {X : Scheme.{u}} {ι : Type*} {W : ι → Scheme.{u}}
    (g : ∀ i, W i ⟶ X) [∀ i, Etale (g i)] (hg : ⋃ i, Set.range (g i).base = Set.univ)
    {F G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)} (φ : F ⟶ G)
    (h : ∀ i, IsIso ((g i)^*[ModuleCat.{u + 1} Λ].map φ)) : IsIso φ := by
  refine Etale.isIso_of_isIso_localizationRestriction _ φ g hg fun i ↦ ?_
  let r := Etale.upperStarIsoLocalizationRestriction (ModuleCat.{u + 1} Λ) (g i) inferInstance
  have h' := r.hom.naturality φ
  rw [← cancel_epi (r.inv.app _), Iso.inv_hom_id_app_assoc] at h'
  rw [← h']
  have := h i
  infer_instance

/-- A morphism `biproduct.lift g` into a biproduct is an isomorphism if one component `g t` is and
all other summands are zero. -/
lemma _root_.CategoryTheory.Limits.isIso_biproduct_lift_of_isZero {β : Type*} {C : Type*}
    [Category* C] [Preadditive C] {f : β → C} [HasBiproduct f] {A : C} (g : ∀ b, A ⟶ f b)
    (t : β) (ht : IsIso (g t)) (hz : ∀ b, b ≠ t → IsZero (f b)) : IsIso (biproduct.lift g) := by
  classical
  refine ⟨⟨biproduct.π f t ≫ inv (g t), by simp, biproduct.hom_ext _ _ fun b ↦ ?_⟩⟩
  by_cases h : b = t
  · subst h
    simp
  · exact (hz b h).eq_of_tgt _ _

attribute [local instance] Abelian.hasFiniteBiproducts in
/-- **A sheaf on a finite disjoint union is the sum of its restrictions to the summands**: for
`ιₐ : Yₐ ⟶ ∐ₐ Yₐ`, the units `G ⟶ ιₐ_* ιₐ^* G` induce an isomorphism `G ≅ ⨁ₐ ιₐ_* ιₐ^* G`. -/
lemma isIso_biproductLift_unit_sigmaι {σ : Type u} [Finite σ] (Y : σ → Scheme.{u})
    (G : Sheaf (∐ Y).smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    IsIso (biproduct.lift fun a ↦
      (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) (Sigma.ι Y a)).unit.app G) := by
  classical
  refine isIso_of_forall_isIso_upperStar_map (Sigma.ι Y) ?_ _ fun t ↦ ?_
  · refine Set.eq_univ_of_forall fun x ↦ Set.mem_iUnion.2 ?_
    obtain ⟨⟨s, y⟩, rfl⟩ := (sigmaMk Y).surjective x
    exact ⟨s, y, by simp [sigmaMk_mk]⟩
  have hcomp : ((Sigma.ι Y t)^*[ModuleCat.{u + 1} Λ].map (biproduct.lift fun a ↦
      (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) (Sigma.ι Y a)).unit.app G) ≫
      ((Sigma.ι Y t)^*[ModuleCat.{u + 1} Λ].mapBiproduct _).hom) =
      biproduct.lift fun a ↦ (Sigma.ι Y t)^*[ModuleCat.{u + 1} Λ].map
        ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) (Sigma.ι Y a)).unit.app G) := by
    refine biproduct.hom_ext _ _ fun a ↦ ?_
    rw [Category.assoc]
    erw [biproduct.lift_π, biproduct.lift_π]
    erw [Functor.mapBicone_π, ← Functor.map_comp, biproduct.bicone_π, biproduct.lift_π]
  rw [← isIso_comp_right_iff _ ((Sigma.ι Y t)^*[ModuleCat.{u + 1} Λ].mapBiproduct _).hom, hcomp]
  refine isIso_biproduct_lift_of_isZero _ t ?_ fun s hst ↦ ?_
  · have h := (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ)
      (Sigma.ι Y t)).left_triangle_components G
    have : IsIso ((Sigma.ι Y t)^*[ModuleCat.{u + 1} Λ].map
        ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) (Sigma.ι Y t)).unit.app G) ≫
        (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) (Sigma.ι Y t)).counit.app _) := by
      rw [h]
      exact IsIso.id _
    exact IsIso.of_isIso_comp_right _
      ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) (Sigma.ι Y t)).counit.app _)
  · refine Etale.isZero_upperStar_lowerStar_of_disjoint_range _ (Sigma.ι Y t) (Sigma.ι Y s)
      (Set.disjoint_left.2 ?_) _
    rintro x ⟨a, rfl⟩ ⟨b, hb⟩
    exact hst (congrArg Sigma.fst ((sigmaι_eq_iff Y s t b a).mp hb))

attribute [local instance] Abelian.hasFiniteBiproducts in
/-- **Higher direct images out of a finite disjoint union.** For `v : ∐ₐ Yₐ ⟶ B` and a sheaf `G`
on `∐ₐ Yₐ`, `Rᵠv_* G ≅ ⨁ₐ Rᵠ(ιₐ ≫ v)_*(ιₐ^* G)`; hence `Rᵠv_* G` is constructible if every
`Rᵠ(ιₐ ≫ v)_*(ιₐ^* G)` is. -/
theorem isConstructibleSheaf_homology_rightDerivedLowerStar_sigma [Finite Λ] {σ : Type u}
    [Finite σ] {Y : σ → Scheme.{u}} {B : Scheme.{u}} (v : ∐ Y ⟶ B)
    (G : Sheaf (∐ Y).smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℤ)
    (h : ∀ a, IsConstructibleSheaf ((_root_.DerivedCategory.homologyFunctor _ q).obj
      ((R((Sigma.ι Y a ≫ v)_*[ModuleCat.{u + 1} Λ])).obj
        ((_root_.DerivedCategory.singleFunctor _ 0).obj
          ((Sigma.ι Y a)^*[ModuleCat.{u + 1} Λ].obj G))))) :
    IsConstructibleSheaf ((_root_.DerivedCategory.homologyFunctor _ q).obj
      ((R((v)_*[ModuleCat.{u + 1} Λ])).obj
        ((_root_.DerivedCategory.singleFunctor _ 0).obj G))) := by
  let Φ := _root_.DerivedCategory.singleFunctor
    (Sheaf (∐ Y).smallEtaleTopology (ModuleCat.{u + 1} Λ)) 0 ⋙
      ((v)_*[ModuleCat.{u + 1} Λ]).rightDerivedFunctor ⋙
      _root_.DerivedCategory.homologyFunctor _ q
  let K : σ → Sheaf B.smallEtaleTopology (ModuleCat.{u + 1} Λ) := fun a ↦
    Φ.obj ((Sigma.ι Y a)_*[ModuleCat.{u + 1} Λ].obj ((Sigma.ι Y a)^*[ModuleCat.{u + 1} Λ].obj G))
  have hK (a : σ) : IsConstructibleSheaf (K a) :=
    have := h a
    IsConstructibleSheaf.of_iso ((_root_.DerivedCategory.homologyFunctor _ q).mapIso
      (rightDerivedLowerStarSingleLowerStarIso (Sigma.ι Y a) v _)).symm
  let e := Finite.equivFin σ
  have : IsConstructibleSheaf (⨁ fun j ↦ K (e.symm j)) := IsConstructibleSheaf.biproduct _
  have : IsConstructibleSheaf (⨁ Φ.obj ∘ fun a ↦
      ((Sigma.ι Y a)^*[ModuleCat.{u + 1} Λ] ⋙ (Sigma.ι Y a)_*[ModuleCat.{u + 1} Λ]).obj G) :=
    IsConstructibleSheaf.of_iso (F := ⨁ fun j ↦ K (e.symm j))
      (biproduct.whiskerEquiv e.symm fun _ ↦ Iso.refl _)
  have := isIso_biproductLift_unit_sigmaι Y G
  exact IsConstructibleSheaf.of_iso ((Φ.mapBiproduct _).symm ≪≫ Φ.mapIso (asIso (biproduct.lift
    fun a ↦ (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) (Sigma.ι Y a)).unit.app G)).symm)

end Etale

end AlgebraicGeometry
