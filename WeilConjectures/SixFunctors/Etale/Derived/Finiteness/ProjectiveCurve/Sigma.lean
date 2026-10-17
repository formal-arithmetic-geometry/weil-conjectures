/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.ConstructibleSheaf.Monoidal
public import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.FiniteCancellation
public import WeilConjectures.SixFunctors.OpenClosed.ClosedImmersion
public import WeilConjectures.SixFunctors.OpenClosed.Vanishing
public import WeilConjectures.SixFunctors.OpenClosed.Conservative

/-!
# Direct images out of a finite disjoint union

Let `Y = ∐ₐ Yₐ` be a finite disjoint union of schemes, with inclusions `ιₐ : Yₐ ⟶ Y`, which are
open and closed immersions. Every étale sheaf `F` on `Y` is the direct sum of the
`ιₐ_* ιₐ^* F` (`AlgebraicGeometry.Etale.isIso_biproductLift_unit_sigmaι`), so the higher direct
images along `h : Y ⟶ S` are the direct sums of those along the `ιₐ ≫ h`. In particular they
are constructible as soon as those along every `ιₐ ≫ h` are
(`AlgebraicGeometry.Etale.isConstructibleSheaf_homology_rightDerivedLowerStar_sigma`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

variable {ι : Type u} [Finite ι] (Y : ι → Scheme.{u})

/-- The inclusion of a member of a finite disjoint union of schemes is a closed immersion: its
range is the complement of the union of the finitely many other ranges, which are open. -/
instance isClosedImmersion_sigmaι (a : ι) : IsClosedImmersion (Sigma.ι Y a) := by
  refine IsClosedImmersion.of_isPreimmersion _ ?_
  have : Set.range (Sigma.ι Y a).base = ⋂ b ∈ ({a}ᶜ : Set ι), (Set.range (Sigma.ι Y b).base)ᶜ := by
    ext x
    obtain ⟨⟨c, y⟩, rfl⟩ := (sigmaMk Y).surjective x
    simp only [sigmaMk_mk, Set.mem_range, Set.mem_iInter, Set.mem_compl_iff, Set.mem_singleton_iff,
      not_exists]
    refine ⟨?_, fun h ↦ ?_⟩
    · rintro ⟨z, hz⟩ b hb w hw
      rw [← hw, sigmaι_eq_iff] at hz
      exact hb (congrArg Sigma.fst hz).symm
    · by_cases hc : c = a
      · subst hc
        exact ⟨y, rfl⟩
      · exact (h c hc y rfl).elim
  rw [this]
  exact isClosed_biInter fun b _ ↦ (Sigma.ι Y b).isOpenEmbedding.isOpen_range.isClosed_compl

instance isFinite_sigmaι (a : ι) : IsFinite (Sigma.ι Y a) :=
  ((IsClosedImmersion.iff_isFinite_and_mono _).1 inferInstance).1

namespace Etale

open _root_.DerivedCategory

variable {Λ : Type (u + 1)} [CommRing Λ]

/-- A morphism into a finite biproduct whose components vanish except one, which is an
isomorphism, is an isomorphism. -/
lemma isIso_biproduct_lift_of_isZero {C : Type*} [Category* C] [Preadditive C]
    {J : Type*} [Finite J] {f : J → C} [HasBiproduct f] {P : C}
    (g : ∀ j, P ⟶ f j) (b : J) [IsIso (g b)] (hz : ∀ j, j ≠ b → IsZero (f j)) :
    IsIso (biproduct.lift g) := by
  classical
  refine ⟨⟨biproduct.π f b ≫ inv (g b), by simp, ?_⟩⟩
  ext j
  by_cases hj : j = b
  · subst hj
    simp
  · exact (hz j hj).eq_of_tgt _ _

/-- **A sheaf on a finite disjoint union is the direct sum of its restrictions.** For a sheaf
`F` on `∐ₐ Yₐ`, the morphism `F ⟶ ⨁ₐ ιₐ_* ιₐ^* F` assembled from the units of the adjunctions
`ιₐ^* ⊣ ιₐ_*` is an isomorphism: after pullback along `ι_b` the components with `a ≠ b` vanish,
the ranges being disjoint, and the component `a = b` is inverse to the counit, which is an
isomorphism since `ι_b` is a closed immersion. -/
lemma isIso_biproductLift_unit_sigmaι
    (F : Sheaf (∐ Y).smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    IsIso (biproduct.lift fun a ↦
      (Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) (Sigma.ι Y a)).unit.app F) := by
  classical
  refine Etale.isIso_of_isIso_upperStar_map_of_jointlySurjective (ModuleCat.{u + 1} Λ)
    (fun a ↦ Sigma.ι Y a) (fun x ↦ ?_) _ fun b ↦ ?_
  · obtain ⟨⟨a, y⟩, rfl⟩ := (sigmaMk Y).surjective x
    exact ⟨a, y, by simp⟩
  let P := (Sigma.ι Y b)^*[ModuleCat.{u + 1} Λ]
  let G := fun a ↦ (Sigma.ι Y a)_*[ModuleCat.{u + 1} Λ].obj
    ((Sigma.ι Y a)^*[ModuleCat.{u + 1} Λ].obj F)
  let η : ∀ a, F ⟶ G a := fun a ↦
    (Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) (Sigma.ι Y a)).unit.app F
  have hη : IsIso (P.map (η b)) := by
    have h := (Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ)
      (Sigma.ι Y b)).left_triangle_components F
    have : IsIso (P.map (η b) ≫ (Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ)
        (Sigma.ι Y b)).counit.app (P.obj F)) := by
      rw [h]
      exact IsIso.id _
    exact IsIso.of_isIso_comp_right _
      ((Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) (Sigma.ι Y b)).counit.app _)
  have hz : ∀ a, a ≠ b → IsZero ((P.obj ∘ G) a) := fun a hab ↦
    Etale.isZero_upperStar_lowerStar_of_disjoint_range (ModuleCat.{u + 1} Λ) (Sigma.ι Y b)
      (Sigma.ι Y a) (Set.disjoint_left.2 (by
        rintro _ ⟨x, rfl⟩ ⟨y, hy⟩
        rw [sigmaι_eq_iff] at hy
        exact hab (congrArg Sigma.fst hy))) _
  have := isIso_biproduct_lift_of_isZero (f := P.obj ∘ G) (fun a ↦ P.map (η a)) b hz
  have e : P.map (biproduct.lift η) ≫ (P.mapBiproduct G).hom =
      biproduct.lift (f := P.obj ∘ G) fun a ↦ P.map (η a) := by
    refine biproduct.hom_ext _ _ fun a ↦ ?_
    simp [← Functor.map_comp]
  have : IsIso (P.map (biproduct.lift η) ≫ (P.mapBiproduct G).hom) := by
    rw [e]
    infer_instance
  have h2 : IsIso (P.map (biproduct.lift η)) := IsIso.of_isIso_comp_right _ (P.mapBiproduct G).hom
  exact h2

/-- **Higher direct images out of a finite disjoint union.** For `h : ∐ₐ Yₐ ⟶ S` and a sheaf
`F` on `∐ₐ Yₐ`, `Rᵠh_* F` is the direct sum of the `Rᵠ(ιₐ ≫ h)_*(ιₐ^* F)`. -/
noncomputable def homologyRightDerivedLowerStarSigmaIso {S : Scheme.{u}} (h : ∐ Y ⟶ S)
    (F : Sheaf (∐ Y).smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℤ) :
    (homologyFunctor _ q).obj ((R((h)_*[ModuleCat.{u + 1} Λ])).obj ((singleFunctor _ 0).obj F))
      ≅ ⨁ fun a ↦ (homologyFunctor _ q).obj ((R((Sigma.ι Y a ≫ h)_*[ModuleCat.{u + 1} Λ])).obj
        ((singleFunctor _ 0).obj ((Sigma.ι Y a)^*[ModuleCat.{u + 1} Λ].obj F))) :=
  let Φ := singleFunctor (Sheaf (∐ Y).smallEtaleTopology (ModuleCat.{u + 1} Λ)) 0 ⋙
    R((h)_*[ModuleCat.{u + 1} Λ]) ⋙ homologyFunctor _ q
  Φ.mapIso (@asIso _ _ _ _ (biproduct.lift fun a ↦
      (Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) (Sigma.ι Y a)).unit.app F)
      (isIso_biproductLift_unit_sigmaι Y F)) ≪≫
    Φ.mapBiproduct _ ≪≫ biproduct.mapIso fun a ↦ (homologyFunctor _ q).mapIso
      (rightDerivedLowerStarSingleLowerStarIso (Sigma.ι Y a) h _)

/-- **Constructibility of higher direct images out of a finite disjoint union.** If the
higher direct images `Rᵠ(ιₐ ≫ h)_*(ιₐ^* F)` along the members of a finite disjoint union are
constructible, so is `Rᵠh_* F`. -/
theorem isConstructibleSheaf_homology_rightDerivedLowerStar_sigma {S : Scheme.{u}}
    (h : ∐ Y ⟶ S) (F : Sheaf (∐ Y).smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℤ)
    (hY : ∀ a, IsConstructibleSheaf ((homologyFunctor _ q).obj
      ((R((Sigma.ι Y a ≫ h)_*[ModuleCat.{u + 1} Λ])).obj
        ((singleFunctor _ 0).obj ((Sigma.ι Y a)^*[ModuleCat.{u + 1} Λ].obj F))))) :
    IsConstructibleSheaf ((homologyFunctor _ q).obj
      ((R((h)_*[ModuleCat.{u + 1} Λ])).obj ((singleFunctor _ 0).obj F))) := by
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin ι
  let G := fun a ↦ (homologyFunctor _ q).obj ((R((Sigma.ι Y a ≫ h)_*[ModuleCat.{u + 1} Λ])).obj
    ((singleFunctor _ 0).obj ((Sigma.ι Y a)^*[ModuleCat.{u + 1} Λ].obj F)))
  have : ∀ j : Fin n, IsConstructibleSheaf (G (e.symm j)) := fun j ↦ hY _
  have := IsConstructibleSheaf.biproduct (fun j : Fin n ↦ G (e.symm j))
  exact IsConstructibleSheaf.of_iso ((biproduct.whiskerEquiv e.symm fun _ ↦ Iso.refl _) ≪≫
    (homologyRightDerivedLowerStarSigmaIso Y h F q).symm)

end Etale

end AlgebraicGeometry
