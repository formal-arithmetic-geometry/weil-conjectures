/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.DerivedCategory.KInjective
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure

/-!
# Resolution independence of derived functors computed by K-injective resolutions

If `s : K ⟶ I` and `t : K ⟶ J` are two K-injective resolutions of a cochain complex `K`, then
`I` and `J` are isomorphic in the homotopy category. Consequently, for every additive functor
`G`, the complexes `G(I)` and `G(J)` have isomorphic cohomology: the groups `Hᵠ(T_ét, F)`
computed from a K-injective resolution of `F` do not depend on the chosen resolution.

## Main statements

- `CochainComplex.IsKInjective.nonempty_iso_quotient_obj`: two K-injective resolutions are
  isomorphic in the homotopy category.
- `CochainComplex.IsKInjective.nonempty_homology_iso`: their images under an additive functor
  have isomorphic cohomology.
-/

@[expose] public section

open CategoryTheory Limits DerivedCategory

namespace CochainComplex.IsKInjective

variable {C : Type*} [Category* C] [Abelian C] [HasDerivedCategory C]

/-- Two K-injective resolutions `s : K ⟶ I`, `t : K ⟶ J` of the same complex are isomorphic in
the homotopy category: the isomorphism `Q(I) ≅ Q(K) ≅ Q(J)` of the derived category lifts,
since `Qh` is bijective on morphisms with K-injective target. -/
theorem nonempty_iso_quotient_obj {K I J : CochainComplex C ℤ} (s : K ⟶ I) (t : K ⟶ J)
    [QuasiIso s] [QuasiIso t] [I.IsKInjective] [J.IsKInjective] :
    Nonempty ((HomotopyCategory.quotient C (.up ℤ)).obj I ≅
      (HomotopyCategory.quotient C (.up ℤ)).obj J) := by
  let e : Qh.obj ((HomotopyCategory.quotient C (.up ℤ)).obj I) ≅
      Qh.obj ((HomotopyCategory.quotient C (.up ℤ)).obj J) :=
    (quotientCompQhIso C).app I ≪≫ (asIso (Q.map s)).symm ≪≫ asIso (Q.map t) ≪≫
      (quotientCompQhIso C).symm.app J
  obtain ⟨a, ha⟩ := (Qh_map_bijective ((HomotopyCategory.quotient C (.up ℤ)).obj I) J).2 e.hom
  obtain ⟨b, hb⟩ := (Qh_map_bijective ((HomotopyCategory.quotient C (.up ℤ)).obj J) I).2 e.inv
  refine ⟨⟨a, b, (Qh_map_bijective _ I).1 ?_, (Qh_map_bijective _ J).1 ?_⟩⟩
  · rw [Functor.map_comp, ha, hb, e.hom_inv_id, CategoryTheory.Functor.map_id]
  · rw [Functor.map_comp, ha, hb, e.inv_hom_id, CategoryTheory.Functor.map_id]

/-- **Resolution independence.** If `s : K ⟶ I` and `t : K ⟶ J` are two K-injective resolutions
of a cochain complex `K` and `G` is an additive functor, then `Hᵠ(G(I)) ≅ Hᵠ(G(J))` for every
`q`: the two resolutions are homotopy equivalent, and `G` preserves homotopies. For
`G = Γ(T, -)` and `K = F[0]` this says that the étale cohomology groups `Hᵠ(T_ét, F)` do not
depend on the chosen K-injective resolution of `F`.
(blueprint: `prop-weil-pbc-cohomology-resolution-independent`) -/
theorem nonempty_homology_iso {D : Type*} [Category* D] [Abelian D] (G : C ⥤ D) [G.Additive]
    {K I J : CochainComplex C ℤ} (s : K ⟶ I) (t : K ⟶ J) [QuasiIso s] [QuasiIso t]
    [I.IsKInjective] [J.IsKInjective] (q : ℤ) :
    Nonempty (((G.mapHomologicalComplex _).obj I).homology q ≅
      ((G.mapHomologicalComplex _).obj J).homology q) := by
  obtain ⟨e⟩ := nonempty_iso_quotient_obj s t
  exact ⟨(HomotopyCategory.homologyFunctorFactors D (.up ℤ) q).symm.app _ ≪≫
    (HomotopyCategory.homologyFunctor D (.up ℤ) q).mapIso
      ((G.mapHomotopyCategoryFactors (.up ℤ)).symm.app I ≪≫
        (G.mapHomotopyCategory (.up ℤ)).mapIso e ≪≫
        (G.mapHomotopyCategoryFactors (.up ℤ)).app J) ≪≫
    (HomotopyCategory.homologyFunctorFactors D (.up ℤ) q).app _⟩

end CochainComplex.IsKInjective

namespace DerivedCategory

variable {C : Type*} [Category* C] [Abelian C] [HasDerivedCategory C]

/-- A morphism from an object of `D(C)` concentrated in degrees `> n` to an injective object of
`C` placed in degree `n` is zero: `Ext^{<0}`-vanishing against an injective, computed by the
K-injective single complex. -/
lemma eq_zero_of_isGE_of_injective {X : DerivedCategory C} (n : ℤ) [X.IsGE (n + 1)] {I : C}
    [Injective I] (f : X ⟶ (singleFunctor C n).obj I) : f = 0 := by
  obtain ⟨K, _, ⟨e⟩⟩ := X.exists_iso_Q_obj_of_isGE (n + 1)
  have : ∀ m, Injective (((HomologicalComplex.single C (ComplexShape.up ℤ) n).obj I).X m) :=
    fun m ↦ by
      by_cases hm : m = n
      · subst hm
        exact Injective.of_iso (HomologicalComplex.singleObjXSelf _ _ _).symm inferInstance
      · exact (HomologicalComplex.isZero_single_obj_X _ _ _ _ hm).injective
  have : CochainComplex.IsKInjective ((HomologicalComplex.single C (ComplexShape.up ℤ) n).obj I) :=
    CochainComplex.isKInjective_of_injective _ n
  obtain ⟨h', hh'⟩ := (CochainComplex.IsKInjective.Qh_map_bijective
    ((HomotopyCategory.quotient _ _).obj K)
    ((HomologicalComplex.single C (ComplexShape.up ℤ) n).obj I)).2
      (e.inv ≫ f ≫ ((singleFunctorIsoCompQ C n).app I).hom)
  obtain ⟨h, rfl⟩ := (HomotopyCategory.quotient _ _).map_surjective h'
  have h0 : h = 0 := by
    refine HomologicalComplex.hom_ext _ _ (fun m ↦ ?_)
    by_cases hm : m = n
    · subst hm
      exact (K.isZero_of_isStrictlyGE (m + 1) m (by omega)).eq_of_src _ _
    · exact (HomologicalComplex.isZero_single_obj_X _ _ _ _ hm).eq_of_tgt _ _
  rw [h0, Functor.map_zero, Functor.map_zero] at hh'
  rw [← cancel_epi e.inv, ← cancel_mono ((singleFunctorIsoCompQ C n).app I).hom,
    Category.assoc]
  exact hh'.symm.trans (by simp)

open Pretriangulated in
/-- Let `P ∈ D(C)` be concentrated in degrees `≥ 0` and `u : A[0] ⟶ P` induce an isomorphism on
`H⁰`. Then for an injective object `I` of `C`, precomposition with `u` is a bijection
`Hom(P, I[0]) ≃ Hom(A[0], I[0])`: the cone of `u` is concentrated in degrees `≥ 1`, and maps
from it and from its shift `[-1]` to `I[0]` vanish
(`DerivedCategory.eq_zero_of_isGE_of_injective`). -/
lemma bijective_comp_of_isIso_homologyMap {A : C} {P : DerivedCategory C} [P.IsGE 0]
    (u : (singleFunctor C 0).obj A ⟶ P) [hu : IsIso ((homologyFunctor C 0).map u)] {I : C}
    [Injective I] :
    Function.Bijective (fun h : P ⟶ (singleFunctor C 0).obj I ↦ u ≫ h) := by
  obtain ⟨Z, v, w, hT⟩ := distinguished_cocone_triangle u

  have hZ : Z.IsGE 1 := by
    rw [isGE_iff]
    intro i hi
    have hmono : ∀ j : ℤ, Mono ((homologyFunctor C j).map (Triangle.mk u v w).mor₁) := by
      intro j
      by_cases h : j = 0
      · subst h; exact (inferInstance : Mono ((homologyFunctor C 0).map u))
      · rcases lt_or_gt_of_ne h with h | h
        · exact (((singleFunctor C 0).obj A).isZero_of_isGE 0 j h).mono _
        · exact (((singleFunctor C 0).obj A).isZero_of_isLE 0 j h).mono _
    have hδ : HomologySequence.δ (Triangle.mk u v w) i (i + 1) rfl = 0 :=
      (HomologySequence.mono_homologyMap_mor₁_iff (Triangle.mk u v w) hT i (i + 1) rfl).1 (hmono _)
    have hepi : Epi ((homologyFunctor C i).map (Triangle.mk u v w).mor₂) :=
      (HomologySequence.epi_homologyMap_mor₂_iff (Triangle.mk u v w) hT i (i + 1) rfl).2 hδ
    have hzero : (homologyFunctor C i).map (Triangle.mk u v w).mor₂ = 0 := by
      rw [← HomologySequence.epi_homologyMap_mor₁_iff (Triangle.mk u v w) hT]
      by_cases h : i = 0
      · subst h; exact (inferInstance : Epi ((homologyFunctor C 0).map u))
      · exact (P.isZero_of_isGE 0 i (by omega)).epi _
    exact @Limits.IsZero.of_epi_eq_zero _ _ _ _ _ _ hepi hzero
  have : Z.IsGE 1 := hZ
  have : (Z⟦(-1 : ℤ)⟧).IsGE 2 := TStructure.t.isGE_shift Z 1 (-1) 2
  have hZ' : (Z⟦(-1 : ℤ)⟧).IsGE (0 + 1) := TStructure.t.isGE_of_ge _ _ 2 (by omega)
  have hZ'' : Z.IsGE (0 + 1) := hZ
  refine ⟨fun h₁ h₂ heq ↦ ?_, fun g ↦ ?_⟩
  · have h0 : u ≫ (h₁ - h₂) = 0 := by
      simp only [Preadditive.comp_sub]; exact sub_eq_zero.2 heq
    obtain ⟨g, hg⟩ := Triangle.yoneda_exact₂ (Triangle.mk u v w) hT (h₁ - h₂) h0
    rw [eq_zero_of_isGE_of_injective (X := Z) 0 g] at hg
    exact sub_eq_zero.1 (hg.trans (Limits.comp_zero))
  · obtain ⟨h, hh⟩ := Triangle.yoneda_exact₂ _ (inv_rot_of_distTriang _ hT) g
      (eq_zero_of_isGE_of_injective (X := Z⟦(-1 : ℤ)⟧) 0 _)
    exact ⟨h, hh.symm⟩

end DerivedCategory
