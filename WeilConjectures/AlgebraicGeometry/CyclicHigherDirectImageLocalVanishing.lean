/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Sites.Kummer
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence
import WeilConjectures.AlgebraicGeometry.AbelianHigherDirectImagePresheaf
import WeilConjectures.AlgebraicGeometry.CyclicDerivedHomCohomologyComparison
import Mathlib.CategoryTheory.Sites.LocallyBijective
import Mathlib.CategoryTheory.Sites.EpiMono

/-!
# Local vanishing of higher direct images with cyclic coefficients

Source: Stacks Project, Tag 03Q8, and the affine basis of the small etale site.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Etale

/-- Local annihilation of every cohomology class on affine etale objects makes the
higher direct image of a constant cyclic abelian sheaf zero.

Source: Stacks Project, Tag 03Q8; the vanishing argument in
`Etale.isZero_higherDirectImage_constantModSheaf_of_forall_exists`. -/
theorem isZero_cyclicHigherDirectImage_of_locally_zero {X Y : Scheme.{u}}
    (h : Y ⟶ X) (e q : ℕ)
    (H : ∀ ⦃U : Scheme.{u}⦄ (u : U ⟶ X) [Etale u] [IsAffine U]
      (ξ : Sheaf.H ((pullback h u).constantZMod e) q),
      ∃ (ι : Type u) (V : ι → Scheme.{u}) (v : ∀ i, V i ⟶ U), (∀ i, Etale (v i)) ∧
        (∀ x : U, ∃ i y, (v i).base y = x) ∧
        ∀ i, Etale.cohomologyMap (pullback.map h (v i ≫ u) h u (𝟙 Y) (v i) (𝟙 X) (by simp)
          (by simp)) _ q ξ = 0) :
    IsZero ((DerivedCategory.Plus.homologyFunctor
      (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℤ)).obj
      ((rightDerivedLowerStarPlus AddCommGrpCat.{u + 1} h).obj
        ((DerivedCategory.Plus.singleFunctor
          (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}) 0).obj (Y.constantZMod e)))) := by
  classical
  let P := (uliftYoneda.{u + 1} ⋙
    (Functor.whiskeringRight _ _ _).obj AddCommGrpCat.free ⋙
    presheafToSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} ⋙
    upperStar AddCommGrpCat.{u + 1} h ⋙ DerivedCategory.Plus.singleFunctor _ 0).op ⋙
      preadditiveYoneda.obj
        (((DerivedCategory.Plus.singleFunctor _ 0).obj (Y.constantZMod e))⟦(q : ℤ)⟧)
  have HC := exists_cyclicDerivedHom_cohomology_comparison h e q
  have hz : ∀ (W : X.Etale) (ξ : P.obj (op W)),
      Presheaf.equalizerSieve ξ (0 : P.obj (op W)) ∈ X.smallEtaleTopology W := by
    intro W ξ
    rw [Scheme.mem_smallEtaleTopology_iff]
    intro x
    obtain ⟨j, y, hy⟩ := W.left.affineCover.exists_eq x
    let A : X.Etale := Scheme.Etale.mk (W.left.affineCover.f j ≫ W.hom)
    let a : A ⟶ W := MorphismProperty.Over.homMk (W.left.affineCover.f j) rfl
    have : IsAffine ((𝟭 Scheme).obj A.left) := by
      change IsAffine (W.left.affineCover.X j)
      infer_instance
    obtain ⟨E, hE⟩ := HC A
    obtain ⟨ι, V, v, hv, hcov, hkill⟩ := H A.hom (E (P.map a.op ξ))
    have : ∀ i, Etale (v i) := hv
    obtain ⟨i, z, hz⟩ := hcov y
    let B : X.Etale := Scheme.Etale.mk (v i ≫ A.hom)
    let b : B ⟶ A := MorphismProperty.Over.homMk (v i) rfl
    refine ⟨B, b ≫ a, ?_, z, ?_⟩
    · change P.map (b ≫ a).op ξ = P.map (b ≫ a).op 0
      rw [map_zero]
      simp only [op_comp, Functor.map_comp, ConcreteCategory.comp_apply]
      exact hE B b (P.map a.op ξ) (hkill i)
    · change (W.left.affineCover.f j).base ((v i).base z) = x
      rw [hz, hy]
  have hzero : Presheaf.IsLocallySurjective X.smallEtaleTopology (0 : P ⟶ P) := by
    constructor
    intro W ξ
    apply X.smallEtaleTopology.superset_covering _ (hz W ξ)
    intro V v hv
    refine ⟨0, ?_⟩
    simpa only [Presheaf.equalizerSieve_apply, map_zero] using hv.symm
  let S := (presheafToSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj P
  have : PreservesLimitsOfSize.{u, u + 1} (forget AddCommGrpCat.{u + 1}) :=
    preservesLimitsOfSize_shrink.{u + 1, u + 1, u, u + 1} _
  have : X.smallEtaleTopology.HasSheafCompose (forget AddCommGrpCat.{u + 1}) :=
    inferInstance
  have : Presheaf.IsLocallySurjective X.smallEtaleTopology (0 : P ⟶ P) := hzero
  have : Sheaf.IsLocallySurjective (0 : S ⟶ S) := by
    have hh := (Presheaf.isLocallySurjective_presheafToSheaf_map_iff
      X.smallEtaleTopology (0 : P ⟶ P)).2 hzero
    simpa only [Functor.map_zero] using hh
  have : Epi (0 : S ⟶ S) :=
    (Sheaf.isLocallySurjective_iff_epi' (J := X.smallEtaleTopology)
      AddCommGrpCat.{u + 1} (0 : S ⟶ S)).1 inferInstance
  have hs : IsZero S := IsZero.of_epi_zero S S
  obtain ⟨I⟩ := nonempty_higherDirectImage_iso_sheafification_abelian_single h (q : ℤ)
    (Y.constantZMod e)
  exact hs.of_iso I.symm

end AlgebraicGeometry.Etale
