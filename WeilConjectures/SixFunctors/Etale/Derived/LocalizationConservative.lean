/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.Localization

/-!
# Detecting isomorphisms by open restriction and exceptional closed restriction

For a closed immersion `i : Z ⟶ X` with complementary open immersion `j : U ⟶ X`, a morphism
`φ` of `D(X_ét)` is an isomorphism as soon as `Lj^* φ` and `Ri^! φ` are: the supported
localization triangles `Ri_! Ri^! L ⟶ L ⟶ Rj_* Lj^* L ⟶` of source and target are related by a
morphism of triangles with middle component `φ`
(`AlgebraicGeometry.Etale.exists_triangleHom_supportedLocalization`).
-/

@[expose] public section

universe u' u

open CategoryTheory Limits Pretriangulated

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

namespace Etale

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [HasSmallSiteSheafify A] [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A]
  [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A] {U Z X : Scheme.{u}}

/-- A morphism `φ` of `D(X_ét)` is an isomorphism if its restriction `Lj^* φ` to an open `U` and
its exceptional restriction `Ri^! φ` to the closed complement `Z` of `U` are isomorphisms. -/
theorem isIso_of_isIso_leftDerivedUpperStar_map_of_isIso_rightDerivedUpperShriek_map
    (i : Z ⟶ X) (j : U ⟶ X) [IsClosedImmersion i] [HasCompactification i]
    [(R(i)_![A]).IsLeftAdjoint] [IsOpenImmersion j] (hij : Set.range i.base = (Set.range j.base)ᶜ)
    {L L' : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)} (φ : L ⟶ L')
    (hj : IsIso ((L((j)^*[A])).map φ)) (hi : IsIso ((R(i)^![A]).map φ)) :
    IsIso φ := by
  have hw := supportedLocalizationTriangle_mem_distTriang A i j hij L
  have hw' := supportedLocalizationTriangle_mem_distTriang A i j hij L'
  obtain ⟨τ, h₁, h₂, h₃⟩ := exists_triangleHom_supportedLocalization A i j
    (hij ▸ disjoint_compl_left) φ hw hw'
  have : IsIso τ.hom₁ := by
    rw [h₁]
    infer_instance
  have : IsIso τ.hom₃ := by
    rw [h₃]
    infer_instance
  rw [← h₂]
  exact isIso₂_of_isIso₁₃ τ hw hw' inferInstance inferInstance

end Etale

end AlgebraicGeometry
