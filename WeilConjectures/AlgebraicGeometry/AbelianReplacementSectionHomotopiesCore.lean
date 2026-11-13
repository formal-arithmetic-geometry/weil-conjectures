/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import WeilConjectures.AlgebraicGeometry.AbelianCounitResolutionCalculation
import WeilConjectures.AlgebraicGeometry.AbelianReplacementSectionHomotopiesCoreParts
import WeilConjectures.Algebra.Homology.MappingCylinderSplitFactorization
import WeilConjectures.Algebra.Homology.LiftToInjectiveUniqueUpToHomotopy
import Mathlib.Algebra.Homology.ModelCategory.Injective
/-! # Constructing the section homotopies before acyclicity

Source: Stacks Project, Tags 013P, 013S and 01FB.
-/

@[expose] public section
universe u
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits Opposite
noncomputable section
namespace AlgebraicGeometry.Scheme.Modules.ExtEdgeResolution
/-- Construction of the comparison map and its two homotopies; the quasi-isomorphism
property is supplied separately. No injectivity of the replacement K is required. -/
theorem abelian_replacement_section_homotopies_core {X Y : Scheme.{u}} (f : X ⟶ Y)
    {F : X.Modules} (I : InjectiveResolution F)
    (J : InjectiveResolution ((pushforward f).obj F)) (K : CochainComplex Y.Modules ℕ)
    (l : ((pushforward f).mapHomologicalComplex (.up ℕ)).obj I.cocomplex ⟶ K)
    (hl : QuasiIso l) (β : J.cocomplex ⟶ K)
    (hβ : J.ι.f 0 ≫ β.f 0 = (pushforward f).map (I.ι.f 0) ≫ l.f 0)
    (a : ((moduleSections X).mapHomologicalComplex (.up ℕ)).obj I.cocomplex ≅
      ((moduleSections Y).mapHomologicalComplex (.up ℕ)).obj
        (((pushforward f).mapHomologicalComplex (.up ℕ)).obj I.cocomplex))
    (ha : ∀ n : ℕ, a.inv.f n = (presheaf (I.cocomplex.X n)).map
      (eqToHom (by simp) : (⊤ : X.Opens) ⟶ f ⁻¹ᵁ (⊤ : Y.Opens)).op) :
    ∃ q : ((moduleSections Y).mapHomologicalComplex (.up ℕ)).obj K ⟶
        ((abelianSections X).mapHomologicalComplex (.up ℕ)).obj
          (standardAbelianResolution X F).cocomplex,
      Nonempty (Homotopy
        (((moduleSections Y).mapHomologicalComplex (.up ℕ)).map β ≫ q)
        (counitSectionMap f F J)) ∧
      Nonempty (Homotopy
        ((a.hom ≫ ((moduleSections Y).mapHomologicalComplex (.up ℕ)).map l) ≫ q)
        (((abelianSections X).mapHomologicalComplex (.up ℕ)).map
          (forgottenResolutionMap X I))) := by
  obtain ⟨q, hq, hr⟩ := second_section_homotopy_of_counit f I J K l hl β hβ
  exact ⟨q, hq, hr a ha⟩
end AlgebraicGeometry.Scheme.Modules.ExtEdgeResolution
