/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import Mathlib.Algebra.Homology.QuasiIso
import WeilConjectures.AlgebraicGeometry.Picard.KFlatResolutionIndependentCoefficients
import WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import WeilConjectures.Algebra.Homology.CyclePullbackResolution
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import Mathlib.Algebra.Homology.Refinements

/-! # Bounded flat replacements at independent universes

Source: Stacks Project, Tags 06YS, 05T7 and 03EW; latest blueprint,
sk-i-additivity.proof.md, Filtered operations, successive flat resolutions.
(blueprint: lem-trf-finite-filtered-bounded-flat-replacement).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u v w
open CategoryTheory CategoryTheory.Limits MonoidalCategory
namespace CochainComplex
variable {C : Type u} [Category.{v} C] [EssentiallySmall.{w} C]
  {J : GrothendieckTopology C} (R : Sheaf J CommRingCat.{w})

/-- A bounded-above module-sheaf complex has a flat replacement with the same upper bound.
Source: Stacks Project, Tags 06YS and 05T7, using the free-sheaf cover of Tag 03EW.
Proof: take the existing functorial categorical flat cover, apply descending cycle-pullback
construction with the specified bound, and convert categorical flatness through the site-tensor
comparison. The local compatible-pair lifting property gives injectivity on homology by lifting
boundaries one degree earlier, and surjectivity by lifting a cycle together with zero in the next
degree. Both arguments use the generic abelian refinement criteria, so no equality of site and
coefficient universes is required. The zero object and all degrees above the bound are included.
(blueprint: lem-trf-finite-filtered-bounded-flat-replacement). -/
theorem exists_finiteFiltered_boundedFlatReplacement
    (K : CochainComplex (ringedSiteModules.{w}
      ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R)) ℤ)
    (N : ℤ) (hK : ∀ n : ℤ, N < n → IsZero (K.X n)) :
    ∃ (P : CochainComplex (ringedSiteModules.{w}
        ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R)) ℤ)
      (f : P ⟶ K),
      (∀ n : ℤ, SheafOfModules.IsFlatOnSite (J := J) (R := R) (P.X n)) ∧
      (∀ n : ℤ, N < n → IsZero (P.X n)) ∧ QuasiIso f := by
  let A := ringedSiteModules.{w}
    ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R)
  let := SheafOfModules.isMonoidal_W_independentCoefficients R
  let := SheafOfModules.monoidalCategory R
  let := SheafOfModules.symmetricCategory R
  let := SheafOfModules.tensorPreadditive R
  obtain ⟨Λ⟩ := SheafOfModules.hasFunctorialFlatResolution_kfi (R := R)
  let T := Λ.F ⋙ ObjectProperty.flat.ι
  have hzero (X : A) (hX : IsZero X) : ObjectProperty.flat X :=
    ObjectProperty.flat_of_isZero hX
  obtain ⟨Q, ε, hQ⟩ := exists_functorial_cyclePullback_construction
    ObjectProperty.flat hzero T Λ.π (fun X ↦ (Λ.F.obj X).property)
    (fun X ↦ Λ.epi_π_app X) N
  let B : ObjectProperty (CochainComplex A ℤ) :=
    fun L ↦ ∀ n : ℤ, N < n → IsZero (L.X n)
  let F : B.FullSubcategory := ⟨K, hK⟩
  refine ⟨Q.obj F, ε.app F, ?_, (hQ F).2.1, ?_⟩
  · intro n
    exact (exactFunctor _ _).prop_of_iso
      (SheafOfModules.siteSheafTensorRightIso R ((Q.obj F).X n)).symm ((hQ F).1 n).2
  · rw [quasiIso_iff]
    intro i
    rw [quasiIsoAt_iff_isIso_homologyMap, isIso_iff_mono_and_epi]
    constructor
    · rw [HomologicalComplex.mono_homologyMap_iff_up_to_refinements
        (ε.app F) (i - 1) i (i + 1) (by simp) (by simp)]
      intro B x hx y hy
      have hlift := (hQ F).2.2 (i - 1)
      rw [show i - 1 + 1 = i by omega] at hlift
      obtain ⟨B', p, hp, z, _, hz⟩ := hlift B x y hx hy
      exact ⟨B', p, hp, z, by simpa using hz.symm⟩
    · rw [HomologicalComplex.epi_homologyMap_iff_up_to_refinements
        (ε.app F) (i - 1) i (i + 1) (by simp) (by simp)]
      intro B y hy
      obtain ⟨B', p, hp, z, hz, hd⟩ :=
        (hQ F).2.2 i B 0 y (by simp) (by simpa using hy.symm)
      exact ⟨B', p, hp, z, by simpa using hd, 0, by simpa using hz.symm⟩
end CochainComplex
