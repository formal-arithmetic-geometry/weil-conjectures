/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.PurityFiniteSetting
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence

/-!
# Cohomology extraction from the affine-line triangle

Source: `literature/blueprint/latest/blueprint/sec-smooth-purity/`
`sk-lem-sp-reduction/lem-pur-gysin-structure.proof.md`, the long exact cohomology
sequence following the pushed-forward localization triangle
(blueprint: lem-pur-gysin-cohomology-extraction).
-/

@[expose] public section
set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open AlgebraicGeometry

namespace WeilConjectures.PurityFiniteSetting

set_option linter.unusedVariables false in
/--
The long exact cohomology sequence extracts the exceptional term from the affine-line
triangle.  The proof applies `lem-sf-derived-homology-long-exact` degree by degree:
the two vanishing hypotheses give vanishing of the first term away from degrees 0, 1,
2; exactness at degrees 0 and 1 and the assumed isomorphism on degree-zero cohomology
give their vanishing; and exactness in degree 1 makes the connecting map an isomorphism.
The shift convention from `def-weil-abstract-derived-category` identifies the surviving
term with degree-zero cohomology after shifting twice.

Source: `literature/blueprint/latest/blueprint/sec-smooth-purity/`
`sk-lem-sp-reduction/lem-pur-gysin-structure.proof.md`, the long exact cohomology
sequence following the pushed-forward localization triangle
(blueprint: lem-pur-gysin-cohomology-extraction).
-/
theorem gysin_cohomology_extraction
    (P : PurityFiniteSetting.{u})
    (Y : Scheme.{u})
    (a : Y ⟶ Spec (CommRingCat.of P.field.k))
    [IsSeparated a] [LocallyOfFiniteType a] [QuasiCompact a]
    (T : Triangle (DerivedCategory
      (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} P.Coefficient))))
    (L M : Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} P.Coefficient))
    (hT : T ∈ distTriang (DerivedCategory
      (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} P.Coefficient))))
    (hB : ∀ m : ℤ, m ≠ 0 → IsZero
      ((DerivedCategory.homologyFunctor
      (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} P.Coefficient)) m).obj T.obj₂))
    (eB : Nonempty ((DerivedCategory.homologyFunctor
      (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} P.Coefficient)) 0).obj T.obj₂ ≅ L))
    (hC : ∀ m : ℤ, m ≠ 0 → m ≠ 1 → IsZero
      ((DerivedCategory.homologyFunctor
      (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} P.Coefficient)) m).obj T.obj₃))
    (eC₀ : Nonempty ((DerivedCategory.homologyFunctor
      (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} P.Coefficient)) 0).obj T.obj₃ ≅ L))
    (eC₁ : Nonempty ((DerivedCategory.homologyFunctor
      (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} P.Coefficient)) 1).obj T.obj₃ ≅ M))
    [IsIso ((DerivedCategory.homologyFunctor
      (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} P.Coefficient)) 0).map T.mor₂)] :
    (∀ m : ℤ, m ≠ 2 → IsZero
      ((DerivedCategory.homologyFunctor
      (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} P.Coefficient)) m).obj T.obj₁)) ∧
      IsIso ((DerivedCategory.homologyFunctor
      (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} P.Coefficient)) 1).map T.mor₃) ∧
      (∀ m : ℤ, m ≠ 0 → IsZero
        ((DerivedCategory.homologyFunctor
          (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} P.Coefficient)) m).obj
          (T.obj₁⟦(2 : ℤ)⟧))) ∧
      Nonempty ((DerivedCategory.homologyFunctor
        (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} P.Coefficient)) 0).obj
        (T.obj₁⟦(2 : ℤ)⟧) ≅ M) := by
  let C := Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} P.Coefficient)
  let H := DerivedCategory.homologyFunctor C
  have hzeroB (m : ℤ) (hm : m ≠ 0) : IsZero ((H m).obj T.obj₂) := hB m hm
  have hzeroC (m : ℤ) (hm : m ≠ 0) (hm1 : m ≠ 1) :
      IsZero ((H m).obj T.obj₃) := hC m hm hm1
  have hzeroA (m : ℤ) (hm : m ≠ 0) (hm1 : m ≠ 1) (hm2 : m ≠ 2) :
      IsZero ((H m).obj T.obj₁) := by
    have hs := DerivedCategory.HomologySequence.exact₁ T hT (m - 1) m (by omega)
    apply hs.isZero_X₂
    · exact (hzeroC (m - 1) (by omega) (by omega)).eq_of_src _ _
    · exact (hzeroB m hm).eq_of_tgt _ _
  have hzeroA0 : IsZero ((H 0).obj T.obj₁) := by
    have hs₂ := DerivedCategory.HomologySequence.exact₂ T hT 0
    have hm₁ : (H 0).map T.mor₁ = 0 := by
      apply (hs₂.mono_g_iff).mp
      infer_instance
    have hs₁ := DerivedCategory.HomologySequence.exact₁ T hT (-1) 0 (by omega)
    apply hs₁.isZero_X₂
    · exact (hzeroC (-1) (by omega) (by omega)).eq_of_src _ _
    · exact hm₁
  have hzeroA1 : IsZero ((H 1).obj T.obj₁) := by
    have hs₃ := DerivedCategory.HomologySequence.exact₃ T hT 0 1 (by omega)
    have hδ0 : DerivedCategory.HomologySequence.δ T 0 1 (by omega) = 0 := by
      apply (hs₃.epi_f_iff).mp
      infer_instance
    have hs₁ := DerivedCategory.HomologySequence.exact₁ T hT 0 1 (by omega)
    apply hs₁.isZero_X₂
    · exact hδ0
    · exact (hzeroB 1 (by omega)).eq_of_tgt _ _
  have hδ1 : IsIso (DerivedCategory.HomologySequence.δ T 1 2 (by omega)) := by
    let δ := DerivedCategory.HomologySequence.δ T 1 2 (by omega)
    have hs₃ := DerivedCategory.HomologySequence.exact₃ T hT 1 2 (by omega)
    have hs₁ := DerivedCategory.HomologySequence.exact₁ T hT 1 2 (by omega)
    have hmono : Mono δ :=
      hs₃.mono_g ((hzeroB 1 (by omega)).eq_of_src _ _)
    have hepi : Epi δ :=
      hs₁.epi_f ((hzeroB 2 (by omega)).eq_of_tgt _ _)
    have := hmono
    have := hepi
    simpa only [δ] using (isIso_of_mono_of_epi δ)
  have hmor₃ : IsIso ((H 1).map T.mor₃) := by
    have hi := hδ1
    let g := ((H 0).shiftIso (1 : ℤ) 1 2 (by omega)).hom.app T.obj₁
    change IsIso ((H 1).map T.mor₃ ≫
      g) at hi
    have := hi
    exact IsIso.of_isIso_comp_right ((H 1).map T.mor₃) g
  refine ⟨?_, hmor₃, ?_, ?_⟩
  · intro m hm
    by_cases hm1 : m = 0
    · subst m; exact hzeroA0
    by_cases hm2 : m = 1
    · subst m; exact hzeroA1
    exact hzeroA m hm1 hm2 (by omega)
  · intro m hm
    have e : (H m).obj (T.obj₁⟦(2 : ℤ)⟧) ≅ (H (m + 2)).obj T.obj₁ := by
      dsimp [H]
      simpa only [DerivedCategory.shift_homologyFunctor, Functor.comp_obj] using
        ((DerivedCategory.homologyFunctor C 0).shiftIso (2 : ℤ) m (m + 2) (by omega)).app
          T.obj₁
    by_cases h0 : m + 2 = 0
    · exact IsZero.of_iso (h0 ▸ hzeroA0) e
    by_cases h1 : m + 2 = 1
    · exact IsZero.of_iso (h1 ▸ hzeroA1) e
    by_cases h2 : m + 2 = 2
    · exfalso; apply hm; omega
    exact IsZero.of_iso (hzeroA (m + 2) h0 h1 h2) e
  · obtain ⟨eC₁⟩ := eC₁
    have eShift : (H 0).obj (T.obj₁⟦(2 : ℤ)⟧) ≅ (H 2).obj T.obj₁ := by
      dsimp [H]
      simpa only [DerivedCategory.shift_homologyFunctor, Functor.comp_obj] using
        ((DerivedCategory.homologyFunctor C 0).shiftIso (2 : ℤ) (0 : ℤ) 2 (by omega)).app
          T.obj₁
    let eδ := asIso (DerivedCategory.HomologySequence.δ T 1 2 (show (1 : ℤ) + 1 = 2 from rfl))
    let eResult := eShift ≪≫ eδ.symm ≪≫ eC₁
    exact ⟨eResult⟩

end WeilConjectures.PurityFiniteSetting
