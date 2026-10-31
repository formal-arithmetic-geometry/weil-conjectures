/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Perfect.PerfectCoefficientShriekMate
public import WeilConjectures.Algebra.Homology.SixFunctors.OrdinaryDerivedChangeOfRings
import WeilConjectures.AlgebraicGeometry.Perfect.PerfectScalarExceptionalExtensionIsIso
import WeilConjectures.AlgebraicGeometry.ExceptionalCoefficients.ExceptionalCoefficientMaps

/-! Naturality and the unit specialization for the perfect scalar exceptional transpose.
Source: the final naturality/specialization step (Step 9) of the parent node
(lem-sf-perfect-scalar-exceptional-extension); the unit identification is the
normalized scalar unit of Stacks 07A4
(blueprint: lem-sf-perfect-scalar-exceptional-extension-natural).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory
namespace AlgebraicGeometry.Etale

/-- The objectwise transpose assembles to the required natural isomorphism and
has the stated constant-unit specialization.
Source: Step 9 of the parent node (def-weil-pbc-adjunction-mate), Stacks 07A4 for the
scalar unit (blueprint: lem-sf-perfect-scalar-exceptional-extension-natural).

Proof.
1. Each component is invertible by `perfectScalarExceptionalExtensionMap_isIso`
   (lem-sf-perfect-scalar-exceptional-extension-isIso).
2. Naturality in N: for g : N ⟶ N', both composites are transposes under the adjunction
   L_B ⊣ F_B (the hom-equivalence is natural on both sides). Their transposes agree by
   naturality of the inverse compact-support comparison c⁻¹ and of the counit of L_R ⊣ F_R:
   L_B E_X F_R g ≫ c⁻¹ ≫ E_Y ε_{N'} = c⁻¹ ≫ E_Y (L_R F_R g ≫ ε_{N'}) = c⁻¹ ≫ E_Y ε_N ≫ E_Y g.
   The components therefore form a natural isomorphism whose hom has the given components.
3. At N = R_Y[0], compose the component with F_B applied to the normalized scalar unit
   identification E_Y(R_Y[0]) ≅ B_Y[0] of `ExceptionalCoefficients.unitIso`
   (def-pur-exceptional-coefficient-normalizations). -/
theorem perfectScalarExceptionalExtension_natural
    {R B : Type (u + 1)} [CommRing R] [CommRing B]
    (φ : R →+* B) {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsNoetherian X] [IsNoetherian Y]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (c : Compactification f)
    (hB : _root_.DerivedCategory.IsPerfectRingComplex
      ((_root_.DerivedCategory.singleFunctor (ModuleCat.{u + 1} R) 0).obj
        ((ModuleCat.restrictScalars φ).obj (ModuleCat.of B B))))
    {FR : DerivedCategoryModule R Y ⥤ DerivedCategoryModule R X}
    {FB : DerivedCategoryModule B Y ⥤ DerivedCategoryModule B X}
    (aR : rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} R) c ⊣ FR)
    (aB : rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} B) c ⊣ FB) :
    (∃ e : FR ⋙ scalarExtension φ X ≅ scalarExtension φ Y ⋙ FB,
      ∀ N : DerivedCategoryModule R Y,
        e.hom.app N =
          (aB.homEquiv _ _
            ((perfectCoefficientCompactSupportIso φ f c hB).inv.app (FR.obj N) ≫
              (scalarExtension φ Y).map (aR.counit.app N)))) ∧
      Nonempty ((scalarExtension φ X).obj (FR.obj (constantComplex R Y)) ≅
        FB.obj (constantComplex B Y)) := by
  have hiso := perfectScalarExceptionalExtensionMap_isIso φ f c hB aR aB
  refine ⟨⟨NatIso.ofComponents (fun N ↦ @asIso _ _ _ _ _ (hiso N)) ?_, fun N ↦ rfl⟩,
    ⟨@asIso _ _ _ _ _ (hiso (constantComplex R Y)) ≪≫
      FB.mapIso (ExceptionalCoefficients.unitIso φ Y)⟩⟩
  intro N N' g
  simp only [Functor.comp_obj, Functor.comp_map, Functor.id_obj, asIso_hom]
  apply (aB.homEquiv _ _).symm.injective
  rw [Adjunction.homEquiv_naturality_left_symm, Adjunction.homEquiv_naturality_right_symm]
  erw [Equiv.symm_apply_apply, Equiv.symm_apply_apply]
  have hc :
      (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} B) c).map
          ((scalarExtension φ X).map (FR.map g)) ≫
        (perfectCoefficientCompactSupportIso φ f c hB).inv.app (FR.obj N') =
      (perfectCoefficientCompactSupportIso φ f c hB).inv.app (FR.obj N) ≫
        (scalarExtension φ Y).map
          ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} R) c).map (FR.map g)) :=
    (perfectCoefficientCompactSupportIso φ f c hB).inv.naturality (FR.map g)
  rw [← Category.assoc, hc, Category.assoc, ← Functor.map_comp, aR.counit_naturality,
    Functor.map_comp, Category.assoc]

end AlgebraicGeometry.Etale
