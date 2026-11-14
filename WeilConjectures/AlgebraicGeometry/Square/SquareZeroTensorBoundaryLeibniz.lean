/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SectionBoundaryExact
public import WeilConjectures.AlgebraicGeometry.TensorPullbackAdjunction
public import WeilConjectures.AlgebraicGeometry.Modules.ClearDenominators
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import WeilConjectures.AlgebraicGeometry.Square.SquareZeroTensorBoundaryProduct

/-! # The graded Leibniz recurrence for square-zero tensor boundaries

Source: Stacks Project, Tags 09MS and 0B8S.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
namespace AlgebraicGeometry.Scheme.Modules
universe u wC wD
attribute [local irreducible] RingedSpace.moduleCohomology
  RingedSpace.moduleSectionBoundary boundaryCoefficientCohomologyIso
  canonicalTensorBoundaryComparisons

/-- The degreewise canonical boundaries, transported through the kernel and closed-immersion
cohomology comparisons, satisfy the two-term Leibniz recurrence. This asserts only the
recurrence; the closed power formula requires a separate induction.

Source: Stacks Project, Tag 09MS, equation (30.17.5.1) and the direct-sum exact sequence following
it; Tag 0B8S, the Leibniz calculation for the connecting map. -/
theorem exists_square_zero_tensor_boundary_leibniz
    {X Z : Scheme.{u}} (j : Z ⟶ X) [IsClosedImmersion j]
    [HasDerivedCategory.{wC} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{wD}
      (ModuleCat.{u} ((moduleRings X.toRingedSpace).obj.obj (Opposite.op ⊤)))]
    (L : X.Modules) [L.IsInvertible] (hI : j.ker ^ 2 = ⊥)
    (n : ℕ) (s : (((tensorPullback j).obj L).tensorPow n).val.presheaf.obj
      (Opposite.op ⊤))
    (hshort : ∀ d : ℕ, (ShortComplex.kernelSequence
      ((Classical.choose (exists_tensorPullbackAdjunction j)).unit.app
        (L.tensorPow d))).ShortExact) :
    let F : Z.Modules := (tensorPullback j).obj (j.ker.toModules ⊗ L.tensorPow n)
    let N : Z.Modules := ((tensorPullback j).obj L).tensorPow n
    let H := RingedSpace.moduleCohomology Z.toRingedSpace 1
    let f := homOfGlobalSection N s
    ∃ a : ∀ e : ℕ, (tensorPullback j).obj (L.tensorPow (n * (e + 1))) ≅
        N.tensorPow (e + 1),
      ∃ b : ∀ e : ℕ, H.obj (show Z.Modules from F ⊗ N.tensorPow e) ≃+
          (RingedSpace.moduleCohomology X.toRingedSpace 1).obj
            (kernel ((Classical.choose (exists_tensorPullbackAdjunction j)).unit.app
              (L.tensorPow (n * (e + 1))))),
        ∃ c : ∀ e : ℕ, H.obj (show Z.Modules from F ⊗ N.tensorPow e),
          (∀ e : ℕ,
            RingedSpace.moduleSectionBoundary X.toRingedSpace
                (ShortComplex.kernelSequence
                  ((Classical.choose (exists_tensorPullbackAdjunction j)).unit.app
                    (L.tensorPow (n * (e + 1))))) (hshort (n * (e + 1)))
                ((tensorPowSection f (e + 1) ≫ (a e).inv).app ⊤ (1 : Γ(Z, ⊤))) =
              b e (c e)) ∧
          ∀ e : ℕ,
            c (e + 1) = H.map (mulTensorPowSection f F e 1) (c e) +
              H.map ((ρ_ F).inv ≫ F ◁ tensorPowSection f (e + 1))
                (H.map (ρ_ F).hom (c 0)) := by
  let F : Z.Modules := (tensorPullback j).obj (j.ker.toModules ⊗ L.tensorPow n)
  let H := RingedSpace.moduleCohomology Z.toRingedSpace 1
  let N : Z.Modules := ((tensorPullback j).obj L).tensorPow n
  let f := homOfGlobalSection N s
  let D : TensorBoundaryComparisonData j L n := canonicalTensorBoundaryComparisons j L hI n
  have hD : canonicalTensorBoundaryComparisons j L hI n = D := rfl
  let a : ∀ e : ℕ, (tensorPullback j).obj (L.tensorPow (n * (e + 1))) ≅
      N.tensorPow (e + 1) := D.a
  let b : ∀ e : ℕ, H.obj (show Z.Modules from F ⊗ N.tensorPow e) ≃+
      (RingedSpace.moduleCohomology X.toRingedSpace 1).obj
        (kernel ((Classical.choose (exists_tensorPullbackAdjunction j)).unit.app
          (L.tensorPow (n * (e + 1))))) :=
    fun e ↦ Iso.addCommGroupIsoToAddEquiv (D.k e)
  let δ : ∀ e : ℕ,
      (RingedSpace.moduleCohomology X.toRingedSpace 1).obj
        (kernel ((Classical.choose (exists_tensorPullbackAdjunction j)).unit.app
          (L.tensorPow (n * (e + 1))))) := fun e ↦
    RingedSpace.moduleSectionBoundary.{u, wC, wD} X.toRingedSpace
      (ShortComplex.kernelSequence
        ((Classical.choose (exists_tensorPullbackAdjunction j)).unit.app
          (L.tensorPow (n * (e + 1))))) (hshort (n * (e + 1)))
      ((tensorPowSection f (e + 1) ≫ (a e).inv).app ⊤ (1 : Γ(Z, ⊤)))
  let c : ∀ e : ℕ, H.obj (show Z.Modules from F ⊗ N.tensorPow e) :=
    fun e ↦ (b e).symm (δ e)
  have hc (e : ℕ) : δ e = b e (c e) := ((b e).apply_symm_apply (δ e)).symm
  refine ⟨a, b, c, ?_, ?_⟩
  · intro e
    exact hc e
  · intro e
    apply transportedTensorBoundary_product.{u, wC, wD} j L hI n hshort D hD e f
      (tensorPowSection f (e + 1)) (c e) (c 0) (c (e + 1))
    · exact hc e
    · exact hc 0
    · exact hc (e + 1)

end AlgebraicGeometry.Scheme.Modules
