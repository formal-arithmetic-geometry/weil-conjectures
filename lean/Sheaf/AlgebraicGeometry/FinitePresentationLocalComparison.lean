/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V1
-/
module

public import Sheaf.Paper.DerivedHomMayerVietoris
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
import Sheaf.Algebra.Homology.RingedSpaceModuleExactnessLocalLifting

/-! # Local comparison of a finite presentation and a finite free epimorphism

Source: Stacks Project, Modules, Lemma 01BP(1), first paragraph of the proof.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry.RingedSpace

/-- Near any point, a finite presentation can be compared in both directions
with a given finite free epimorphism.
Source: Stacks Project, Modules, Lemma 01BP(1), first paragraph of the proof;
kernel restriction is Modules, Section 01AF.
(blueprint: lem-weil-pbc-finite-presentation-local-comparison)

Proof: Choose a finite presentation near x from the finite-presentation data.
Each of the finitely many basis images of psi lifts locally through its generator
map, since that map is epi. Each of the finitely many presentation generators
lifts locally through psi, since psi is epi. Intersect these finitely many
neighborhoods of x and restrict the presentation to the intersection. Restriction
preserves finite free modules, epis, and kernels; transport the restriction of
psi across the canonical free-module isomorphism to obtain psi'. The chosen
lifts define alpha and beta. Both equations hold because they agree on the free
basis. Evaluation computes kernels sectionwise, so restriction supplies the
isomorphism of kernels in the statement. Empty basis sets need no shrinking;
the empty space has no points to check. -/
theorem finitePresentation_local_comparison
    (X : RingedSpace.{u}) (F : SheafOfModules.{u} (moduleRings X))
    [F.IsFinitePresentation] (r : ℕ)
    (ψ : SheafOfModules.free (R := moduleRings X) (ULift.{u} (Fin r)) ⟶ F)
    (hψ : Epi ψ) (x : X) :
    ∃ (U : Opens X), x ∈ U ∧
      ∃ (ψ' : SheafOfModules.free (R := (moduleRings X).over U)
          (ULift.{u} (Fin r)) ⟶ F.over U)
        (P : (F.over U).Presentation), P.IsFinite ∧
        ∃ (α : SheafOfModules.free (R := (moduleRings X).over U)
            (ULift.{u} (Fin r)) ⟶ SheafOfModules.free P.generators.I)
          (β : SheafOfModules.free (R := (moduleRings X).over U) P.generators.I ⟶
            SheafOfModules.free (ULift.{u} (Fin r))),
          α ≫ P.generators.π = ψ' ∧ β ≫ ψ' = P.generators.π ∧
            Nonempty ((kernel ψ).over U ≅ kernel ψ') := by
  sorry

end AlgebraicGeometry.RingedSpace
