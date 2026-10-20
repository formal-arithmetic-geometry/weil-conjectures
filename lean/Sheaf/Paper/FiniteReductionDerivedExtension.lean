/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group R1
-/
module

public import Sheaf.Paper.FiniteReductionSystem
import Sheaf.Paper.FiniteReductionRestrictTensor

/-! Universal fixed-scalar derived extension, computed on K-flat complexes. -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped TensorProduct

namespace AlgebraicGeometry.FiniteReduction

section Site
variable {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
    (J : GrothendieckTopology C)
    {A B : Type (u + 1)} [CommRing A] [CommRing B]

/-- Sheafified extension of constant scalars has its universal total left derived pair,
computed on all K-flat complexes. Source: Stacks Tags 06YT and 06YY.
(blueprint: lem-pur-finite-reduction-derived-extension).

Proof: after exact conservative restriction of scalars, ordinary extension is tensor
with the constant target coefficient ring. This preserves quasi-isomorphisms between
K-flat complexes. The K-flat derivability structure therefore gives a total left
derived functor with the universal counit, invertible on every K-flat complex. -/
theorem nonempty_derivedExtension (f : A →+* B) :
    Nonempty (DerivedExtension J f) := by
  let W := HomologicalComplex.quasiIso (Sheaf J (ModuleCat.{u + 1} A)) (.up ℤ)
  let F := (extend J f).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q
  have hderive : W.localizerMorphismKFlat.Derives F := by
    intro P Q g hg
    have : QuasiIso g.hom := (HomologicalComplex.mem_quasiIso_iff _).mp hg
    have h := CochainComplex.quasiIso_map_of_iso_tensorRight
      (extend J f) (Sheaf.restrictScalars J f) (extend_restrict_tensor J f)
      g.hom P.property Q.property
    exact Localization.inverts DerivedCategory.Q
      (HomologicalComplex.quasiIso (Sheaf J (ModuleCat.{u + 1} B)) (.up ℤ)) _
      ((HomologicalComplex.mem_quasiIso_iff _).mpr h)
  let : F.HasLeftDerivedFunctor W := hderive.hasLeftDerivedFunctor
  let L := F.totalLeftDerived DerivedCategory.Q W
  let ε := F.totalLeftDerivedCounit DerivedCategory.Q W
  refine ⟨{ functor := L
            counit := ε
            universal := inferInstance
            computation := fun P hP ↦ ?_ }⟩
  exact hderive.isIso_of_isLeftDerivedFunctor ε ⟨P, hP⟩

end Site
end AlgebraicGeometry.FiniteReduction
