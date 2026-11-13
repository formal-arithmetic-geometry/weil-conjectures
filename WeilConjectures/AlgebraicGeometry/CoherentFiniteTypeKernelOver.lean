/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Coherent
import WeilConjectures.AlgebraicGeometry.CoherentIteratedSliceRelations
import WeilConjectures.AlgebraicGeometry.FiniteTypeKernelLocalGenerators

/-! # Finite type kernels into a coherent module on an open slice

Source: Stacks Project, Modules, Lemma 01BY (2), with Definition 01BV.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry.RingedSpace

/-- A map from a finite type module on an open slice to the restriction of a coherent
module has a finite type kernel (Stacks, Tags 01BY and 01BV). -/
theorem coherent_finiteType_kernel_over (X : RingedSpace.{u})
    (U : Opens X) (G : SheafOfModules.{u} (moduleRings X))
    (F : SheafOfModules.{u} ((moduleRings X).over U))
    (φ : F ⟶ G.over U) (hF : F.IsFiniteType) (hG : IsCoherent X G) :
    (kernel φ).IsFiniteType := by
  obtain ⟨q, hq⟩ := hF.exists_localGeneratorsData
  apply finiteType_kernel_local_generators X U φ q
  intro i
  have : (q.generators i).IsFiniteType := hq.isFiniteType i
  exact coherent_iterated_slice_relations X U G hG (q.X i)
    (q.generators i).I ((q.generators i).π ≫ φ.over (q.X i))

end AlgebraicGeometry.RingedSpace
