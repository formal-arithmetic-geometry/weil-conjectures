/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Curve.Assertions
import WeilConjectures.AlgebraicGeometry.Curve.UniversalHomeomorphismAssertions
import WeilConjectures.AlgebraicGeometry.ReductionUniversalHomeomorphism

/-! # The eight assertions descend from the reduction

Source: Stacks Project, Theorem 59.83.10 (03SC), first proof sentence,
and Proposition 59.45.4 (03SI).
-/

@[expose] public section

universe u
open CategoryTheory
namespace AlgebraicGeometry
open Etale

/-- For a fixed sheaf, all eight assertions descend from the nilradical reduction.
Source: Stacks Project, Theorem 59.83.10 (03SC), first proof sentence. -/
theorem IsCurve.assertions_of_reduction
    (Λ : Type (u + 1)) [CommRing Λ] {k : Type u} [Field k] [IsAlgClosed k]
    {C : Scheme.{u}} (f : C ⟶ Spec (.of k)) [IsCurve f]
    (F : Sheaf C.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (H : IsCurve.Assertions Λ (C.nilradical.subschemeι ≫ f)
      ((C.nilradical.subschemeι)^*[ModuleCat.{u + 1} Λ].obj F)) :
    IsCurve.Assertions Λ f F := by
  obtain ⟨hred, hclosed, hsurj, huniv⟩ :=
    reduction_isReduced_isClosedImmersion_isSurjective_isUniversalHomeomorphism C
  let D := C.nilradical.subscheme
  let i : D ⟶ C := C.nilradical.subschemeι
  have : IsClosedImmersion i := hclosed
  have : Surjective i := hsurj
  have : IsUniversalHomeomorphism i := inferInstance
  have : IsReduced D := hred
  let : IsCurve (i ≫ f) :=
    { toIsSeparated := inferInstance
      toLocallyOfFiniteType := inferInstance
      toQuasiCompact := inferInstance
      krullDim_le_one := by
        rw [IsHomeomorph.topologicalKrullDim_eq i i.isHomeomorph]
        exact IsCurve.krullDim_le_one (f := f) }
  exact IsCurve.assertions_of_universalHomeomorphism Λ f i F H

end AlgebraicGeometry
