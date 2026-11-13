/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Etale.Hom.EtaleHomComparisonModels
import WeilConjectures.AlgebraicGeometry.Etale.Hom.EtaleHomTransposeExactShiftData
import WeilConjectures.AlgebraicGeometry.Etale.Hom.EtaleHomTransposeExactCommShift

/-! # Exactness of the evaluation-defined étale scalar Hom comparison

Source: Stacks Project, Cohomology on Sites, Tags 08JA and 08JC.
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory
namespace AlgebraicGeometry.Etale

/-- The evaluation transpose commutes with the normalized reversed Hom shifts and
maps distinguished triangles to morphisms of distinguished triangles.
Source: Stacks 08JA and 08JC. -/
theorem etaleHomComparison_reversedExact
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (X : Scheme.{u}) (φ : A →+* B) (M : DerivedCategoryModule A X)
    (v : EtaleHomLeft X φ M ⟶ EtaleHomRight X φ M)
    (hv : IsEtaleHomTranspose X φ M v) : IsEtaleHomReversedExact X φ M v  := by
  let _ := etaleHomScalarCommShift X φ
  obtain ⟨sA, sB, chiPhi, chiPsi, hA, hB, hPhi, hPsi, hTriA, hTriB⟩ :=
    etaleHomComparison_reversedExact_shiftData X φ M
  have hComm := etaleHomComparison_reversedExact_commShift X φ M v hv sA sB
    chiPhi chiPsi hA hB hPhi hPsi
  exact ⟨sA, sB, chiPhi, chiPsi, hA, hB, hPhi, hPsi, hTriA, hTriB, hComm⟩

end AlgebraicGeometry.Etale
