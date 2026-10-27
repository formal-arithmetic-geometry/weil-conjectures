/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.ProEtaleClopenTotalTensorKFlatDetectionData

/-! K-flatness detection for finite clopen pro-etale partitions.
Source: Stacks Project, sites-cohomology.tex, Tags 06YN and 0FPQ.
(blueprint: lem-pur-clopen-total-tensor-kflat-detection)

The proof tests K-flatness against arbitrary unbounded acyclic complexes, using
componentwise acyclicity and zero insertion. It is isolated from the parent
conjunction so it can be proved independently.
-/

@[expose] public noncomputable section
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
universe t u w
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open WeilConjectures
namespace AlgebraicGeometry.Scheme.ProEt

/-- K-flatness is detected componentwise by restriction along a finite disjoint
open-and-closed covering. The proof uses the total tensor comparison and zero
insertion for arbitrary unbounded acyclic complexes. Source: Stacks Project sites-cohomology.tex,
Tag 06YN.
(blueprint: lem-pur-clopen-kflat-detection). -/
theorem clopen_kflat_detection
    (X : Scheme.{t}) (I : Type w) [Finite I] (Y : I → Scheme.{t})
    (j : ∀ i, Y i ⟶ X) [∀ i, IsOpenImmersion (j i)] [∀ i, IsClosedImmersion (j i)]
    (hdisjoint : Pairwise (fun i k ↦ Disjoint (Set.range (j i)) (Set.range (j k))))
    (hcover : ∀ x : X, ∃ i, x ∈ Set.range (j i))
    (R : Sheaf (topology X) CommRingCat.{max u (t + 1)}) :
    ∀ P : CochainComplex (ClopenData.clopenTensorModules.{t, u} R) ℤ,
      CochainComplex.IsKFlatIndependentCoefficients (J := topology X) (R := R) P ↔
        ∀ i, CochainComplex.IsKFlatIndependentCoefficients (J := topology (Y i))
          (R := (ClopenData.clopenTensorRings.{t, u} (j i)).obj R)
          ((ClopenData.clopenTensorComplexRestriction.{t, u} (j i) R).obj P) := by
  sorry

end AlgebraicGeometry.Scheme.ProEt
