/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.ProEtaleClopenTotalTensorKFlatDetectionData

/-! Flatness detection for finite clopen pro-etale partitions.
Source: Stacks Project, sites-modules.tex, Tag 03ER (3).
(blueprint: lem-pur-clopen-total-tensor-kflat-detection)

The proof is the componentwise exactness argument: restriction detects exactness,
restriction commutes with tensor by the local comparison, and zero insertion tests
the converse. The statement is isolated from the parent conjunction so it can be
proved independently.
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

/-- Flatness is detected componentwise by restriction along a finite disjoint
open-and-closed covering. The proof restricts exact tensor tests and uses zero
insertion for the converse. Source: Stacks Project sites-modules.tex, Tag 03ER (3).
(blueprint: lem-pur-clopen-flat-detection). -/
theorem clopen_flat_detection
    (X : Scheme.{t}) (I : Type w) [Finite I] (Y : I → Scheme.{t})
    (j : ∀ i, Y i ⟶ X) [∀ i, IsOpenImmersion (j i)] [∀ i, IsClosedImmersion (j i)]
    (hdisjoint : Pairwise (fun i k ↦ Disjoint (Set.range (j i)) (Set.range (j k))))
    (hcover : ∀ x : X, ∃ i, x ∈ Set.range (j i))
    (R : Sheaf (topology X) CommRingCat.{max u (t + 1)}) :
    ∀ F : ClopenData.clopenTensorModules.{t, u} R,
      SheafOfModules.IsFlatOnSite (J := topology X) (R := R) F ↔
        ∀ i, SheafOfModules.IsFlatOnSite (J := topology (Y i))
          (R := (ClopenData.clopenTensorRings.{t, u} (j i)).obj R)
          ((ClopenData.clopenTensorRestriction.{t, u} (j i) R).obj F) := by
  sorry

end AlgebraicGeometry.Scheme.ProEt
