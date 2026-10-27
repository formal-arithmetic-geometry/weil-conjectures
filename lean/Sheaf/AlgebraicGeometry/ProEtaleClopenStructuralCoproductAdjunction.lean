/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.ProEtaleClopenTotalTensorKFlatDetectionData

/-! Split coproduct and adjunction data for finite clopen restriction.
Source: Stacks Project, sites-modules.tex, Tag 0GMW; sites-cohomology.tex, Tag 0FPQ.
(blueprint: lem-pur-clopen-structural-coproduct-adjunction). -/

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

/-- The restriction preserves all displayed coproducts and admits the stated zero-insertion
adjunction. This is the lower structural clause used by the parent tensor theorem. -/
theorem clopen_structural_coproduct_adjunction
    (X : Scheme.{t}) (I : Type w) [Finite I] (Y : I → Scheme.{t})
    (j : ∀ i, Y i ⟶ X) [∀ i, IsOpenImmersion (j i)] [∀ i, IsClosedImmersion (j i)]
    (hdisjoint : Pairwise (fun i k ↦ Disjoint (Set.range (j i)) (Set.range (j k))))
    (hcover : ∀ x : X, ∃ i, x ∈ Set.range (j i))
    (R : Sheaf (topology X) CommRingCat.{max u (t + 1)}) :
    (∀ i (K : Type (max u (t + 1))),
      PreservesColimitsOfShape (Discrete K) (ClopenData.clopenTensorRestriction.{t, u} (j i) R)) ∧
    (∀ i
      (e : ClopenData.clopenTensorModules.{t, u}
        ((ClopenData.clopenTensorRings.{t, u} (j i)).obj R) ⥤
        ClopenData.clopenTensorModules.{t, u} R),
      Nonempty (e ⋙ ClopenData.clopenTensorRestriction.{t, u} (j i) R ≅ 𝟭 _) →
      (∀ k, k ≠ i → ∀ N, IsZero ((e ⋙ ClopenData.clopenTensorRestriction.{t, u} (j k) R).obj N)) →
      Nonempty (ClopenData.clopenTensorRestriction.{t, u} (j i) R ⊣ e)) := by
  sorry

end AlgebraicGeometry.Scheme.ProEt
