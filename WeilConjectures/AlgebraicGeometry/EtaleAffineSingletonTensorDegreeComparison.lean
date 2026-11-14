/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleAffineSingletonTensorDegreeHomNormalization
import WeilConjectures.AlgebraicGeometry.EtaleAffineSingletonTensorDegreeHom
import WeilConjectures.AlgebraicGeometry.EtaleAffineSingletonTensorDegreeInverse

/-! # Degreewise affine singleton tensor comparison

## References

* Stacks Project, Tag 03P2
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct

namespace AlgebraicGeometry.Scheme

noncomputable section

/-- Affine pullback sections give canonical degree isomorphisms, with their pure-tensor
normalization, without asserting compatibility between different degrees.
(Stacks, Tags 03P2, 01I9 and 01IA) -/
/- Fixed-degree affine tensor-section calculation. The geometric proof identifies the
degree-n affine fibre product with the indexed tensor power, applies the affine pullback
sections formula, and checks the displayed normalization on pure tensors; tensor
generators then extend it to all sections. -/
theorem exists_singletonTensorDegreeComparison_degree
    (X : Scheme.{u}) (F : X.Modules) [F.IsQuasicoherent]
    (U W : X.Etale) (g : W ⟶ U) (hU : IsAffine U.left) (hW : IsAffine W.left)
    (n : ℕ) :
    ∃ e : (singletonTensorAmitsur X F U W g).X n ≅
      (singletonTensorCech X F U W g).X n,
      IsSingletonTensorDegreeComparison X F U W g n e := by
  obtain ⟨f, hf⟩ :=
    exists_singletonTensorDegreeComparison_hom X F U W g hU hW n
  obtain ⟨inv, hfi, hif⟩ :=
    exists_singletonTensorDegreeComparison_inverse X F U W g hU hW n f hf
  let e : (singletonTensorAmitsur X F U W g).X n ≅
      (singletonTensorCech X F U W g).X n :=
    { hom := f
      inv := inv
      hom_inv_id := hfi
      inv_hom_id := hif }
  exact ⟨e, hf⟩

/-- Affine pullback sections give canonical degree isomorphisms between the Amitsur and
tensor-section Čech complexes, with their pure-tensor normalization in every degree. -/
theorem exists_singletonTensorDegreeComparison
    (X : Scheme.{u}) (F : X.Modules) [F.IsQuasicoherent]
    (U W : X.Etale) (g : W ⟶ U) (hU : IsAffine U.left) (hW : IsAffine W.left) :
    ∃ e : ∀ n : ℕ, (singletonTensorAmitsur X F U W g).X n ≅
      (singletonTensorCech X F U W g).X n,
      ∀ n, IsSingletonTensorDegreeComparison X F U W g n (e n) := by
  choose e he using fun n ↦
    exists_singletonTensorDegreeComparison_degree X F U W g hU hW n
  exact ⟨e, he⟩

end
end AlgebraicGeometry.Scheme
