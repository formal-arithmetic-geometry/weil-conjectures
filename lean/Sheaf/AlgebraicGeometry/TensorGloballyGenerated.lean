/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H1
-/
module

public import Sheaf.AlgebraicGeometry.PositiveTensorFamily
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
import WeilConjectures.AlgebraicGeometry.Modules.ProjectionFormula
import Sheaf.AlgebraicGeometry.FiniteGlobalGeneratingFamily
import Sheaf.AlgebraicGeometry.FiniteTensorGeneratingSections

/-!
# Tensor products of globally generated invertible modules

Source: Stacks Project, Varieties, Tag 09NC, proof; Modules, Tag 01AO
(blueprint: lem-sc-tensor-globally-generated).
-/

@[expose] public section

universe v

open CategoryTheory MonoidalCategory

namespace AlgebraicGeometry.Scheme.Modules

/-- On a quasi-compact scheme the positive tensor product of globally generated invertible
modules is invertible and globally generated. Every choice of finite generating families
of the factors generates the tensor product by its pure tensor sections.
Source: Stacks, Tag 09NC, proof, and Tag 01AO (blueprint: lem-sc-tensor-globally-generated).

Proof: first use induction on the number of factors, with the first factor as base case
and `lem-weil-pbc-invertible-pullback-tensor` (1) in the induction step, to obtain
invertibility of the left-associated tensor product (`def-pur-sheaf-tensor-product`).
Next choose finite global generating families: on an invertible stalk a generating
family contains a section that generates that rank-one stalk; the corresponding
nonvanishing opens cover X, and quasi-compactness gives a finite subcover for each factor.
For any such finite families, `lem-sc-tensor-generating-sections` shows that the pure
tensors generate the tensor product: tensor-product stalks are tensor products of the
stalks, where multilinear expansion in the factor generators proves generation.
The resulting epimorphism from the free sheaf proves global generation in the sense of
`def-weil-pbc-generating-sections`. For one factor all assertions reduce to the input.
-/
theorem isInvertible_and_globallyGenerated_positiveTensorFamily
    (X : Scheme.{v}) [CompactSpace X] (n : ℕ) (L : Fin (n + 1) → X.Modules)
    (hL : ∀ i, (L i).IsInvertible)
    (hG : ∀ i, Nonempty (SheafOfModules.GeneratingSections (L i))) :
    (positiveTensorFamily n L).IsInvertible ∧
      Nonempty (SheafOfModules.GeneratingSections (positiveTensorFamily n L)) ∧
      (∃ σ : (i : Fin (n + 1)) → SheafOfModules.GeneratingSections (L i),
        ∀ i, (σ i).IsFiniteType) ∧
      (∀ σ : (i : Fin (n + 1)) → SheafOfModules.GeneratingSections (L i),
        (∀ i, (σ i).IsFiniteType) →
        Epi ((positiveTensorFamily n L).freeHomEquiv.symm
          (fun j : (i : Fin (n + 1)) → (σ i).I ↦
            positiveTensorFamilySection n L (fun i ↦ (σ i).s (j i))))) := by
  classical
  have hInv : ∀ (k : ℕ) (F : Fin (k + 1) → X.Modules),
      (∀ i, (F i).IsInvertible) → (positiveTensorFamily k F).IsInvertible := by
    intro k
    induction k with
    | zero => intro F hF; exact hF 0
    | succ k ih =>
      intro F hF
      let := ih (fun i ↦ F i.castSucc) (fun i ↦ hF i.castSucc)
      let := hF (Fin.last (k + 1))
      exact IsInvertible.tensorObj _ _
  obtain ⟨σ, hσ⟩ : ∃ σ : (i : Fin (n + 1)) →
      SheafOfModules.GeneratingSections (L i), ∀ i, (σ i).IsFiniteType := by
    choose σ hσ using fun i ↦ finite_global_generating_family X (L i) (hL i) (hG i)
    exact ⟨σ, hσ⟩
  have hEpi := finite_tensor_generating_sections n L
  have hp := hEpi σ hσ
  exact ⟨hInv n L hL,
    ⟨{ I := (i : Fin (n + 1)) → (σ i).I
       s := fun j ↦ positiveTensorFamilySection n L (fun i ↦ (σ i).s (j i))
       epi := hp }⟩, ⟨σ, hσ⟩, hEpi⟩

end AlgebraicGeometry.Scheme.Modules
