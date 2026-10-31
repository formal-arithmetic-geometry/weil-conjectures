/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SmoothPurityTowerReconstructionData
public import WeilConjectures.Algebra.Homology.DerivedCategory.AdicTower

/-! Strict ell-adic models and their bounded-free cone comparison. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits Opposite SheafOfModules
namespace AlgebraicGeometry.ProEtale
attribute [-instance] spCoefficientModulesAbelian
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (T : Scheme.{u})
  (D : SpCoefficientTowersAbelian l E T)

/-- A normalized derived ell-power tower admits a strict normalized adic model.
Source: blueprint sk-lem-sp-tower.proof.md, flat-term strictification; Bhatt--Scholze,
Lemmas 3.5.4--3.5.5. (blueprint: lem-sp-tower-strict-normalized-adic-model).

Proof: resolve the zeroth finite level by a K-flat complex with flat terms. Inductively
represent each successor transition by a right fraction and resolve its source over
its own finite coefficient ring. The resulting chain maps form a strict tower after
restriction to completed coefficients. Insert zero at index zero. Multiplication by
ell^(a+b) vanishes at level a+b, and flatness over that quotient identifies the kernel
of ell^b with the image of ell^a. Normalization and the specified derived adjunction
identify the quotient maps with the original reduction maps, so these are
quasi-isomorphisms. The chosen level isomorphisms commute with successor transitions,
and retain the finite complexes and their specified derived level identifications.
No boundedness or constructibility is used. The scalar action is the canonical integer
linear action, so the scalar l is the actual coefficient ell. -/
theorem spTower_strict_normalized_adic_model
    (C : spDerivedCoefficientTowers l E T D)
    (hnorm : IsSpNormalizedTower l E T D C) :
    ∃ (U : ℕᵒᵖ ⥤ CochainComplex
          (WeilConjectures.scalarReductionSource.{u, u} l E T) ℤ)
        (hU : CochainComplex.IsNormalizedAdicTower (l : ℤ) U)
        (eU : ∀ j : ℕ, DerivedCategory.Q.obj (U.obj (op (j + 1))) ≅
          (spDerivedCompletedEvaluation l E T D j).obj C),
        (∀ j : ℕ,
          DerivedCategory.Q.map (U.map
              (homOfLE (Nat.succ_le_succ j.le_succ)).op) ≫ (eU j).hom =
            (eU (j + 1)).hom ≫ (spDerivedCompletedTransition l E T D j).app C) ∧
        ∀ j : ℕ,
          ∃ (N : CochainComplex (Scheme.proEtaleRingModules T
              (Scheme.proEtaleConstantRing T (Padic.coefficientExtensionIntegers l E ⧸
                spEllIdeal l E ^ (j + 1)))) ℤ)
            (iN : U.obj (op (j + 1)) ≅
              ((spCompletedEllRestriction l E T j).mapHomologicalComplex (.up ℤ)).obj N)
            (eN : DerivedCategory.Q.obj N ≅
              (spDerivedCoefficientEvaluation l E T D j).obj C),
            (eU j).hom = DerivedCategory.Q.map iN.hom ≫
              (spCompletedEllRestriction l E T j).mapDerivedCategoryFactors.inv.app N ≫
              (spCompletedEllRestriction l E T j).mapDerivedCategory.map eN.hom := by
  sorry

end AlgebraicGeometry.ProEtale
