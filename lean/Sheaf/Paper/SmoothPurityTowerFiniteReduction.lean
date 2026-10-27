/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P9
-/
module

public import Sheaf.Paper.SmoothPurityTowerReconstructionData

/-! # Finite reduction of the projection from a normalized tower limit

Source: current blueprint, sec-smooth-purity/sk-lem-sp-tower, finite-reduction paragraph.
(blueprint: lem-sp-tower-projection-finite-reduction)
-/

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

/-- The finite reduction calculation for one specified projection. No boundedness or
constructibility assumption is used.
Source: current blueprint, sk-lem-sp-tower.proof.md, first paragraph, through
"the reduction formula follows"; Stacks 0940 and 099P
(blueprint: lem-sp-tower-projection-finite-reduction).

Proof: choose the simultaneous flat-term K-flat model of
lem-sp-semilinear-kflat-tower-model, retaining the original reductions and projections.
The model's counit equation and normalization make its ordinary reduction maps
quasi-isomorphisms. Fix exponent m+1 and delete the first m terms of the tower.
The coefficient-fiber lemma identifies the fiber of the augmented Koszul complex
with the smaller coefficient ring in degree -1; its transitions are multiplication
by the corresponding powers of ell. Tensor with the K-flat level complexes.
The normalized-error-tower lemma makes the left error tower pro-zero: every m+1
successive transitions vanish. Its derived limit is zero, while the right constant
tower has the given level as limit. Thus the middle Koszul tower has that same limit.
The Koszul--Roos projection comparison identifies it with reduction of M, retaining
the m-th projection. Its adjunction normalization identifies the resulting arrow with
the displayed spTowerReconstructionMap. Exact scalar restriction detects isomorphisms,
so the map is invertible in the finite-coefficient category itself. -/
theorem spTower_projection_finite_reduction
    (C : spDerivedCoefficientTowers l E T D)
    (hnorm : IsSpNormalizedTower l E T D C)
    (M : DerivedCategory (WeilConjectures.scalarReductionSource.{u, u} l E T))
    [HasProduct (fun n : ℕ ↦ (spDerivedCompletedEvaluation l E T D n).obj C)]
    (p : M ⟶ ∏ᶜ fun n : ℕ ↦ (spDerivedCompletedEvaluation l E T D n).obj C)
    (δ : (∏ᶜ fun n : ℕ ↦ (spDerivedCompletedEvaluation l E T D n).obj C) ⟶ M⟦(1 : ℤ)⟧)
    (hlim : IsDerivedLimitTriangle
      (fun n : ℕ ↦ (spDerivedCompletedTransition l E T D n).app C) M p δ) (m : ℕ) :
    IsIso (spTowerReconstructionMap l E T D C M p m) := by sorry

end AlgebraicGeometry.ProEtale
