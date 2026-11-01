/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.Normalized.NormalizedCoefficientFamilies
public import WeilConjectures.AlgebraicGeometry.Pbc.PbcPullbackCoherentFamily
public import WeilConjectures.AlgebraicGeometry.Pbc.PbcQbarCompletedPullback
import WeilConjectures.AlgebraicGeometry.Rational.RationalScalarCompletionUnitSquare
import WeilConjectures.AlgebraicGeometry.Pbc.PbcUniformCompleteTriangulated

/-! # Strict completed-pullback coefficient family argument

Source: current blueprint, coefficient coherence.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits
private theorem transportUnit
    {C : Type*} [Category C] {A B D E F : C}
    (a : A ≅ B) (b : D ≅ E) (c : D ≅ F)
    (u : A ⟶ D) (v : B ⟶ E) (w : A ⟶ F)
    (h : u ≫ b.hom = a.hom ≫ v) (h' : u ≫ c.hom = w) :
    v ≫ b.inv ≫ c.hom = a.inv ≫ w := by
  apply (cancel_epi a.hom).1
  simp only [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
  rw [← h]
  simpa only [Category.assoc, Iso.hom_inv_id_assoc] using h'

namespace AlgebraicGeometry.Scheme

end AlgebraicGeometry.Scheme
