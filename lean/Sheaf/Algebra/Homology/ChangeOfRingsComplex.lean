/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NK
-/
module

public import Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.Algebra.Homology.HomologicalComplex

/-!
# Termwise change of rings of a cochain complex

Source: Stacks Project, Cohomology on Sites, Tag 0G7E, coefficient-change specialization
(blueprint: def-pur-change-of-rings-complex).
-/

@[expose] public section

universe u v

open CategoryTheory

namespace SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{max u v} RingCat.{max u v})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
  [HasWeakSheafify J AddCommGrpCat.{max u v}]
  {R S : Sheaf J CommRingCat.{max u v}} (φ : R ⟶ S)
  (K : CochainComplex (SheafOfModules.{max u v}
    ((sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj R)) ℤ)

/-- The changed differentials have cochain shape. Source: Stacks, Tag 0G7E
(blueprint: def-pur-change-of-rings-complex).
Proof: outside the shape, K's differential is zero. Sectionwise extension of scalars
preserves zero, and so does the additive module sheafification functor. -/
theorem changeOfRingsComplex_shape (i j : ℤ) (h : ¬ (ComplexShape.up ℤ).Rel i j) :
    changeOfRingsHom φ (K.X i) (K.d i j) = 0 := by
  sorry

/-- The changed differentials square to zero. Source: Stacks, Tag 0G7E
(blueprint: def-pur-change-of-rings-complex).
Proof: sectionwise extension of scalars and module sheafification preserve composition
and zero. Apply these identities to K.d_comp_d i j k. -/
theorem changeOfRingsComplex_comp (i j k : ℤ) :
    changeOfRingsHom φ (K.X i) (K.d i j) ≫
      changeOfRingsHom φ (K.X j) (K.d j k) = 0 := by
  sorry

/-- Apply the existing change of rings to every term and differential.
Source: Stacks, Tag 0G7E (blueprint: def-pur-change-of-rings-complex). -/
noncomputable def changeOfRingsComplex : CochainComplex (SheafOfModules.{max u v}
    ((sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj S)) ℤ where
  X i := changeOfRings φ (K.X i)
  d i j := changeOfRingsHom φ (K.X i) (K.d i j)
  shape := changeOfRingsComplex_shape φ K
  d_comp_d' i j k _ _ := changeOfRingsComplex_comp φ K i j k

end SheafOfModules
