/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Braided
public import WeilConjectures.AlgebraicGeometry.FiniteTensorSignedReduction
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Shift

import WeilConjectures.AlgebraicGeometry.FiniteTensorShiftFirst
import WeilConjectures.AlgebraicGeometry.FiniteTensorShiftSecond

/-! # Finite scalar tensor reduction respects simultaneous integer shifts

Source: Stacks 07A4 and 0FNH; parent proof Step 6.
(blueprint: lem-pur-finite-tensor-shift-coherence)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open AlgebraicGeometry.Scheme
open scoped TensorProduct
attribute [local instance] _root_.DerivedCategory.braidedCategory'

namespace WeilConjectures.PurityFiniteSetting

/-- Finite scalar tensor reduction respects simultaneous integer shifts.
Source: Stacks 07A4 and 0FNH; parent proof Step 6.
(blueprint: lem-pur-finite-tensor-shift-coherence).
Proof: Resolve both inputs by flat-term K-flat complexes. Scalar extension carries
these to flat-term K-flat complexes over the quotient ring without requiring
flatness of the quotient. The scalar shift induced by the exact restriction
adjunction is the degreewise identity. The simultaneous tensor shift has the
standard Koszul sign on every homogeneous summand; scalar extension preserves
that sign, including the zero and negative integer cases. Thus the two routes
agree as cochain maps. The cochain tensor-shift descent theorem identifies
these maps with the displayed native derived comparisons, and uniqueness of
K-flat localization together with finiteTensorCore normalization gives the
claimed equality for all derived inputs. -/
theorem finiteTensorShiftCoherence (P : PurityFiniteSetting.{u}) (m : ℕ) (hm : 1 ≤ m)
    (hmn : m ≤ P.level) (T : Scheme.{u}) :
    ∀ U V (a b : ℤ), FiniteTensorShiftSquare
      (P.finiteTensorReduction m hm hmn T) (P.finiteTensorScalarShift m hm hmn T)
      (P.finiteTensorCore m hm hmn T) U V a b
      (_root_.DerivedCategory.shiftTensorShiftIso _ U V a b)
      (_root_.DerivedCategory.shiftTensorShiftIso _
        ((P.finiteTensorReduction m hm hmn T).obj U)
        ((P.finiteTensorReduction m hm hmn T).obj V) a b) := by
  intro U V a b
  let F := P.finiteTensorReduction m hm hmn T
  let δ (X Y) := ((P.finiteTensorCore m hm hmn T).μIso X Y).inv
  let := P.finiteTensorReductionCommShift m hm hmn T
  change F.map (_root_.DerivedCategory.shiftTensorShiftIso _ U V a b).hom ≫
      (F.commShiftIso (a + b)).hom.app _ ≫ (δ U V)⟦a + b⟧' =
    δ (U⟦a⟧) (V⟦b⟧) ≫
      ((F.commShiftIso a).hom.app U ⊗ₘ (F.commShiftIso b).hom.app V) ≫
      (_root_.DerivedCategory.shiftTensorShiftIso _ (F.obj U) (F.obj V) a b).hom
  have hleft := P.finiteTensorShiftFirst m hm hmn T U (V⟦b⟧) a
  have hright := P.finiteTensorShiftSecond m hm hmn T U V b
  have : NatTrans.CommShift
      ((curriedTensor _).flip.map ((F.commShiftIso b).hom.app V)) ℤ :=
    inferInstance
  have h₁ := NatTrans.shift_app_comm
    ((curriedTensor _).flip.map ((F.commShiftIso b).hom.app V)) a (F.obj U)
  have h₂ := (shiftFunctorAdd' _ b a (a + b) (add_comm b a)).inv.naturality (δ U V)
  dsimp at h₁ h₂
  simp only [_root_.DerivedCategory.shiftTensorShiftIso, Iso.trans_hom, Functor.mapIso_hom,
    Iso.app_hom, Iso.symm_hom, Category.assoc, Functor.map_comp,
    F.commShiftIso_add' (add_comm b a), Functor.CommShift.isoAdd'_hom_app,
    curriedTensor_obj_obj]
  rw [← Functor.map_comp_assoc F (((shiftFunctorAdd' _ b a (a + b) _).inv.app _)),
    Iso.inv_hom_id_app, CategoryTheory.Functor.map_id, Category.id_comp, ← h₂]
  erw [Functor.commShiftIso_hom_naturality_assoc]
  rw [← Functor.map_comp_assoc, ← Functor.map_comp_assoc, Category.assoc]
  erw [hright]
  simp only [Functor.map_comp, Category.assoc]
  erw [reassoc_of% hleft]
  erw [reassoc_of% h₁]
  simp only [MonoidalCategory.tensorHom_def, Category.assoc]
  rfl

end WeilConjectures.PurityFiniteSetting
