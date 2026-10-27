/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A3
-/
module

public import Sheaf.CategoryTheory.LatticeKoszulTriangulatedCupComparison
public import Sheaf.CategoryTheory.LatticeDerivedInvariantsTensor
public import WeilConjectures.CategoryTheory.ModuleObjects.Monoidal

/-! # Normalized tensor maps of single-term regular complexes -/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

namespace Profinite.DiscreteLattice.OrderedKoszul

variable (R : Profinite.CondensedRing.{u}) [IsCommMonObj R.X]

local notation "S" => (fun q : ℕ ↦
  Functor.obj (HomologicalComplex.single (Modules R) (ComplexShape.up ℤ) (q : ℤ)) (𝟙_ (Modules R)))

/-- Single-term regular complexes have unsigned shift and ordered tensor identifications,
and their canonical derived tensor comparison is invertible.

Source: Stacks Tag 0FNH (ordered extraction of shifts), and step 3 and the single-term
part of step 6 of `lem-sfb-lattice-ordered-koszul-products`.
(blueprint: lem-sfb-koszul-single-tensor-normalization).

Proof: identify S_q with S_0[-q] by the identity of its unique nonzero term. For
S_p tensor S_q extract the first shift, then the second, and apply the regular
module unitor. The first comparison is unsigned; after extracting it the first
factor is in degree zero, so the second comparison has sign (-1)^(0q)=1.
Consequently the displayed component is precisely the regular unitor. Each S_p
is a shift of the tensor unit, hence K-flat: tensoring an acyclic E gives its
reindexing with differential multiplied by (-1)^p, which preserves kernels and
images. The computation of derived tensor on this K-flat complex makes the
canonical localization tensor map invertible. No division or nonzero unit is used. -/
theorem single_tensor_normalization :
    ∃ (single_shift : ∀ q : ℕ, S q ≅ (S 0)⟦(-(q : ℤ))⟧)
      (mul : ∀ p q : ℕ, S p ⊗ S q ≅ S (p + q)),
      (∀ q : ℕ,
    (single_shift q).hom.f (q : ℤ) ≫
      (CochainComplex.shiftFunctorObjXIso (S 0) (-(q : ℤ)) (q : ℤ) 0
        (by omega)).hom ≫
      (HomologicalComplex.singleObjXSelf (.up ℤ) 0 (𝟙_ (Modules R))).hom =
        (HomologicalComplex.singleObjXSelf (.up ℤ) (q : ℤ) (𝟙_ (Modules R))).hom) ∧
      (∀ p q : ℕ,
    ((HomologicalComplex.singleObjXSelf (.up ℤ) (p : ℤ) (𝟙_ (Modules R))).inv ⊗ₘ
      (HomologicalComplex.singleObjXSelf (.up ℤ) (q : ℤ) (𝟙_ (Modules R))).inv) ≫
      HomologicalComplex.ιTensorObj (S p) (S q) (p : ℤ) (q : ℤ)
        ((p + q : ℕ) : ℤ) (Nat.cast_add p q).symm ≫
      (mul p q).hom.f ((p + q : ℕ) : ℤ) ≫
      (HomologicalComplex.singleObjXSelf (.up ℤ) ((p + q : ℕ) : ℤ)
        (𝟙_ (Modules R))).hom = (λ_ (𝟙_ (Modules R))).hom) ∧
      (∀ p q : ℕ,
    IsIso (Functor.LaxMonoidal.μ DerivedCategory.Q.{u + 2} (S p) (S q))) := by sorry

end Profinite.DiscreteLattice.OrderedKoszul
