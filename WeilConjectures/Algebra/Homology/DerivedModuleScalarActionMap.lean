/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.Algebra.Homology.OrdinaryModuleDerivedInternalHom
public import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel

/-! # The scalar-action map of an ordinary derived module

Source: Stacks Project, dualizing.tex, Tag 0BZW(1)(c), the scalar-action morphism
(blueprint: def-sfb-derived-module-scalar-action-map).

This construction names the transpose of the unit action, using the existing
closed derived tensor structure and its canonical identification of A[0] with
the tensor unit. It requires no finiteness or Noetherian hypotheses.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.MonoidalCategory

namespace ModuleCat

/-- The canonical scalar-action morphism A[0] → RHom_A(K,K) is the transpose of
K ⊗ A[0] → K. Transport A[0] to the tensor unit and curry the identity of K,
so the map is fixed by the unit action, rather than chosen from an existence claim.
Source: Stacks Project, dualizing.tex, Tag 0BZW(1)(c)
(blueprint: def-sfb-derived-module-scalar-action-map). -/
def derivedModuleScalarActionMap {A : Type u} [CommRing A]
    [HasDerivedCategory.{u} (ModuleCat.{u} A)]
    (K : DerivedCategory (ModuleCat.{u} A)) :
    (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A A) ⟶
      (ihom K).obj K :=
  (DerivedCategory.singleFunctorObjUnitIso (ModuleCat.{u} A)).hom ≫
    MonoidalClosed.curry' (𝟙 K)

end ModuleCat
