/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import WeilConjectures.AlgebraicGeometry.Modules.FaithfullyFlatDescent

/-!
# Effectivity of descent for quasi-coherent modules along finite affine flat coverings

Let `f j : W j ⟶ Spec R` be a finite family of flat morphisms from affine schemes whose images
cover `Spec R`. Every descent datum for `modulesPseudofunctor` relative to `f` whose components
are quasi-coherent comes from a quasi-coherent module on `Spec R`.
-/

@[expose] public section

universe u

open CategoryTheory Opposite TensorProduct CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat

namespace AlgebraicGeometry.Scheme.Modules

/-- **Fpqc descent for quasi-coherent modules, affine case**: a descent datum with
quasi-coherent components relative to a finite family of flat morphisms from affine schemes
covering `Spec R` is effective. -/
theorem exists_iso_toDescentData_of_finite_of_isAffine {R : CommRingCat.{u}} {J : Type u}
    [Finite J] {W : J → Scheme.{u}} [∀ j, IsAffine (W j)] (f : ∀ j, W j ⟶ Spec R)
    [∀ j, Flat (f j)] (hf : ⋃ j, Set.range (f j) = Set.univ)
    (D : modulesPseudofunctor.DescentData f)
    (hD : ∀ j, (D.obj j : (W j).Modules).IsQuasicoherent) :
    ∃ P : (Spec R).Modules, P.IsQuasicoherent ∧
      Nonempty ((modulesPseudofunctor.toDescentData f).obj P ≅ D) := by
  sorry

end AlgebraicGeometry.Scheme.Modules
