/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import WeilConjectures.AlgebraicGeometry.Dimension
public import WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree
import WeilConjectures.AlgebraicGeometry.DimZeroFiniteOverField
import WeilConjectures.AlgebraicGeometry.ProperBasic

/-!
# Proper zero-dimensional schemes over a field

Source: Stacks Project, Varieties, Tag 06LH (Lemma algebraic-scheme-dim-0)
(blueprint: lem-pc-dim-zero-finite-over-field)
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- A proper zero-dimensional scheme over a field is finite and affine, and has
finite-dimensional global sections.

Source: Stacks Project, Varieties, Tag 06LH (Lemma algebraic-scheme-dim-0),
algebraic case (blueprint: lem-pc-dim-zero-finite-over-field).

The proof first uses [pqf-lem-proper-basic] to obtain finite type from properness.
Then [lem-pc-algebraic-dim-zero-affine-finite] gives affineness and finiteness
from finite type and dimension at most zero. Finally,
[lem-weil-pbc-finite-over-field-affine-finite-dim] gives the finite-dimensional
global sections of a scheme finite over `Spec k`.
-/
theorem proper_dim_zero_finite_over_field {k : Type u} [Field k] {Y : Scheme.{u}}
    (f : Y ⟶ Spec (.of k)) [IsProper f] (hY : Y.dim ≤ 0) :
    IsFinite f ∧ IsAffine Y ∧
      (letI := f.ΓAlgebra; Module.Finite k Γ(Y, ⊤)) := by
  let : Y.Over (Spec (.of k)) := ⟨f⟩
  have : LocallyOfFiniteType (Y ↘ Spec (.of k)) := (proper_basic f).2.2.1
  have : QuasiCompact (Y ↘ Spec (.of k)) := (proper_basic f).2.2.2.1
  obtain ⟨hAffine, hFinite⟩ := isAffine_and_isFinite_of_dim_le_zero (k := k) Y hY
  have : IsFinite f := hFinite
  refine ⟨hFinite, hAffine, ?_⟩
  let := f.ΓAlgebra
  apply RingHom.finite_algebraMap.mp
  change (((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop).hom).Finite
  rw [CommRingCat.hom_comp, RingHom.finite_respectsIso.cancel_left_isIso]
  exact f.finite_appTop

end AlgebraicGeometry
