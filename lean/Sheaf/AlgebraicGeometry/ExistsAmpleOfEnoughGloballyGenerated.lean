/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M1
-/
import Sheaf.AlgebraicGeometry.Ample
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators

/-! # Enough globally generated invertible modules give an ample module

Source: Stacks Project, Varieties, Lemma 09NC
(blueprint: lem-sc-enough-globally-generated-ample).
-/

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- A quasi-compact scheme with an affine nonvanishing neighbourhood of each point supplied
by a section of a globally generated invertible module has an ample invertible module.
Source: Stacks Project, Varieties, Lemma 09NC
(blueprint: lem-sc-enough-globally-generated-ample).

Proof: quasi-compactness gives finitely many pairs `(Lᵢ, sᵢ)` whose affine loci cover
(`def-weil-pbc-quasi-compact-scheme`). For each `Lᵢ`, choose finitely many sections whose
nonvanishing loci cover, using `lem-sc-finite-sections-cover-qc`, and add `sᵢ` as index zero.
Form the tensor product of the `Lᵢ` (`def-pur-sheaf-tensor-product`); it is invertible by
`lem-sc-tensor-globally-generated`. Tensor the chosen sections for every multi-index.
If one index is zero, the tensor section has affine nonvanishing locus by
`lem-sc-tensor-section-affine-open`. These loci cover: at any point choose nonvanishing
sections in all factors, choosing index zero in a factor whose original affine locus
contains the point. These degree-one sections witness `def-weil-pbc-ample-invertible-module`.
For the empty scheme use the structure sheaf (the empty tensor product). -/
theorem exists_isAmple_of_enough_globallyGenerated (X : Scheme.{u}) [CompactSpace X]
    (h : ∀ x : X, ∃ L : X.Modules, L.IsInvertible ∧
      Nonempty (SheafOfModules.GeneratingSections L) ∧
      ∃ s : L.val.presheaf.obj (Opposite.op ⊤), ∃ U : X.Opens,
        (U : Set X) = nonvanishingLocus L s ∧ x ∈ U ∧ IsAffineOpen U) :
    ∃ (L : X.Modules) (hL : L.IsInvertible), @IsAmple X L hL := by
  sorry

end AlgebraicGeometry.Scheme.Modules
