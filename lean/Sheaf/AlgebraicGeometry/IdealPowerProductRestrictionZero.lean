/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group S2
-/
module

public import Sheaf.AlgebraicGeometry.IdealModuleProductStalk
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent

/-! # Restriction detects vanishing of ideal-power products

Source: Stacks Project, Cohomology of Schemes, proof of Lemma 01YD;
Schemes, Lemma 01I8; Modules, Lemma 01CD
(blueprint: lem-weil-pbc-ideal-power-product-restriction-zero).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.Modules

/-- Restricting an ideal-power product to an open gives zero exactly when the
corresponding product of the restricted ideal and module is zero.
Source: Stacks Project, Cohomology of Schemes, proof of Lemma 01YD;
Schemes, Lemma 01I8; Modules, Lemma 01CD
(blueprint: lem-weil-pbc-ideal-power-product-restriction-zero).

Proof: Restriction computes sections on image opens, with scalars transported by
the structure-ring isomorphism. Kernels are computed on sections, so restriction
preserves kernels; its restriction/direct-image adjunction preserves cokernels.
Thus it is exact and preserves images. The tensor comparison and unit comparison
carry the multiplication map to restricted multiplication: on a pure tensor a ⊗ m
both composites give a • m. Pure tensors determine maps from tensor products.
The restricted inclusion of K is the inclusion of K.comap V.ι, as follows on each
affine open of V from the section formula for a quasi-coherent ideal. Induct on n:
for n = 0 the ideal is the structure sheaf with identity inclusion; for n = 1 use
the preceding identification; for n + 2 apply the product comparison to K and its
(n + 1)-st power and compose inclusions. Apply the same comparison once more to F.
This gives an isomorphism between the two objects below, which preserves and
reflects being a zero object. The argument also covers the empty open and F = 0. -/
theorem idealPowerProduct_restrict_isZero_iff {X : Scheme.{u}}
    (K : X.IdealSheafData) (F : X.Modules) [F.IsQuasicoherent]
    (V : X.Opens) (n : ℕ) :
    IsZero ((restrictFunctor V.ι).obj
      (idealModuleProduct (idealSheafPower K.toModulesι n).2 F)) ↔
    IsZero (idealModuleProduct (idealSheafPower (K.comap V.ι).toModulesι n).2
      ((restrictFunctor V.ι).obj F)) := by sorry

end AlgebraicGeometry.Scheme.Modules
