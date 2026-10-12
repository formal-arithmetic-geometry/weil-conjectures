/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P2
-/
module

public import Sheaf.AlgebraicGeometry.IdealModuleProductStalk
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
public import Mathlib.RingTheory.Ideal.Operations
import Sheaf.AlgebraicGeometry.Modules.IdealTimesQuasiCoherentAffineSections
import Sheaf.AlgebraicGeometry.Modules.QuasiCoherentCokernelImage
import Sheaf.AlgebraicGeometry.QuasiCoherentTensorProductAffineSections

/-! # Detecting vanishing of an ideal-power product on an affine cover

Source: Stacks Project, Cohomology of Schemes, proof of Lemma 01Y9, and
Schemes, Lemma 01I8 (blueprint: lem-weil-pbc-ideal-power-product-zero-affine-cover).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- An ideal-power product of a quasi-coherent module vanishes if and only if the
corresponding powers of ideals of affine sections annihilate the section modules
on an affine open cover. Neither finiteness nor Noetherianity is needed here.

Source: Stacks Project, Cohomology of Schemes, proof of Lemma 01Y9; Schemes,
Lemma 01I8 (blueprint: lem-weil-pbc-ideal-power-product-zero-affine-cover).

Proof: On each affine open identify the ideal and module with the tilde sheaves
of their sections by the tilde/global-sections adjunction. The tensor comparison
and preservation of images identify the product with the tilde of I^t M; induction
on t identifies the power with I^t. For t = 0 the power inclusion is the identity
of the structure sheaf, and multiplication is the left unitor, so the product is M.
The submodule I^t M is zero exactly when every element of I^t annihilates every
section, equivalently I^t is contained in Ann(M). A quasi-coherent sheaf on an
affine is zero exactly when its section module is zero, by the counit isomorphism
and preservation of zero by tilde. Finally a sheaf zero on an open cover is zero:
restrict any section to its intersections with the covering opens and use the
uniqueness clause of the sheaf axiom. The reverse implication follows by restricting
a zero sheaf. This also covers an empty cover of the empty scheme. -/
theorem idealPowerProduct_isZero_iff_affine_cover (X : Scheme.{u})
    (F : X.Modules) [F.IsQuasicoherent] (K : X.IdealSheafData)
    (S : Set X.affineOpens) (hS : ∀ x : X, ∃ U ∈ S, x ∈ U.1) (t : ℕ) :
    IsZero (idealModuleProduct (idealSheafPower K.toModulesι t).2 F) ↔
      ∀ U ∈ S, K.ideal U ^ t ≤ Module.annihilator Γ(X, U.1) Γ(F, U.1) := by sorry

end AlgebraicGeometry.Scheme
