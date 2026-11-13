/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.KummerLine.KummerLineGeometry

/-!
# The punctured-line inclusion is over the base field
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.Etale

/-- The polynomial-to-Laurent inclusion commutes with the structure maps to `Spec k`. -/
theorem normalizedKummerInclusion_over (k : Type u) [Field k] :
    KummerLine.inclusion k ≫ KummerLine.structureMap k false =
      KummerLine.structureMap k true := by
  have h : (Polynomial.toLaurent (R := k)).comp Polynomial.C = LaurentPolynomial.C := by
    apply RingHom.ext
    intro a
    exact Polynomial.toLaurent_C a
  simp only [KummerLine.inclusion, KummerLine.structureMap, ← Spec.map_comp,
    ← CommRingCat.ofHom_comp, h]

end AlgebraicGeometry.Etale
