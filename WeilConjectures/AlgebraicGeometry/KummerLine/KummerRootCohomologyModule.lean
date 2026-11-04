/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.KummerLine.KummerLineGeometry
public import WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic

/-!
# The residue ring action on root-sheaf cohomology

The cohomology of the roots-of-unity sheaf `μₘ` is killed by `m`, hence is canonically a
module over `ZMod m`, and over its universe lift `ULift (ZMod m)`.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- Multiplication by `m` is zero on the roots-of-unity sheaf `μₘ` (étale site). -/
theorem nsmul_id_etale_rootsOfUnitySheaf (X : Scheme.{u}) (m : ℕ) :
    m • 𝟙 (X.rootsOfUnitySheaf m) = 0 := by
  change m • 𝟙 (kernel (m • 𝟙 X.gmSheaf)) = 0
  rw [← cancel_mono (kernel.ι (m • 𝟙 X.gmSheaf)), Preadditive.nsmul_comp,
    Category.id_comp, zero_comp, ← Category.comp_id (kernel.ι _),
    ← Preadditive.comp_nsmul, kernel.condition]

/-- Multiplication by `m` kills the cohomology of the roots-of-unity sheaf `μₘ`. -/
theorem nsmul_sheafH_rootsOfUnitySheaf (X : Scheme.{u}) (m q : ℕ)
    (x : Sheaf.H (X.rootsOfUnitySheaf m) q) : m • x = 0 := by
  rw [← Sheaf.H.map_id_apply x, ← Sheaf.H.map_nsmul_apply, nsmul_id_etale_rootsOfUnitySheaf]
  have h0 := Sheaf.H.map_add_apply (0 : X.rootsOfUnitySheaf m ⟶ X.rootsOfUnitySheaf m) 0 x
  rw [add_zero] at h0
  exact left_eq_add.1 h0

/-- The `ULift (ZMod m)`-module structure on the cohomology of `μₘ`. -/
noncomputable instance sheafHRootsOfUnitySheafModule (X : Scheme.{u}) (m q : ℕ) :
    Module (ULift.{u + 1} (ZMod m)) (Sheaf.H (X.rootsOfUnitySheaf m) q) :=
  letI := AddCommGroup.zmodModule (nsmul_sheafH_rootsOfUnitySheaf X m q)
  Module.compHom _ ULift.ringEquiv.toRingHom

end AlgebraicGeometry.Scheme
