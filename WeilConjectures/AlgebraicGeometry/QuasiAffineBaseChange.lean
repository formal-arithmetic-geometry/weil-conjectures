/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Mathlib.AlgebraicGeometry.QuasiAffine
public import Mathlib.AlgebraicGeometry.Pullbacks

/-!
# Base change of quasi-affine morphisms

Source: Stacks Project, Morphisms, Tag 01SO, lemma-base-change-quasi-affine
(blueprint: lem-trf-quasi-affine-base-change).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

set_option autoImplicit false

/-- Arbitrary base change preserves quasi-affineness (Stacks Project, Morphisms, Tag 01SO,
lemma-base-change-quasi-affine) (blueprint: lem-trf-quasi-affine-base-change).

Proof:
1. The inverse image of every affine open is quasi-affine, hence quasi-compact.
   The affine-open criterion for quasi-compact morphisms makes `f` quasi-compact.
2. Each such inverse image is separated, hence quasi-separated. The affine-local
   criterion `HasAffineProperty.of_iSup_eq_top` makes `f` quasi-separated.
   These are the first two observations in the proof of Tag 01SM.
3. Apply the proved source-library theorem `IsQuasiAffineHom.of_isPullback` to
   the defining pullback square. Its quasi-compactness and quasi-separatedness
   assumptions were derived in Steps 1 and 2; no extra hypothesis is imposed. -/
theorem isQuasiAffineHom_baseChange {X S S' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S)
    (hf : IsQuasiAffineHom f) :
    IsQuasiAffineHom (pullback.snd f g) := by
  let : IsQuasiAffineHom f := hf
  have : QuasiCompact f := by
    refine quasiCompact_iff_forall_isAffineOpen.mpr fun U hU ↦ ?_
    have := hU.isQuasiAffine_preimage f
    exact isCompact_iff_compactSpace.mpr
      (inferInstance : CompactSpace (f ⁻¹ᵁ U).toScheme)
  have : QuasiSeparated f := by
    refine HasAffineProperty.of_iSup_eq_top (P := @QuasiSeparated)
      (fun U : S.affineOpens ↦ U) (iSup_affineOpens_eq_top S) fun U ↦ ?_
    have := U.2.isQuasiAffine_preimage f
    exact inferInstance
  exact IsQuasiAffineHom.of_isPullback (IsPullback.of_hasPullback f g)

end AlgebraicGeometry
