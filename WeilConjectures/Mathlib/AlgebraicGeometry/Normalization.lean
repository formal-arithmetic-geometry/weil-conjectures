/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Normalization
public import WeilConjectures.Mathlib.AlgebraicGeometry.FunctionField

/-!
# Complements on the relative normalization

For a quasi-compact open immersion `f : X ⟶ Y`, the relative normalization `f.normalization`
of `Y` in `X` contains `X` as an open subscheme: the morphism `f.toNormalization` is an open
immersion. If `X` is integral with integrally closed local rings, then so is `f.normalization`,
and if `Y` is locally of finite type over a field then `f.fromNormalization` is finite.

## Main statements

- `AlgebraicGeometry.Scheme.Hom.isOpenImmersion_toNormalization`: for a quasi-compact open
  immersion `f`, the morphism `f.toNormalization` is an open immersion.
- `AlgebraicGeometry.Scheme.Hom.isIntegrallyClosed_stalk_normalization`: the normalization of
  `Y` in an integral scheme with integrally closed local rings has integrally closed local
  rings.
- `AlgebraicGeometry.Scheme.Hom.isFinite_fromNormalization`: the normalization of a scheme
  locally of finite type over a field in a quasi-compact integral open subscheme is finite.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.Hom

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

section OpenImmersion

variable [IsOpenImmersion f] [QuasiCompact f]

/-- For a quasi-compact open immersion `f : X ⟶ Y`, the morphism `X ⟶ f.normalization` is an
open immersion: normalization commutes with the smooth base change `f` itself, and the
normalization of the isomorphism `X ×_Y X ⟶ X` is trivial. -/
instance isOpenImmersion_toNormalization : IsOpenImmersion f.toNormalization := by
  have h := f.toNormalization_normalizationPullback_fst f
  have : f.toNormalization = inv (pullback.fst f f) ≫ (pullback.snd f f).toNormalization ≫
      f.normalizationPullback f ≫ pullback.fst _ _ := by
    rw [h, IsIso.inv_hom_id_assoc]
  rw [this]
  infer_instance

end OpenImmersion

/-- The relative normalization of `Y` in an integral scheme `X` with integrally closed local
rings has integrally closed local rings. Over an affine open `V` of `Y` it is the spectrum of
the integral closure of `Γ(Y, V)` in the integrally closed domain `Γ(X, f⁻¹ V)`, which is
again an integrally closed domain. -/
theorem isIntegrallyClosed_stalk_normalization [QuasiCompact f] [QuasiSeparated f]
    [IsIntegral X] (hX : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (y : f.normalization) : IsIntegrallyClosed (f.normalization.presheaf.stalk y) := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hyU, -⟩ := Y.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ (f.fromNormalization y)) isOpen_univ
  let := (f.app U).hom.toAlgebra
  have hV : IsAffineOpen (f.fromNormalization ⁻¹ᵁ U) := hU.preimage f.fromNormalization
  have : Nonempty (f.fromNormalization ⁻¹ᵁ U) := ⟨⟨y, hyU⟩⟩
  have : Nonempty (f ⁻¹ᵁ U) := by
    by_contra h
    have : Subsingleton Γ(X, f ⁻¹ᵁ U) := CommRingCat.subsingleton_of_isTerminal
      (X.sheaf.isTerminalOfEqEmpty ((TopologicalSpace.Opens.not_nonempty_iff_eq_bot _).mp
        fun ⟨x, hx⟩ ↦ h ⟨⟨x, hx⟩⟩))
    exact not_subsingleton Γ(f.normalization, f.fromNormalization ⁻¹ᵁ U)
      (f.normalizationObjIso hU).commRingCatIsoToRingEquiv.subsingleton
  have := isIntegrallyClosed_of_isIntegrallyClosed_stalk hX (f ⁻¹ᵁ U)
  have : IsIntegrallyClosed (integralClosure Γ(Y, U) Γ(X, f ⁻¹ᵁ U)) :=
    .of_isIntegrallyClosed_of_isIntegrallyClosedIn _ Γ(X, f ⁻¹ᵁ U)
  have : IsIntegrallyClosed Γ(f.normalization, f.fromNormalization ⁻¹ᵁ U) :=
    .of_equiv (f.normalizationObjIso hU).commRingCatIsoToRingEquiv.symm
  let := TopCat.Presheaf.algebra_section_stalk f.normalization.presheaf
    (⟨y, hyU⟩ : f.fromNormalization ⁻¹ᵁ U)
  have := hV.isLocalization_stalk ⟨y, hyU⟩
  exact isIntegrallyClosed_of_isLocalization _ _
    (hV.primeIdealOf ⟨y, hyU⟩).asIdeal.primeCompl_le_nonZeroDivisors

/-- The normalization of a scheme `Y` locally of finite type over a field `K` in a
quasi-compact integral open subscheme `X` is finite over `Y`.

Over an affine open `Spec A` of `Y` meeting `X`, the ring of the normalization is the integral
closure of `A` in `Γ(X ∩ Spec A)`, which lies in the integral closure of the finitely generated
`K`-domain `A ⧸ 𝔭` in its fraction field, `𝔭` the generic point of the closure of `X`; the
latter is a finite `A`-module by E. Noether's finiteness theorem. -/
theorem isFinite_fromNormalization {K : Type u} [Field K] [IsOpenImmersion f] [QuasiCompact f]
    [IsIntegral X] (q : Y ⟶ Spec (.of K)) [LocallyOfFiniteType q] :
    IsFinite f.fromNormalization := by
  sorry

end AlgebraicGeometry.Scheme.Hom
