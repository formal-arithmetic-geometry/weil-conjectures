/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Normalization
public import WeilConjectures.Mathlib.AlgebraicGeometry.FunctionField
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import WeilConjectures.Mathlib.Topology.KrullDimension

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

namespace AlgebraicGeometry.Scheme

variable (X : Scheme.{u}) [IsIntegral X]

/-- The *normalization* `X^ν` of an integral scheme `X` in its function field `K = k(X)`: the
relative normalization `Spec_X(𝒪̃_X)` of `X` in the generic point `Spec K ⟶ X`, where `𝒪̃_X` is
the integral closure of `𝒪_X` in the constant sheaf `K`. Finiteness of `X^ν ⟶ X` is a separate
property, `AlgebraicGeometry.Scheme.isFinite_fromNormalization_of_locallyOfFiniteType`.
(blueprint: `def-sc-normalization`) -/
noncomputable abbrev normalization : Scheme.{u} :=
  X.fromSpecFunctionField.normalization

/-- The canonical morphism `ν : X^ν ⟶ X` from the normalization of an integral scheme `X` in its
function field. (blueprint: `def-sc-normalization`) -/
noncomputable abbrev fromNormalization : X.normalization ⟶ X :=
  X.fromSpecFunctionField.fromNormalization

instance isDominant_fromNormalization : IsDominant X.fromNormalization :=
  have : IsDominant (X.fromSpecFunctionField.toNormalization ≫ X.fromNormalization) := by
    rw [Hom.toNormalization_fromNormalization]; infer_instance
  .of_comp X.fromSpecFunctionField.toNormalization _

/-- The normalization `ν : X^ν ⟶ X` of an integral scheme in its function field is surjective:
it is integral, hence closed, and dominant. (blueprint: `lem-sc-normalization-exists`) -/
instance surjective_fromNormalization : Surjective X.fromNormalization :=
  have : UniversallyClosed X.fromNormalization :=
    (IsIntegralHom.iff_universallyClosed_and_isAffineHom.mp inferInstance).1
  inferInstance

/-- **Finiteness of the normalization.** For an integral scheme `X` locally of finite type over a
field `k`, the normalization `ν : X^ν ⟶ X` in the function field is finite: over an affine open
`Spec A`, the integral closure of the finitely generated `k`-domain `A` in its fraction field is a
finite `A`-module by E. Noether's finiteness theorem. In particular `X^ν` is proper over `k` if
`X` is. (blueprint: `lem-sc-normalization-exists`) -/
theorem isFinite_fromNormalization_of_locallyOfFiniteType {k : Type u} [Field k]
    (q : X ⟶ Spec (.of k)) [LocallyOfFiniteType q] : IsFinite X.fromNormalization :=
  sorry

/-- **The normalization is birational.** For an integral scheme `X` locally of finite type over
a field `k`, the normalization `ν : X^ν ⟶ X` is an isomorphism over a nonempty, hence dense,
open subscheme of `X`. (blueprint: `lem-sc-normalization-exists`) -/
theorem exists_isIso_fromNormalization_restrict {k : Type u} [Field k] (q : X ⟶ Spec (.of k))
    [LocallyOfFiniteType q] :
    ∃ U : X.Opens, (U : Set X).Nonempty ∧ IsIso (X.fromNormalization ∣_ U) :=
  sorry

/-- **The normalization preserves dimension.** For an integral scheme `X` locally of finite type
over a field `k`, `dim X^ν = dim X`: the finite surjective morphism `ν` lifts chains of
specializations, and identifies no two distinct points one of which specializes to the other.
(blueprint: `lem-sc-normalization-exists`) -/
theorem topologicalKrullDim_normalization {k : Type u} [Field k] (q : X ⟶ Spec (.of k))
    [LocallyOfFiniteType q] : topologicalKrullDim X.normalization = topologicalKrullDim X := by
  have := X.isFinite_fromNormalization_of_locallyOfFiniteType q
  exact le_antisymm (topologicalKrullDim_le_of_continuous X.fromNormalization.continuous
      fun _ _ h e ↦ X.fromNormalization.eq_of_specializes_of_apply_eq h e)
    (topologicalKrullDim_le_of_specializingMap X.fromNormalization.isClosedMap.specializingMap
      X.fromNormalization.surjective)

/-- **The normalization over the normal locus.** For every open `U` of an integral scheme `X`
whose local rings are integrally closed, the normalization `ν : X^ν ⟶ X` restricts to an
isomorphism `ν⁻¹ U ⟶ U`: over an affine open `Spec A ⊆ U` the ring `A` is an integrally closed
domain, hence equal to its integral closure in `k(X)`.
(blueprint: `lem-sc-normalization-over-normal-locus`) -/
theorem isIso_fromNormalization_restrict (U : X.Opens)
    (hU : ∀ x ∈ U, IsIntegrallyClosed (X.presheaf.stalk x)) :
    IsIso (X.fromNormalization ∣_ U) :=
  sorry

end AlgebraicGeometry.Scheme
