/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
public import WeilConjectures.Mathlib.AlgebraicGeometry.ZariskisMainTheorem

/-!
# Proper quasi-finite morphisms are finite

A morphism of schemes which is proper and locally quasi-finite is finite
(`AlgebraicGeometry.IsFinite.of_isProper_of_locallyQuasiFinite`, Stacks 02LS, a consequence of
Zariski's main theorem). This file records the elementary facts around this statement used in
the blueprint, and the variant with finite fibres.

## Main statements

- `AlgebraicGeometry.Scheme.Hom.discreteTopology_fiber_and_quasiFiniteAt`: a morphism locally of
  finite type with a finite fibre is quasi-finite at the points of that fibre, and the fibre is
  discrete.
- `AlgebraicGeometry.locallyQuasiFinite_and_quasiCompact_iff_finite_preimage_singleton`:
  quasi-finite morphisms are the morphisms of finite type with finite fibres.
- `AlgebraicGeometry.IsFinite.iff_isProper_and_finite_preimage_singleton`: a morphism is finite
  if and only if it is proper with finite fibres.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- **Basic properties of proper morphisms.** A proper morphism is separated, universally
closed, of finite type, quasi-compact and quasi-separated; if the target is affine, the source
is separated and quasi-compact.

(blueprint: `pqf-lem-proper-basic`) -/
theorem IsProper.isSeparated_and_universallyClosed [IsProper f] :
    IsSeparated f ∧ UniversallyClosed f ∧ LocallyOfFiniteType f ∧ QuasiCompact f ∧
      QuasiSeparated f ∧ (IsAffine S → IsSeparated (X ↘ ⊤_ Scheme) ∧ CompactSpace X) :=
  ⟨inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, fun _ ↦
    ⟨by rw [terminal.hom_ext (X ↘ ⊤_ Scheme) (f ≫ terminal.from S)]; infer_instance,
      QuasiCompact.compactSpace_of_compactSpace f⟩⟩

/-- **Finite morphisms are quasi-finite**: a finite morphism is locally quasi-finite and
quasi-compact.

(blueprint: `pqf-lem-finite-qf`) -/
theorem IsFinite.locallyQuasiFinite_and_quasiCompact [IsFinite f] :
    LocallyQuasiFinite f ∧ QuasiCompact f :=
  ⟨inferInstance, inferInstance⟩

/-- **Quasi-finite morphisms have finite fibres.** A morphism is locally quasi-finite and
quasi-compact if and only if it is locally of finite type, quasi-compact and has finite fibres.

Here "locally quasi-finite" is Mathlib's `LocallyQuasiFinite` (quasi-finite stalk maps, which
does not include finite type: `Spec ℚ ⟶ Spec ℤ` is locally quasi-finite and quasi-compact), so
the finite type hypothesis appears on both sides.

(blueprint: `pqf-lem-qf-finitefibres`) -/
theorem locallyQuasiFinite_and_quasiCompact_iff_finite_preimage_singleton :
    (LocallyOfFiniteType f ∧ LocallyQuasiFinite f ∧ QuasiCompact f) ↔
      (LocallyOfFiniteType f ∧ QuasiCompact f ∧ ∀ s : S, (f ⁻¹' {s}).Finite) :=
  ⟨fun ⟨h₁, _, h₃⟩ ↦ ⟨h₁, h₃, f.finite_preimage_singleton⟩,
    fun ⟨h₁, h₃, h⟩ ↦ ⟨h₁, .of_finite_preimage_singleton f h, h₃⟩⟩

/-- **A finite fibre is discrete.** If `f` is locally of finite type and the fibre `f⁻¹{s}` is
finite, then the fibre `X_s` is a finite discrete space and `f` is quasi-finite at every point of
`X` lying over `s`.

(blueprint: `pqf-lem-locqf-fibre-discrete`) -/
theorem Scheme.Hom.discreteTopology_fiber_and_quasiFiniteAt [LocallyOfFiniteType f] (s : S)
    (hs : (f ⁻¹' {s}).Finite) :
    Finite (f.fiber s) ∧ DiscreteTopology (f.fiber s) ∧ ∀ x : X, f x = s → f.QuasiFiniteAt x :=
  by
  have hfin : Finite (f.fiber s) := (f.fiberHomeo s).finite_iff.mpr hs
  refine ⟨hfin, inferInstance, ?_⟩
  rintro x rfl
  exact Scheme.Hom.quasiFiniteAt_iff_isOpen_singleton_asFiber.mpr (isOpen_discrete _)

/-- **Finite = proper with finite fibres.** A morphism of schemes is finite if and only if it is
proper with finite fibres. The blueprint assumes the target locally noetherian and argues with
Serre's criterion for affineness; the statement holds without this assumption, and is proved
here through Zariski's main theorem
(`AlgebraicGeometry.IsFinite.iff_isProper_and_locallyQuasiFinite`).

(blueprint: `thm-pqf-finite-iff-proper-finite-fibres`) -/
theorem IsFinite.iff_isProper_and_finite_preimage_singleton :
    IsFinite f ↔ IsProper f ∧ ∀ s : S, (f ⁻¹' {s}).Finite :=
  by
  rw [IsFinite.iff_isProper_and_locallyQuasiFinite]
  exact ⟨fun ⟨_, _⟩ ↦ ⟨inferInstance, f.finite_preimage_singleton⟩,
    fun ⟨_, h⟩ ↦ ⟨inferInstance, .of_finite_preimage_singleton f h⟩⟩

end AlgebraicGeometry
