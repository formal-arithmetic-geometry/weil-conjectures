/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF groups K1, G6
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.RingTheory.LocalProperties.IntegrallyClosed
import WeilConjectures.Mathlib.AlgebraicGeometry.FunctionField
import WeilConjectures.Mathlib.RingTheory.DedekindDomain.IntegralClosure

/-!
# A finite-type integral scheme contains a normal open

Source: Blueprint, `sec-smooth-purity/sk-prop-a1-kummer/lem-fin-dense-normal-open`
(blueprint: lem-fin-dense-normal-open).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

variable {k : Type u} [Field k] {X : Scheme.{u}}

/-- Every integral finite-type scheme over a field has a nonempty open subscheme whose local
    rings are integrally closed (the normal-open conclusion of the blueprint).

    (blueprint: lem-fin-dense-normal-open)

    Choose a nonempty affine open `Spec B` in `X`. Since `X` is integral, `B` is a domain.
    Noether finiteness (`Algebra.FiniteType.finite_integralClosure`) makes the integral closure
    of `B` in its fraction field a finite `B`-module. The proved common-denominator lemma
    `exists_isInteger_smul_of_finite_integralClosure` supplies a nonzero `b` clearing all
    integral elements. The proved criterion `isIntegrallyClosed_of_isLocalization_away`
    then makes `B[1/b]` integrally closed. The generic point belongs to `D(b)`, so this affine
    open is nonempty. Its stalks are localizations of `B[1/b]`, hence integrally closed.

    This is the normal-open construction in the proof of the source-library theorem
    `Scheme.exists_isIso_fromNormalization_restrict`, without the final assertion about
    the normalization morphism. -/
theorem exists_nonempty_normal_open (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f]
    [QuasiCompact f] [IsIntegral X] :
    ∃ U : X.Opens, Nonempty U ∧ ∀ x : X, x ∈ U → IsIntegrallyClosed (X.presheaf.stalk x) := by
  obtain ⟨x⟩ := (inferInstance : Nonempty X)
  obtain ⟨V, hV, hxV, -⟩ := exists_isAffineOpen_mem_and_subset (x := x) (U := ⊤) trivial
  have : Nonempty V := ⟨⟨x, hxV⟩⟩
  let := ((f.appLE ⊤ V le_top).hom.comp (Scheme.ΓSpecIso (.of k)).inv.hom).toAlgebra
  have : Algebra.FiniteType k Γ(X, V) :=
    RingHom.FiniteType.comp (HasRingHomProperty.appLE @LocallyOfFiniteType f ‹_›
      ⟨⊤, isAffineOpen_top _⟩ ⟨V, hV⟩ le_top) (RingHom.FiniteType.of_surjective _
        (Scheme.ΓSpecIso (.of k)).commRingCatIsoToRingEquiv.symm.surjective)
  have := functionField_isFractionRing_of_isAffineOpen X V hV
  have := Algebra.FiniteType.finite_integralClosure k (A := Γ(X, V)) X.functionField
    X.functionField
  obtain ⟨b, hb, hbint⟩ := exists_isInteger_smul_of_finite_integralClosure (A := Γ(X, V))
    (K := X.functionField)
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have hηV : genericPoint X ∈ V :=
    ((genericPoint_spec X).mem_open_set_iff V.isOpen).mpr (by simpa using ‹Nonempty V›)
  have hηW : genericPoint X ∈ X.basicOpen b := by
    rw [X.mem_basicOpen b _ hηV]
    exact isUnit_iff_ne_zero.mpr ((map_ne_zero_iff _ (X.germToFunctionField_injective V)).mpr hb0)
  have hW : IsAffineOpen (X.basicOpen b) := hV.basicOpen b
  have : Nonempty (X.basicOpen b) := ⟨⟨_, hηW⟩⟩
  have := hV.isLocalization_basicOpen b
  have := functionField_isFractionRing_of_isAffineOpen X _ hW
  have : IsScalarTower Γ(X, V) Γ(X, X.basicOpen b) X.functionField :=
    .of_algebraMap_eq fun a ↦ (X.presheaf.germ_res_apply _ _ _ a).symm
  have : IsIntegrallyClosed Γ(X, X.basicOpen b) :=
    isIntegrallyClosed_of_isLocalization_away hb0 hbint
  refine ⟨X.basicOpen b, ⟨⟨_, hηW⟩⟩, fun y hy ↦ ?_⟩
  let := TopCat.Presheaf.algebra_section_stalk X.presheaf (⟨y, hy⟩ : X.basicOpen b)
  have := hW.isLocalization_stalk ⟨y, hy⟩
  exact isIntegrallyClosed_of_isLocalization _ _
    (hW.primeIdealOf ⟨y, hy⟩).asIdeal.primeCompl_le_nonZeroDivisors

end AlgebraicGeometry
