/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C1
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.FieldTheory.Separable
public import Mathlib.RingTheory.Finiteness.Defs

import Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified
import Mathlib.RingTheory.Etale.Field

/-!
# Unramified algebras over a field

Source: Stacks Project, Morphisms, Lemma 02G7 (1), affine case; Algebra, proof of Lemma 00UW
(blueprint: lem-weil-pbc-unramified-algebra-over-field-product).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- An algebra whose spectrum is unramified over a field is a finite product of finite
separable field extensions, including the empty product for the zero ring.
Source: Stacks Project, Morphisms, Lemma 02G7 (1), and Algebra, proof of Lemma 00UW
(blueprint: lem-weil-pbc-unramified-algebra-over-field-product).

Proof:
1. Apply `lem-weil-pbc-unramified-ring-map-iff-unramified-affine` to the structure map:
   the algebra is finitely generated and its module of relative differentials vanishes.
2. By `lem-weil-pbc-unramified-ring-map-over-field-etale` it is an etale algebra: over
   a field, finite type implies finite presentation and unramified implies formally etale.
3. Apply `lem-weil-pbc-etale-ring-map-iff-etale-affine` to obtain an etale spectrum morphism.
4. Apply `lem-weil-pbc-etale-algebra-over-field-product` to get the finite separable factors
   and their algebra isomorphism. Enumerate the finite index set by `Fin n`. -/
theorem exists_algEquiv_pi_finite_separable_of_unramified_spec
    (k C : Type u) [Field k] [CommRing C] [Algebra k C]
    (hft : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap k C))))
    (hdiag : IsOpenImmersion
      (pullback.diagonal (Spec.map (CommRingCat.ofHom (algebraMap k C))))) :
    ∃ (n : ℕ) (L : Fin n → Type u) (_ : ∀ j, Field (L j))
      (_ : ∀ j, Algebra k (L j)),
      (∀ j, Module.Finite k (L j) ∧ Algebra.IsSeparable k (L j)) ∧
        Nonempty (C ≃ₐ[k] (∀ j, L j)) := by
  classical
  have : Algebra.FiniteType k C := by
    rw [← RingHom.finiteType_algebraMap]
    exact (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mp hft
  have hfu : FormallyUnramified (Spec.map (CommRingCat.ofHom (algebraMap k C))) :=
    inferInstance
  have : Algebra.FormallyUnramified k C := by
    rw [← RingHom.formallyUnramified_algebraMap]
    exact (HasRingHomProperty.Spec_iff (P := @FormallyUnramified)).mp hfu
  have : Algebra.FormallyEtale k C :=
    Algebra.FormallyEtale.of_formallyUnramified_of_field k C
  have : Algebra.Etale k C :=
    ⟨inferInstance, Algebra.FinitePresentation.of_finiteType.mp inferInstance⟩
  obtain ⟨I, hI, L, hL, hA, e, h⟩ :=
    (Algebra.Etale.iff_exists_algEquiv_prod k C).mp inferInstance
  let : Fintype I := Fintype.ofFinite I
  let f : Fin (Fintype.card I) ≃ I := (Fintype.equivFin I).symm
  refine ⟨Fintype.card I, fun j ↦ L (f j), fun j ↦ hL (f j),
    fun j ↦ hA (f j), fun j ↦ h (f j), ?_⟩
  exact ⟨e.trans (AlgEquiv.piCongrLeft k L f).symm⟩

end AlgebraicGeometry
