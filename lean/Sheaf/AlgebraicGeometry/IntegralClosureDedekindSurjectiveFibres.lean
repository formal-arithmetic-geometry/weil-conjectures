/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import Mathlib.RingTheory.DedekindDomain.IntegralClosure
public import Mathlib.RingTheory.KrullDimension.Basic
import Sheaf.RingTheory.DimOneResidueFieldsFinite
import Sheaf.RingTheory.KrullAkizukiNoetherian
import Sheaf.RingTheory.LocalizationPrimeResidueFieldIso
import WeilConjectures.Mathlib.RingTheory.Ideal.HasGoingUp

/-!
# Integral closure of a one-dimensional Noetherian domain

Source: literature/stacks-project/algebra.tex, Algebra Lemma 09IG
(blueprint: lem-sc-integral-closure-dedekind-surjective-fibres).
-/

@[expose] public section

universe u v

open AlgebraicGeometry

namespace AlgebraicGeometry

/-- The integral closure of a one-dimensional Noetherian domain in a finite field
extension is Dedekind, and its spectrum maps surjectively with finite fibres and
finite residue-field extensions (Stacks, Algebra Lemma 09IG).

Proof (Stacks, Algebra Lemma 09IG, `lemma-integral-closure-Dedekind`):
1. Since `A ⊆ C ⊆ L`, Krull--Akizuki gives Noetherianity of `C`
   (`lem-sc-krull-akizuki-noetherian`).
2. The integral injective inclusion preserves dimension, giving `dim C = 1`
   (`lem-weil-pbc-integral-injective-dimension-equal`). The integral closure is a
   normal domain with fraction field `L`
   (`lem-weil-pbc-integral-closure-finite-extension-normal`), hence is Dedekind.
3. Lying over for the integral injective inclusion gives surjectivity on spectra
   (`lem-weil-pbc-integral-injective-lying-over`).
4. At a maximal ideal of `A`, localize both rings at its complement. The prime
   correspondence and residue-field isomorphisms
   (`lem-weil-pbc-localization-prime-residue-field-iso`) identify the closed fibre
   and its residue extensions with those of the localized map. Its source is a
   one-dimensional Noetherian local domain, so the local finiteness theorem
   (`lem-weil-pbc-dim-one-residue-field-extensions-finite`) makes this fibre and
   these extensions finite. At the generic prime, incomparability
   (`lem-weil-pbc-integral-incomparability`) leaves only the zero prime in `C`;
   the residue extension is the given finite extension `L/K`.

Mathlib's Dedekind predicate permits dimension zero, so dimension one is stated
separately to retain the node's convention.
(blueprint: lem-sc-integral-closure-dedekind-surjective-fibres).
-/
theorem integralClosure_isDedekind_surjective_finite_fibres
    (A L : Type u) (K : Type v) [CommRing A] [IsDomain A] [Field K] [Field L]
    [Algebra A K] [IsFractionRing A K] [Algebra K L] [Algebra A L]
    [IsScalarTower A K L] [FiniteDimensional K L] [IsNoetherianRing A]
    (hA : ringKrullDim A = 1) :
    let C := integralClosure A L
    let f : Spec (CommRingCat.of C) ⟶ Spec (CommRingCat.of A) :=
      Spec.map (CommRingCat.ofHom (algebraMap A C))
    IsDedekindDomain C ∧ ringKrullDim C = 1 ∧ Function.Surjective f.base ∧
      (∀ y : Spec (CommRingCat.of A), Finite (f ⁻¹' {y})) ∧
      (∀ x : Spec (CommRingCat.of C), (f.residueFieldMap x).hom.Finite) := by
  sorry

end AlgebraicGeometry
