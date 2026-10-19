/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q14
-/
module

public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.FieldTheory.PurelyInseparable.Basic
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.FiniteType
public import Sheaf.RingTheory.ExcellentRing
import Mathlib.RingTheory.Noetherian.Basic
import WeilConjectures.FieldTheory.SeparableExtension
import WeilConjectures.FieldTheory.MakeSeparable
import Sheaf.RingTheory.JZeroFiniteTypeDomainDescent
import Sheaf.RingTheory.NonemptyRegularOpenSeparableAscent
import Sheaf.RingTheory.RegularLocusOpenFromPrimeQuotients
import WeilConjectures.FieldTheory.MakeSeparable
import WeilConjectures.FieldTheory.SeparableExtension

/-!
# A residue-field finite-model criterion for J-2

Source: Stacks Project, More on Algebra, Tag 07PC, lemma-J-2, implication (4) to (1),
with J-0 and J-2 expanded using Tag 07P7, definition-J
(blueprint: lem-exc-j2-residue-field-criterion).
-/

@[expose] public section

set_option autoImplicit false

universe u v

/-- Finite models with a nonempty regular open for finite purely inseparable residue-field
extensions imply that every finite type algebra has open regular locus, the J-2 condition
in `IsQuasiExcellent`.

Source: Stacks Project, More on Algebra, Tag 07PC, lemma-J-2, implication (4) to (1),
and Tag 07P7, definition-J (blueprint: lem-exc-j2-residue-field-criterion).

Proof (the seven steps of the node):
1. Let `S` be a finite type domain over `R`, `p` the kernel of `R → S`, and `K` its
   fraction field. By `lem-weil-pbc-finite-type-algebra-noetherian`, `S` is Noetherian.
   Fractions of images of elements of `R` embed `p.ResidueField` into `K`: equality of
   two residue fractions and equality of their images both mean their cross difference
   lies in `p`. Finite algebra generators of `S` generate `K` as a field over this residue
   field (`def-weil-pbc-finite-type-algebra`, `def-weil-pbc-localization-at-prime`).
2. By `lem-weil-pbc-make-separable`, extend the residue field to `L` and `K` to `K'`
   by finite purely inseparable extensions so that `K'/L` is separable and the square
   commutes. Identify these fields with their images in `K'`.
3. Choose the finite subalgebra `B` of `L` from the hypothesis. It is Noetherian by
   `lem-weil-pbc-finite-algebra-noetherian`. Inside `K'`, form `S'` from finite sums of
   products of elements of `S` and `B`. Distributivity makes this a subring containing
   both rings. Algebra generators of `S` generate `S'` over `B`; finite module generators
   of `B` generate `S'` over `S`. Thus both inclusions are injective and of finite type
   (`def-weil-finitely-generated-module`, `def-weil-pbc-finite-type-algebra`).
4. The fraction field of `S'` is the compositum `KL`, since it contains both fraction
   fields and is contained in their compositum. It need not be all of `K'`. Every finitely
   generated intermediate field of `KL/L` is one of `K'/L`, so `KL/L` is separable by
   `def-weil-pbc-separable-field-extension`.
5. Apply `lem-exc-j0-separable-finite-type-ascent` to `B → S'`, using the chosen regular
   open of `B`, then `lem-exc-j0-finite-type-domain-descent` to `S → S'`. Thus every finite
   type domain over `R` has a nonempty regular open.
6. For any finite type algebra `A`, each prime quotient `A/q` is a finite type domain:
   images of algebra generators generate the quotient. Step 5 supplies its regular open.
   The algebra `A` is Noetherian by `lem-weil-pbc-finite-type-algebra-noetherian`, so
   `lem-exc-regular-locus-open-from-prime-quotients` gives openness of its regular locus.
   This includes the zero algebra, whose prime spectrum is empty.
7. This conclusion is exactly the expanded J-2 clause of `def-exc-excellent-ring`.
-/
theorem isOpen_regularLocus_of_residueField_finite_models
    (R : Type u) [CommRing R] [IsNoetherianRing R]
    (hmodels : ∀ (p : Ideal R) [p.IsPrime] (L : Type (max u v)) [Field L]
      [Algebra p.ResidueField L] [Algebra R L] [IsScalarTower R p.ResidueField L]
      [Module.Finite p.ResidueField L] [IsPurelyInseparable p.ResidueField L],
      ∃ B : Subalgebra R L, Module.Finite R B ∧
        (∀ x : L, ∃ b c : B, (c : L) ≠ 0 ∧ x = (b : L) / (c : L)) ∧
        ∃ U : Set (PrimeSpectrum B), IsOpen U ∧ U.Nonempty ∧
          ∀ q ∈ U, IsRegularLocalRing (Localization.AtPrime q.asIdeal))
    (A : Type (max u v)) [CommRing A] [Algebra R A] [Algebra.FiniteType R A] :
    IsOpen {q : PrimeSpectrum A | IsRegularLocalRing (Localization.AtPrime q.asIdeal)} := by
  sorry
