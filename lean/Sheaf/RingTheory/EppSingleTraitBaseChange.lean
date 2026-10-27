/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q10
-/
module

public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Algebraic.Defs
public import Sheaf.RingTheory.ExcellentRing

import Sheaf.RingTheory.CompleteDVRFiniteNormalization
import Sheaf.FieldTheory.FiniteSeparableTensorFieldReduced
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.FieldTheory.SeparablyGenerated
import Mathlib.FieldTheory.Perfect
import WeilConjectures.FieldTheory.SeparableExtension
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.Localization.Integral

/-!
# Epp base change for a single trait

Source: Illusie--Laszlo--Orgogozo, Travaux de Gabber, Expose IV, Theorem 3.1.2,
Remark 3.1.3 and the finite-base-change stability sentence in Section 4.2.3
(blueprint: lem-per-epp-single-trait-base-change).
-/

@[expose] public section

set_option autoImplicit false

universe u v w x y

open scoped TensorProduct

namespace IsDiscreteValuationRing

/-- Goodness of a finite trait extension: every normalized generic field factor has
reduced special fibre. The fraction fields and their maps are canonical. The tensor map
sends `t tensor a` to their images in the generic tensor product. Its composite with the
maximal-ideal quotient supplies the algebra used by `integralClosure`. Integrality over
this tensor algebra is exactly integrality over its image in the field factor.
Quantifying over all uniformizers avoids choosing a generator of the maximal ideal.

Source: Illusie--Laszlo--Orgogozo, Travaux de Gabber, IV 3.1.1--3.1.3 and 4.2.3
(blueprint: lem-per-epp-single-trait-base-change). -/
noncomputable def IsGoodSingleTraitExtension
    (W0 : Type u) (T : Type v) (W' : Type w)
    [CommRing W0] [IsDomain W0] [CommRing T] [IsDomain T]
    [CommRing W'] [IsDomain W'] [Algebra W0 T] [Algebra W0 W']
    [FaithfulSMul W0 T] [FaithfulSMul W0 W'] : Prop :=
  letI := FractionRing.liftAlgebra W0 (FractionRing T)
  letI := FractionRing.liftAlgebra W0 (FractionRing W')
  letI := FractionRing.isScalarTower_liftAlgebra W0 (FractionRing T)
  letI := FractionRing.isScalarTower_liftAlgebra W0 (FractionRing W')
  ∀ (π' : W'), Irreducible π' →
    ∀ q : Ideal (FractionRing T ⊗[FractionRing W0] FractionRing W'), q.IsMaximal →
      letI := ((Ideal.Quotient.mk q).comp
        (Algebra.TensorProduct.mapRingHom (algebraMap W0 (FractionRing W0))
          (algebraMap T (FractionRing T)) (algebraMap W' (FractionRing W'))
          ((IsScalarTower.algebraMap_eq W0 T (FractionRing T)).symm.trans
            (IsScalarTower.algebraMap_eq W0 (FractionRing W0) (FractionRing T)))
          ((IsScalarTower.algebraMap_eq W0 W' (FractionRing W')).symm.trans
            (IsScalarTower.algebraMap_eq W0 (FractionRing W0) (FractionRing W'))))).toAlgebra
      IsReduced
        ((integralClosure (T ⊗[W0] W')
          ((FractionRing T ⊗[FractionRing W0] FractionRing W') ⧸ q)) ⧸
          Ideal.span {algebraMap (T ⊗[W0] W')
            (integralClosure (T ⊗[W0] W')
              ((FractionRing T ⊗[FractionRing W0] FractionRing W') ⧸ q))
            ((1 : T) ⊗ₜ[W0] π')})

/-- The structural assertion about a finite extension in the single-trait statement:
its fraction-field extension is finite and the generic tensor is a finite product of
fields. The product presentation is asserted to exist; it is not chosen to define any
normalization or map. Each field can be realized as a quotient of the generic tensor,
so the common universe does not restrict the assertion.

Source: Illusie--Laszlo--Orgogozo, Travaux de Gabber, IV 3.1.2--3.1.3
(blueprint: lem-per-epp-single-trait-base-change). -/
noncomputable def HasSingleTraitGenericStructure
    (W0 : Type u) (T : Type v) (W' : Type w)
    [CommRing W0] [IsDomain W0] [CommRing T] [IsDomain T]
    [CommRing W'] [IsDomain W'] [Algebra W0 T] [Algebra W0 W']
    [FaithfulSMul W0 T] [FaithfulSMul W0 W'] : Prop :=
  letI := FractionRing.liftAlgebra W0 (FractionRing T)
  letI := FractionRing.liftAlgebra W0 (FractionRing W')
  Module.Finite (FractionRing W0) (FractionRing W') ∧
    ∃ (n : ℕ) (E : Fin n → Type (max u v w)) (_ : ∀ i : Fin n, Field (E i)),
      Nonempty ((FractionRing T ⊗[FractionRing W0] FractionRing W') ≃+*
        ((i : Fin n) → E i))

/-- Epp's single-trait theorem, reducedness of every finite base change, and stability
of goodness under every further finite trait extension. Injectivity is expressed by
`FaithfulSMul`, equivalent to injectivity of the algebra map. Finite extensions in the
existence clause may be realized in the universe of the base ring, since they are finite
modules. The two universal clauses allow arbitrary extension universes.

Source: Illusie--Laszlo--Orgogozo, Travaux de Gabber, IV Theorem 3.1.2,
Remark 3.1.3 and Section 4.2.3
(blueprint: lem-per-epp-single-trait-base-change).

Proof:
1. For each finite extension W', complete-DVR finite normalization identifies W'
   with the integral closure in its fraction field. Finiteness implies integrality
   (lem-weil-pbc-finite-algebra-is-integral); torsion-free finite modules over a DVR
   are free (lem-sc-dvr-fg-torsionfree-free). The normalization-structure theorem
   lem-sfb-dvr-algebraic-normalization-structure and integral transitivity identify
   the normalized tensor algebra with the product of the field-factor closures B_E.
2. A basis of W' embeds T tensor W' into its generic tensor algebra. Localization
   and tensor products commute (lem-weil-pbc-localization-tensor); a DVR fraction
   field inverts its uniformizer (lem-weil-pbc-dvr-unit-times-uniformizer-power).
   Characteristic zero gives separability (lem-weil-pbc-char-zero-field-extension-separable,
   def-weil-pbc-separable-field-extension), so the generic tensor algebra is reduced by
   lem-weil-pbc-finite-separable-tensor-field-reduced. Finite-dimensional reduced
   commutative field algebras are finite products of fields, as in step 1. This gives
   the stated generic structure and reducedness of T tensor W'.
3. At each maximal localization of the normalization, write pi' = unit times t^e
   by lem-weil-pbc-dvr-unit-times-uniformizer-power. The special fibre is reduced
   exactly when e = 1. Reducedness is detected at maximal localizations and on
   finite products. A unit change of uniformizer leaves the quotient unchanged.
4. The perfect-core hypothesis is separable algebraicity, since k0 is perfect
   (lem-weil-pbc-perfect-field-separating-basis). Apply
   lem-sfb-epp-strict-complete-reduction and lem-sfb-epp-compatible-coefficient-dvrs
   to obtain the complete coefficient triple with algebraically closed lower residue
   field and perfect-core equality. Characteristic zero removes the descent restriction.
5. Apply lem-sfb-epp-finite-coefficient-triple. Choose a field factor of the lower
   fraction-field tensor product using lem-sfb-dvr-algebraic-normalization-structure.
   Tensor associativity and characteristic-zero separability identify its upper
   factors with a subset of the factors supplied by that weak solution.
6. For local DVRs S -> R -> U, write s = unit times r^i and r = unit times t^j
   (lem-weil-pbc-dvr-unit-times-uniformizer-power). Since sU is maximal, ij = 1,
   hence j = 1. Descend the weak solution by lem-sfb-epp-strict-complete-reduction;
   lem-per-complete-dvr-finite-normalization and step 3 give a good finite extension.
7. For a good W', its finite residue extension is perfect by
   lem-per-algebraic-extension-perfect. Each normalized local branch has index one
   and separable residue extension (lem-weil-pbc-perfect-field-separating-basis and
   def-weil-pbc-separable-field-extension). Apply
   lem-sfb-dvr-index-one-separable-base-change to each branch and the further finite
   fraction-field extension. Complete-DVR normalization identifies the lower ring
   with W''. A local W0-algebra map W' -> W'' is injective: a nonzero kernel contains
   a power of its uniformizer, hence a nonzero base element, which is impossible.
8. Integral transitivity identifies each new field-factor closure with the closure
   of the preceding B_E (lem-weil-pbc-integral-transitive). Maximal ideals contract
   to maximal ideals (lem-weil-pbc-integral-maximal-contracts-maximal), and integral
   closure commutes with localization (lem-weil-pbc-integral-closure-commutes-localization).
   Thus every new branch is one from step 7. Step 3 gives goodness of W''.
-/
theorem epp_single_trait_base_change
    (p : ℕ) (hp : p.Prime)
    (W0 : Type u) [CommRing W0] [IsDomain W0] [IsDiscreteValuationRing W0]
    [IsAdicComplete (IsLocalRing.maximalIdeal W0) W0]
    [CharZero (FractionRing W0)] [CharP (IsLocalRing.ResidueField W0) p]
    (hperfect : Function.Surjective (fun a : IsLocalRing.ResidueField W0 => a ^ p))
    (T : Type v) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T]
    [Algebra W0 T] [FaithfulSMul W0 T] [IsLocalHom (algebraMap W0 T)]
    (hexcellent : IsExcellent T)
    (hcore : ∀ a : IsLocalRing.ResidueField T,
      (∀ n : ℕ, ∃ b : IsLocalRing.ResidueField T, b ^ (p ^ n) = a) →
        IsAlgebraic (IsLocalRing.ResidueField W0) a) :
    (∃ (W' : Type u) (_ : CommRing W') (_ : IsDomain W')
      (_ : IsDiscreteValuationRing W') (_ : Algebra W0 W')
      (_ : FaithfulSMul W0 W') (_ : IsLocalHom (algebraMap W0 W')),
      IsAdicComplete (IsLocalRing.maximalIdeal W') W' ∧ Module.Finite W0 W' ∧
        IsGoodSingleTraitExtension W0 T W') ∧
    (∀ (W' : Type x) [CommRing W'] [IsDomain W'] [IsDiscreteValuationRing W']
      [Algebra W0 W'] [FaithfulSMul W0 W'] [IsLocalHom (algebraMap W0 W')]
      [IsAdicComplete (IsLocalRing.maximalIdeal W') W'] [Module.Finite W0 W'],
      (IsReduced (T ⊗[W0] W') ∧ HasSingleTraitGenericStructure W0 T W')) ∧
    (∀ (W' : Type x) [CommRing W'] [IsDomain W'] [IsDiscreteValuationRing W']
      [Algebra W0 W'] [FaithfulSMul W0 W'] [IsLocalHom (algebraMap W0 W')]
      [IsAdicComplete (IsLocalRing.maximalIdeal W') W'] [Module.Finite W0 W'],
      IsGoodSingleTraitExtension W0 T W' →
        ∀ (W'' : Type y) [CommRing W''] [IsDomain W''] [IsDiscreteValuationRing W'']
          [Algebra W0 W''] [FaithfulSMul W0 W''] [IsLocalHom (algebraMap W0 W'')]
          [IsAdicComplete (IsLocalRing.maximalIdeal W'') W''] [Module.Finite W0 W'']
          (f : W' →ₐ[W0] W''), IsLocalHom f.toRingHom →
            IsGoodSingleTraitExtension W0 T W'') := by
  sorry

end IsDiscreteValuationRing
