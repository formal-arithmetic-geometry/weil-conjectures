module

public import Sheaf.RingTheory.NormalizedTensorMultiplication
public import WeilConjectures.FieldTheory.SeparableExtension
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs

import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.RingTheory.Ideal.GoingUp

/-!
# Descent of a normalized DVR solution to a finite field stage

Source: Stacks Project, More on Algebra, Tag 09II,
`proposition-epp-essentially-finite-type`, final three proof paragraphs, with the
finite-normalization hypothesis recorded by the stage-1 correction
(blueprint: lem-sfb-dvr-normalized-finite-stage-descent).
-/

@[expose] public section

set_option autoImplicit false

universe u v w x y

open scoped TensorProduct

namespace IsDiscreteValuationRing

/-- An algebraic normalized solution with finite upper normalization descends to a
finite intermediate field of the given algebraic extension.

Source: Stacks Project, More on Algebra, Tag 09II,
`proposition-epp-essentially-finite-type`, final three proof paragraphs, with the
finite-module repair recorded in the DAG
(blueprint: lem-sfb-dvr-normalized-finite-stage-descent).

Proof:
1. Direct the finite intermediate fields by compositum. Integral elements, their
   monic equations, tensor expressions and nilpotence witnesses occur at finite
   stages. Thus both normalizations are unions of their finite-stage versions,
   with injective integral transition maps.
2. Apply lem-sfb-dvr-algebraic-normalization-structure, case (a), at each finite
   stage and case (b) at the limit. Apply lem-sfb-finite-normalization-algebraic-model
   using precisely the finite-module hypothesis to obtain a finite stage after
   which `C_F ⊗[R_F] R_P` is canonically `C_P`.
3. The limit spectra are finite. Separate their finitely many distinct primes
   by elements of a common finite stage. Integral lying-over
   (lem-weil-pbc-integral-injective-lying-over) makes contraction surjective;
   going-up (pqf-lem-going-up) makes its inverse preserve inclusion. Hence these
   bijections identify maximal primes and all primes below them.
4. Put the numerators and denominators of the finitely many lower uniformizers
   into a common finite stage. A nonunit of a DVR becoming a uniformizer in a
   local DVR extension was already a uniformizer: otherwise its image lies in
   the square of the target maximal ideal. Apply this to both lower and upper
   local rings, using the hypothesized equality of extended maximal ideals.
5. Localize the model isomorphism of step 2 at a maximal prime. The spectrum
   bijections of step 3 identify the result with `(C_P)_q`; localization at the
   lower prime changes nothing. Quotient by the common uniformizer to obtain
   the actual canonical residue-field tensor isomorphism
   `κ(q_F) ⊗[κ(n_F)] κ(n) ≃ κ(q)`.
6. Apply lem-sfb-separability-tensor-field-descent to that tensor-field
   isomorphism and the assumed separability over the limit lower residue field.
   The one common finite stage works for all finitely many maximal primes,
   yielding maximal contractions, both local DVRs, equal extended maximal
   ideals and separable residue extensions as asserted.
-/
theorem exists_normalized_finite_stage
    (A : Type u) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    (B : Type v) [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    [Algebra A B] [IsLocalHom (algebraMap A B)]
    (hinj : Function.Injective (algebraMap A B))
    (K : Type w) [Field K] [Algebra A K] [IsFractionRing A K]
    (L : Type x) [Field L] [Algebra B L] [IsFractionRing B L]
    [Algebra A L] [Algebra K L] [IsScalarTower A B L] [IsScalarTower A K L]
    (hfiniteType : ∃ (U : Type (max u v)) (_ : CommRing U) (_ : Algebra A U)
      (p : Ideal U) (_ : p.IsPrime),
      RingHom.FiniteType (algebraMap A U) ∧ Nonempty (B ≃ₐ[A] Localization.AtPrime p))
    (P : Type y) [Field P] [Algebra K P] [Algebra.IsAlgebraic K P]
    [Algebra A P] [IsScalarTower A K P]
    (hfiniteModule : @Module.Finite (B ⊗[A] integralClosure A P)
      (normalizedUpperClosure B K L P) _ _
      (normalizedTensorMultiplication A B K L P).toAlgebra.toModule)
    [IsNoetherianRing (integralClosure A P)]
    [IsNoetherianRing (normalizedUpperClosure B K L P)]
    (hmaxLower : Finite {n : Ideal (integralClosure A P) // n.IsMaximal})
    (hmaxUpper : Finite {q : Ideal (normalizedUpperClosure B K L P) // q.IsMaximal})
    (hlocal : ∀ (q : Ideal (normalizedUpperClosure B K L P)) [q.IsMaximal],
      (q.comap (normalizedLowerMap A B K L P)).IsMaximal ∧
      IsDiscreteValuationRing (Localization.AtPrime (q.comap (normalizedLowerMap A B K L P))) ∧
      (∃ hdom : IsDomain (Localization.AtPrime q),
        @IsDiscreteValuationRing (Localization.AtPrime q) _ hdom) ∧
      Ideal.map ((algebraMap (normalizedUpperClosure B K L P) (Localization.AtPrime q)).comp
        (normalizedLowerMap A B K L P)) (q.comap (normalizedLowerMap A B K L P)) =
          Ideal.map (algebraMap (normalizedUpperClosure B K L P) (Localization.AtPrime q)) q ∧
      @Algebra.IsSeparableExtension (q.comap (normalizedLowerMap A B K L P)).ResidueField
        q.ResidueField _ _
        (Ideal.ResidueField.map (q.comap (normalizedLowerMap A B K L P)) q
          (normalizedLowerMap A B K L P) rfl).toAlgebra ∧
      @IntermediateField.FG (q.comap (normalizedLowerMap A B K L P)).ResidueField _
        q.ResidueField _
        (Ideal.ResidueField.map (q.comap (normalizedLowerMap A B K L P)) q
          (normalizedLowerMap A B K L P) rfl).toAlgebra ⊤) :
    ∃ K₀ : IntermediateField K P, Module.Finite K K₀ ∧
      ∀ (q : Ideal (normalizedUpperClosure B K L K₀)) [q.IsMaximal],
        (q.comap (normalizedLowerMap A B K L K₀)).IsMaximal ∧
        IsDiscreteValuationRing (Localization.AtPrime (q.comap (normalizedLowerMap A B K L K₀))) ∧
        (∃ hdom : IsDomain (Localization.AtPrime q),
          @IsDiscreteValuationRing (Localization.AtPrime q) _ hdom) ∧
        Ideal.map ((algebraMap (normalizedUpperClosure B K L K₀) (Localization.AtPrime q)).comp
          (normalizedLowerMap A B K L K₀)) (q.comap (normalizedLowerMap A B K L K₀)) =
            Ideal.map (algebraMap (normalizedUpperClosure B K L K₀) (Localization.AtPrime q)) q ∧
        @Algebra.IsSeparableExtension (q.comap (normalizedLowerMap A B K L K₀)).ResidueField
          q.ResidueField _ _
          (Ideal.ResidueField.map (q.comap (normalizedLowerMap A B K L K₀)) q
            (normalizedLowerMap A B K L K₀) rfl).toAlgebra := by
  sorry

end IsDiscreteValuationRing
