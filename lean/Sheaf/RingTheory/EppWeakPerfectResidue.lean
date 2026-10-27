module

public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.FieldTheory.Perfect
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.TensorProduct.Quotient
public import Mathlib.RingTheory.Finiteness.Defs

import WeilConjectures.AlgebraicGeometry.Morphisms.DvrUniformizerRootAlgebra

/-! # Weak Epp over a perfect residue field

Source: Stacks Project, More on Algebra, Tag 09F9 (theorem-epp), specialized as
in Tag 09II (proposition-epp-essentially-finite-type).
(blueprint: lem-sfb-epp-weak-perfect-residue)
-/

@[expose] public section

set_option autoImplicit false

universe u v w x

open scoped TensorProduct

namespace IsDiscreteValuationRing

/-- Weak elimination of ramification when the lower residue field is perfect and
its extension to the upper residue field is finitely generated as a field.

The function applied in the conclusion is just a binder for the explicitly
constructed canonical normalization homomorphism: include the second tensor
factor, reduce, and restrict to integral elements. No choice of map is involved.

Source: Stacks Project, More on Algebra, Tag 09F9 (theorem-epp), and the
perfect-residue application in Tag 09II.
(blueprint: lem-sfb-epp-weak-perfect-residue)

Proof:
1. In residue characteristic zero, write the image of a lower uniformizer as
   a unit times the e-th power of an upper uniformizer, by
   lem-weil-pbc-dvr-unit-times-uniformizer-power. Adjoin an e-th root of the
   lower uniformizer. The root algebra is a DVR by
   lem-sbc-dvr-uniformizer-root-algebra and has finite fraction field over K.
   It is the lower integral closure: a negative uniformizer valuation would
   contradict a monic equation after clearing denominators. Apply
   lem-sfb-dvr-algebraic-normalization-structure, case (a), to get maximal
   contractions and both local DVRs; lem-sfb-abhyankar-arbitrary-dvr-branches
   gives equality of the extended maximal ideals.
2. In positive residue characteristic p, use
   lem-sfb-finitely-generated-residue-perfect-core to show that every element
   of the upper perfect core is separable algebraic over the lower residue.
   Apply lem-sfb-epp-strict-complete-reduction with a fixed lower uniformizer.
   The resulting complete pair has algebraically closed lower residue equal
   to the upper perfect core. It suffices to find its prescribed weak solution.
3. Use lem-sfb-epp-compatible-coefficient-dvrs to obtain the coefficient triple
   A0 -> D -> B' with equal extended maximal ideals for A0 -> D and finite
   upper fraction-field degree. Apply lem-sfb-epp-finite-coefficient-triple.
   In equal characteristic p retain its separable-plus-uniformizer-root form.
4. In equal characteristic, A0 -> A' is an isomorphism carrying the parameter
   to the prescribed uniformizer. Transport the solution through it and use
   lem-sfb-epp-strict-complete-reduction to descend to the original pair.
5. In mixed characteristic, choose a field factor N of the reduced tensor
   of Frac(A') with the coefficient solution. By
   lem-sfb-dvr-algebraic-normalization-structure, case (a), this is finite.
   Tensor associativity and reduction identify upper branches with factors
   over the coefficient solution. Integral elements give the canonical local
   maps S -> R -> T, where S is the lower coefficient branch and R the lower
   A' branch. Write successive uniformizers with exponents a,b >= 1 using
   lem-weil-pbc-dvr-unit-times-uniformizer-power. The coefficient solution
   gives ab = 1, hence b = 1, proving equality of the ideals for R -> T.
6. Apply the mixed-characteristic descent clause of
   lem-sfb-epp-strict-complete-reduction. Fraction characteristic zero imposes
   no inseparability restriction. Unpack the weak solution to obtain the
   maximal contraction, both local DVRs and ideal equality at every branch.
-/
theorem exists_epp_weak_perfect_residue
    (A : Type u) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    (K : Type v) [Field K] [Algebra A K] [IsFractionRing A K]
    (B : Type w) [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    [Algebra A B] [IsLocalHom (algebraMap A B)]
    (hinj : Function.Injective (algebraMap A B))
    (L : Type x) [Field L] [Algebra B L] [IsFractionRing B L]
    [Algebra A L] [Algebra K L] [IsScalarTower A B L] [IsScalarTower A K L]
    [PerfectField (IsLocalRing.ResidueField A)]
    (hfg : (⊤ : IntermediateField (IsLocalRing.ResidueField A)
      (IsLocalRing.ResidueField B)).FG) :
    ∃ (N : Type (max u v w x)) (_ : Field N) (_ : Algebra K N)
      (_ : Algebra A N) (_ : IsScalarTower A K N),
      Module.Finite K N ∧
      (fun f : integralClosure A N →+*
          integralClosure B ((L ⊗[K] N) ⧸ nilradical (L ⊗[K] N)) =>
        ∀ (q : Ideal (integralClosure B ((L ⊗[K] N) ⧸ nilradical (L ⊗[K] N))))
          [q.IsMaximal],
          (q.comap f).IsMaximal ∧
          (∃ hdom : IsDomain (Localization.AtPrime (q.comap f)),
            @IsDiscreteValuationRing (Localization.AtPrime (q.comap f)) _ hdom) ∧
          (∃ hdom : IsDomain (Localization.AtPrime q),
            @IsDiscreteValuationRing (Localization.AtPrime q) _ hdom) ∧
          Ideal.map ((algebraMap _ (Localization.AtPrime q)).comp f) (q.comap f) =
            Ideal.map (algebraMap _ (Localization.AtPrime q)) q)
        (((((Ideal.Quotient.mkₐ K (nilradical (L ⊗[K] N))).comp
          Algebra.TensorProduct.includeRight).restrictScalars A).comp
          (integralClosure A N).val).codRestrict
            ((integralClosure B ((L ⊗[K] N) ⧸ nilradical (L ⊗[K] N))).restrictScalars A)
            (fun a => (a.property.map
              (((Ideal.Quotient.mkₐ K (nilradical (L ⊗[K] N))).comp
                Algebra.TensorProduct.includeRight).restrictScalars A)).tower_top)).toRingHom := by
  sorry

end IsDiscreteValuationRing
