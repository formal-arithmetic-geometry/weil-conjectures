module

public import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs
public import Mathlib.FieldTheory.Separable
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.RingTheory.Localization.FractionRing

import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.FieldTheory.SeparableClosure
import Mathlib.FieldTheory.SeparableDegree
import Mathlib.RingTheory.Ideal.GoingUp
import WeilConjectures.AlgebraicGeometry.Morphisms.DvrUniformizerRootAlgebra
import WeilConjectures.RingTheory.DvrNormalizedCompositumLocalDiagram
import WeilConjectures.RingTheory.DvrAbhyankarLocalMaximalIdeal
import WeilConjectures.RingTheory.DvrAbhyankarLocalResidue

/-! # Domination of a tame extension by a uniformizer-root extension

Source: Stacks Project, Tag 0EXW, implication (1) to (2), and Tag 09EV.
(blueprint: lem-sfb-tame-extension-uniformizer-root-domination)
-/

@[expose] public section

universe u v w

namespace RingTheory

/-- A finite tame extension embeds in an extension unramified over a uniformizer-root base.

Source: Stacks Project, Tag 0EXW, implication (1) to (2), and Tag 09EV.
(blueprint: lem-sfb-tame-extension-uniformizer-root-domination)

The fields `K` and rings `A` below are fixed by their displayed equalities to the
Mathlib adjoins, rather than arbitrary intermediate objects. The elements `aK` and
`aA` express the same chosen root in those subtypes. Residue algebra structures
commute with `R`, so they are the canonical structures induced by constants.

Proof:
1. A DVR is Noetherian and normal (lem-weil-pbc-pid-noetherian-normal). Its normalization
   in the finite separable extension is finite
   (lem-weil-pbc-noetherian-normal-separable-integral-closure-finite), with finitely many
   maximal branches, each a DVR (lem-sfb-dvr-algebraic-normalization-structure). Take
   `m` to be the product of their indices; it is positive and prime to `p`.
2. In an algebraic closure of `T` (lem-pc-algebraic-closure-exists-unique), choose a root
   of `X^m - pi`. The Bezout identity with its derivative proves separability
   (def-pc-separable-polynomial and def-weil-pbc-separable-algebraic-extension).
3. Put `T' = T(a)`. Generated scalar extension preserves separability
   (lem-sfb-separable-generated-scalar-extension), and separability is transitive
   (lem-zl-separable-permanence). The products of a basis of `T/F` and
   `1,a,...,a^(m-1)` span `T'/F`, so this extension is finite. Restriction to the
   intermediate base preserves separability (lem-sfb-separable-algebraic-intermediate-base).
4. The root algebra is a DVR with root uniformizer
   (lem-sbc-dvr-uniformizer-root-algebra). Evaluation identifies it with `R[a]`:
   a nonzero prime kernel would contain the uniformizer and hence `pi`, contradicting
   injectivity on `R`. Its fraction field is `F(a)`, and reduction modulo the root
   identifies its residue field canonically with that of `R`. This includes `m = 1`.
5. Normalize `R[a]` in `T'`. Finiteness of normalization and contraction of maximal
   ideals (lem-weil-pbc-integral-maximal-contracts-maximal) give finite residue extensions.
6. For each maximal branch apply lem-sbc-dvr-normalized-compositum-local-diagram.
   Primes above the base maximal ideal are maximal
   (lem-weil-pbc-integral-prime-over-maximal-maximal), so all its tame hypotheses hold.
7. The base index is `m`, divisible by each original index, which is a unit in `R`.
   Apply lem-sbc-dvr-abhyankar-local-maximal-ideal and lem-sbc-dvr-abhyankar-local-residue.
   These give the maximal-ideal equality and residue separability. The residue field
   of a maximal localization is canonically the quotient by that maximal ideal;
   transport through the constant residue identification from step 4 completes the claim.
-/
theorem tame_extension_uniformizer_root_domination
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (F : Type v) [Field F] [Algebra R F] [IsFractionRing R F]
    (p : ℕ) (hp : p.Prime) [CharP (IsLocalRing.ResidueField R) p]
    (pi : R) (hpi : Irreducible pi)
    (T : Type w) [Field T] [Algebra F T] [Algebra R T] [IsScalarTower R F T]
    [FiniteDimensional F T] [Algebra.IsSeparable F T]
    (htame : ∀ (n : Ideal (integralClosure R T)) [n.IsMaximal],
      ∃ e : ℕ, ¬ p ∣ e ∧
        (IsLocalRing.maximalIdeal R).map
            (algebraMap R (Localization.AtPrime n)) =
          IsLocalRing.maximalIdeal (Localization.AtPrime n) ^ e ∧
        ∃ (_ : Algebra (IsLocalRing.ResidueField R) ((integralClosure R T) ⧸ n)),
          IsScalarTower R (IsLocalRing.ResidueField R) ((integralClosure R T) ⧸ n) ∧
          FiniteDimensional (IsLocalRing.ResidueField R) ((integralClosure R T) ⧸ n) ∧
          Algebra.IsSeparable (IsLocalRing.ResidueField R) ((integralClosure R T) ⧸ n)) :
    ∃ m : ℕ, 0 < m ∧ ¬ p ∣ m ∧
      ∃ (T' : Type (max u v w)) (_ : Field T') (_ : Algebra F T')
        (_ : Algebra R T') (_ : IsScalarTower R F T')
        (_ : FiniteDimensional F T') (_ : Algebra.IsSeparable F T')
        (_ : T →ₐ[F] T') (a : T'),
        a ^ m = algebraMap R T' pi ∧
        ∃ K : IntermediateField F T', K = IntermediateField.adjoin F {a} ∧
          ∃ aK : K, (aK : T') = a ∧
            ∃ A : Subalgebra R K, A = Algebra.adjoin R {aK} ∧
              ∃ (_ : IsDiscreteValuationRing A),
                IsFractionRing A K ∧
                (∃ aA : A, (aA : K) = aK ∧
                  IsLocalRing.maximalIdeal A = Ideal.span {aA}) ∧
                Nonempty (IsLocalRing.ResidueField R ≃ₐ[R] IsLocalRing.ResidueField A) ∧
                ∀ (h : Ideal (integralClosure A T')) [h.IsMaximal],
                  (IsLocalRing.maximalIdeal A).map
                      (algebraMap A (Localization.AtPrime h)) =
                    IsLocalRing.maximalIdeal (Localization.AtPrime h) ∧
                  ∃ (_ : Algebra (IsLocalRing.ResidueField R) ((integralClosure A T') ⧸ h)),
                    (∀ r : R,
                      algebraMap (IsLocalRing.ResidueField R)
                        ((integralClosure A T') ⧸ h) (IsLocalRing.residue R r) =
                      algebraMap A ((integralClosure A T') ⧸ h) (algebraMap R A r)) ∧
                    FiniteDimensional (IsLocalRing.ResidueField R)
                      ((integralClosure A T') ⧸ h) ∧
                    Algebra.IsSeparable (IsLocalRing.ResidueField R)
                      ((integralClosure A T') ⧸ h) := by
  sorry

end RingTheory
