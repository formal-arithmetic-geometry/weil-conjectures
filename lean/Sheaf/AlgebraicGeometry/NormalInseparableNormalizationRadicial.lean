/-
Copyright (c) 2026 The SHEAF project authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import WeilConjectures.Mathlib.AlgebraicGeometry.Normalization
public import WeilConjectures.AlgebraicGeometry.BaseChangeConventions
public import WeilConjectures.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyInjective
public import Mathlib.FieldTheory.PurelyInseparable.Basic
import WeilConjectures.AlgebraicGeometry.HomeomorphPurelyInseparableBaseChange
import Sheaf.AlgebraicGeometry.ReducedNormalization
import Mathlib.RingTheory.LocalProperties.IntegrallyClosed
import Mathlib.RingTheory.Algebraic.Integral

/-!
# Uniform Frobenius bounds for normalized inseparable base change

Source: Stacks Project, varieties.tex, Tag 0C3N, lemma-normalization-and-change-of-fields,
and algebra.tex, Tag 0BRA, lemma-p-ring-map
(blueprint: lem-sfb-normal-inseparable-normalization-radicial).
-/

@[expose] public section
set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace AlgebraicGeometry

noncomputable section

variable (k l : Type u) [Field k] [Field l] [Algebra k l]

/-- The reduction of the specified field base change; this abbreviates the existing reduction.
Source: Stacks 0C3N (blueprint: lem-sfb-normal-inseparable-normalization-radicial). -/
abbrev inseparableBaseChangeReduction (S : Scheme.{u}) (pS : S ⟶ Spec (.of k)) : Scheme.{u} :=
  (pullback pS (Spec.map (CommRingCat.ofHom (algebraMap k l)))).nilradical.subscheme

/-- The canonical normalization--reduction--projection composite, with no chosen extra map.
Source: Stacks 0C3N (blueprint: lem-sfb-normal-inseparable-normalization-radicial). -/
abbrev normalInseparableProjection (S : Scheme.{u}) (pS : S ⟶ Spec (.of k))
    [IsIntegral (inseparableBaseChangeReduction k l S pS)] :
    (inseparableBaseChangeReduction k l S pS).normalization ⟶ S :=
  (inseparableBaseChangeReduction k l S pS).fromNormalization ≫
    (pullback pS (Spec.map (CommRingCat.ofHom (algebraMap k l)))).nilradical.subschemeι ≫
    pullback.fst pS (Spec.map (CommRingCat.ofHom (algebraMap k l)))

variable (C : Type u) [CommRing C] [Algebra k C]

/-- The affine ring R = (C tensor_k l)_red, using the actual nilradical quotient.
Source: Stacks 0C3N (blueprint: lem-sfb-normal-inseparable-normalization-radicial). -/
abbrev inseparableAffineReduction : CommRingCat.{u} :=
  .of ((C ⊗[k] l) ⧸ nilradical (C ⊗[k] l))

/-- The integral closure D of R in its fraction ring, not an arbitrary finite algebra.
Source: Stacks 0C3N (blueprint: lem-sfb-normal-inseparable-normalization-radicial). -/
abbrev inseparableAffineNormalization : CommRingCat.{u} :=
  .of (integralClosure (inseparableAffineReduction k l C)
    (FractionRing (inseparableAffineReduction k l C)))

/-- The canonical tensor inclusion followed by reduction, C to R.
Source: Stacks 0C3N (blueprint: lem-sfb-normal-inseparable-normalization-radicial). -/
def toInseparableAffineReduction : C →+* inseparableAffineReduction k l C :=
  (Ideal.Quotient.mk (nilradical (C ⊗[k] l))).comp
    (Algebra.TensorProduct.includeLeft : C →ₐ[k] C ⊗[k] l).toRingHom

/-- The canonical map C to D through R and its integral closure in Frac R.
Source: Stacks 0C3N (blueprint: lem-sfb-normal-inseparable-normalization-radicial). -/
def toInseparableAffineNormalization : C →+* inseparableAffineNormalization k l C :=
  (algebraMap (inseparableAffineReduction k l C)
    (integralClosure (inseparableAffineReduction k l C)
      (FractionRing (inseparableAffineReduction k l C)))).comp
    (toInseparableAffineReduction k l C)

/-- Normalized finite purely inseparable base change of a normal integral finite-type scheme
is finite, surjective and radicial, with the same prescribed uniform Frobenius bound on all
normalization charts, residue fields and function fields.

Source: Stacks 0C3N, proof, and 0BRA, proof
(blueprint: lem-sfb-normal-inseparable-normalization-radicial).

Proof (the node's ten steps).
1. A finite k-basis of l and the maximum of its inseparability exponents give a uniform N.
Fix any N satisfying the statement, without increasing it.
2. The rings C of nonempty affine opens are domains by integrality. Their localizations are
normal local rings of S (lem-weil-pbc-affine-open-stalk-localization), so C is integrally
closed by lem-weil-pbc-normal-domain-of-local-normal.
3. Purely inseparable base change is a homeomorphism (lem-pc-homeo-pure-insep). Reduction
preserves its space, so T is integral. Its affine tensor quotients are finite type over l,
hence it is locally Noetherian (lem-weil-pbc-finite-type-over-noetherian).
4. A k-linear retraction l to k taking 1 to 1 proves C to C tensor l injective. The domain
property preserves injectivity on reduction. Frobenius gives r^(p^N) in C for all r in R,
and a basis of l proves R finite over C.
5. Normalization is finite and surjective (lem-sc-normalization-exists). Its affine charts
are Spec D (lem-sfb-normalization-affine-total-fractions); the one-component reduced
normalization agrees with Scheme.normalization. Finiteness of D over R and of R over C
makes D finite over C (def-weil-finite-integral-morphism).
6. These domain charts cover B, and any two intersect by surjectivity over integral T.
Thus B is integral, C to D is injective, and Frac D = Frac R.
7. For x=a/b in Frac R, x^(p^N) belongs to Frac C. Raise a monic integral equation for d
in D to p^N: d^(p^N) is integral over C, hence belongs to C by its normality.
8. The ring homomorphism d to d^(p^N) pulls each prime P of C back to the displayed unique
prime of D. Primality implies its contraction is P and proves uniqueness. Taking fractions
modulo these primes proves the same exponent bound for residues. This gives surjectivity
and radiciality (def-weil-radicial-morphism).
9. Identify function fields with the affine fraction fields
(lem-sc-integral-function-field-affine-fraction). The finite injective map C to D gives a
finite field extension (lem-trf-finite-domain-fraction-degree); step 7 makes it purely
inseparable with the prescribed exponent (def-weil-pbc-finite-purely-inseparable-extension).
10. In characteristic zero l=k. All affine C are normal, so reduction and normalization
are identities (lem-sfb-normalization-affine-total-fractions); their inverses glue to q's
inverse. The other assertions reduce to the identity extension.
-/
theorem normal_inseparable_normalization_radicial
    [Module.Finite k l] [IsPurelyInseparable k l]
    (S : Scheme.{u}) (pS : S ⟶ Spec (.of k)) [IsIntegral S]
    [LocallyOfFiniteType pS] [QuasiCompact pS]
    (hnormal : ∀ s : S, IsDomain (S.presheaf.stalk s) ∧
      IsIntegrallyClosed (S.presheaf.stalk s)) :
    ∃ (_ : IsIntegral (inseparableBaseChangeReduction k l S pS)),
      ∃ (_ : IsIntegral (inseparableBaseChangeReduction k l S pS).normalization),
        IsFinite (normalInseparableProjection k l S pS) ∧
        Surjective (normalInseparableProjection k l S pS) ∧
        UniversallyInjective (normalInseparableProjection k l S pS) ∧
        (∃ (hq : normalInseparableProjection k l S pS
              (genericPoint (inseparableBaseChangeReduction k l S pS).normalization) =
            genericPoint S)
            (_ : Algebra S.functionField
              (inseparableBaseChangeReduction k l S pS).normalization.functionField),
          algebraMap S.functionField
              (inseparableBaseChangeReduction k l S pS).normalization.functionField =
            (S.presheaf.stalkSpecializes (specializes_of_eq hq) ≫
              (normalInseparableProjection k l S pS).stalkMap
                (genericPoint (inseparableBaseChangeReduction k l S pS).normalization)).hom ∧
          Module.Finite S.functionField
            (inseparableBaseChangeReduction k l S pS).normalization.functionField ∧
          IsPurelyInseparable S.functionField
            (inseparableBaseChangeReduction k l S pS).normalization.functionField ∧
          (∀ (p : ℕ) [CharP k p], p.Prime →
            (∃ N : ℕ, ∀ a : l, a ^ (p ^ N) ∈ Set.range (algebraMap k l)) ∧
            ∀ (N : ℕ), (∀ a : l, a ^ (p ^ N) ∈ Set.range (algebraMap k l)) →
              (∀ z : (inseparableBaseChangeReduction k l S pS).normalization.functionField,
                z ^ (p ^ N) ∈ Set.range (algebraMap S.functionField
                  (inseparableBaseChangeReduction k l S pS).normalization.functionField)) ∧
              (∀ b : (inseparableBaseChangeReduction k l S pS).normalization,
                ∀ z : (inseparableBaseChangeReduction k l S pS).normalization.residueField b,
                  z ^ (p ^ N) ∈ Set.range
                    ((normalInseparableProjection k l S pS).residueFieldMap b).hom) ∧
              (∀ (U : S.Opens) (hU : IsAffineOpen U), Nonempty U →
                ∀ (C : Type u) [CommRing C] [Algebra k C]
                  (e : Spec (.of C) ≅ U.toScheme),
                  e.hom ≫ U.ι ≫ pS = Spec.map (CommRingCat.ofHom (algebraMap k C)) →
                  (∃ j : ((normalInseparableProjection k l S pS) ⁻¹ᵁ U).toScheme ≅
                      Spec (inseparableAffineNormalization k l C),
                    j.hom ≫ Spec.map (CommRingCat.ofHom
                        (toInseparableAffineNormalization k l C)) ≫ e.hom ≫ U.ι =
                      ((normalInseparableProjection k l S pS) ⁻¹ᵁ U).ι ≫
                        normalInseparableProjection k l S pS) ∧
                  Function.Injective (toInseparableAffineNormalization k l C) ∧
                  (toInseparableAffineNormalization k l C).Finite ∧
                  (∀ d : inseparableAffineNormalization k l C,
                    d ^ (p ^ N) ∈ Set.range (toInseparableAffineNormalization k l C)) ∧
                  ∀ P : PrimeSpectrum C,
                    ∃ J : PrimeSpectrum (inseparableAffineNormalization k l C),
                      Ideal.comap (toInseparableAffineNormalization k l C) J.asIdeal = P.asIdeal ∧
                      (∀ J' : PrimeSpectrum (inseparableAffineNormalization k l C),
                        Ideal.comap (toInseparableAffineNormalization k l C) J'.asIdeal =
                          P.asIdeal → J' = J) ∧
                      ∀ d : inseparableAffineNormalization k l C,
                        d ∈ J.asIdeal ↔ ∃ c : C, c ∈ P.asIdeal ∧
                          toInseparableAffineNormalization k l C c = d ^ (p ^ N)))) ∧
        (∀ [CharZero k], Function.Surjective (algebraMap k l) ∧
          IsIso (normalInseparableProjection k l S pS)) := by
  sorry

end
end AlgebraicGeometry
