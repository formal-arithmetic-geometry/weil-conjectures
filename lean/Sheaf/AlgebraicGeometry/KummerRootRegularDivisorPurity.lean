/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q65
-/
module

public import Sheaf.AlgebraicGeometry.PunctualPurity
public import Sheaf.AlgebraicGeometry.IndEtaleClosedSupportBaseChange
public import Sheaf.AlgebraicGeometry.IsRegularScheme
public import Sheaf.AlgebraicGeometry.RegularImmersionClassCalculus
public import Sheaf.AlgebraicGeometry.EtaleFiniteTwistPullback
public import Sheaf.AlgebraicGeometry.OrdinarySupportedCartierKummer
public import Sheaf.AlgebraicGeometry.StalkRegularClosedImmersion
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence
public import WeilConjectures.SixFunctors.Finite.Exact
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusExact
public import WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
import WeilConjectures.RepresentationTheory.DiscreteContinuousRep
import Mathlib.RingTheory.RingHom.Flat
import Sheaf.RepresentationTheory.ProcyclicTwoTerm
import WeilConjectures.AlgebraicGeometry.Morphisms.EtaleRegularDivisorBaseChange
import WeilConjectures.RingTheory.RootAlgebraRegularAtRoot
import Sheaf.AlgebraicGeometry.Morphisms.RootSplitAwayCoverEtale
import Sheaf.AlgebraicGeometry.Morphisms.StrictHenselRegularDivisorQuotient
import WeilConjectures.RingTheory.StrictHenselizationFaithfullyFlat
import WeilConjectures.RingTheory.StrictHenselizationRegular
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle
import Sheaf.TraceFormula.FiniteBaseStrictLocalization
import Mathlib.RingTheory.Noetherian.Basic
import Sheaf.AlgebraicGeometry.FiniteFreeAlgebraSpectrum

/-!
# Kummer-root invariance of regular divisor purity

Source: ILO, Exposé XVI, Proposition 3.4.5 and Lemmas 3.4.6--3.4.9, pp.246--248
(blueprint: lem-per-kummer-root-regular-divisor-purity).

The class map and the introductory punctual-purity terminology are the published
`punctualPurityClassMap`, `IsPunctuallyPureAt` and `IsPunctuallyPure`. The theorem concerns
divisor purity, with no assumption of punctual purity on the ambient scheme.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

/-- The actual monic root algebra B[U]/(U^ell-f).
Source: ILO XVI 3.4.5 (blueprint: lem-per-kummer-root-regular-divisor-purity). -/
abbrev divisorRootAlgebra (B : CommRingCat.{u}) (ℓ : ℕ) (f : B) :=
  AdjoinRoot ((Polynomial.X : Polynomial B) ^ ℓ - Polynomial.C f)

/-- The spectrum of the monic root algebra.
Source: ILO XVI 3.4.5 (blueprint: lem-per-kummer-root-regular-divisor-purity). -/
abbrev divisorRootScheme (B : CommRingCat.{u}) (ℓ : ℕ) (f : B) : Scheme.{u} :=
  Spec (.of (divisorRootAlgebra B ℓ f))

/-- The root coordinate U, the class of the polynomial indeterminate.
Source: ILO XVI 3.4.5 (blueprint: lem-per-kummer-root-regular-divisor-purity). -/
abbrev divisorRootCoordinate (B : CommRingCat.{u}) (ℓ : ℕ) (f : B) :
    divisorRootAlgebra B ℓ f :=
  AdjoinRoot.root _

/-- The projection induced by the constants B -> B[U]/(U^ell-f).
Source: ILO XVI 3.4.5 (blueprint: lem-per-kummer-root-regular-divisor-purity). -/
def divisorRootProjection (B : CommRingCat.{u}) (ℓ : ℕ) (f : B) :
    divisorRootScheme B ℓ f ⟶ Spec B :=
  Spec.map (CommRingCat.ofHom (algebraMap B (divisorRootAlgebra B ℓ f)))

/-- The closed subscheme D'=V(U), with its quotient scheme structure.
Source: ILO XVI 3.4.5 (blueprint: lem-per-kummer-root-regular-divisor-purity). -/
abbrev divisorRootDivisor (B : CommRingCat.{u}) (ℓ : ℕ) (f : B) : Scheme.{u} :=
  Spec (.of (divisorRootAlgebra B ℓ f ⧸ Ideal.span {divisorRootCoordinate B ℓ f}))

/-- The closed inclusion D' -> X', induced by the quotient by U.
Source: ILO XVI 3.4.5 (blueprint: lem-per-kummer-root-regular-divisor-purity). -/
def divisorRootDivisorInclusion (B : CommRingCat.{u}) (ℓ : ℕ) (f : B) :
    divisorRootDivisor B ℓ f ⟶ divisorRootScheme B ℓ f :=
  Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {divisorRootCoordinate B ℓ f})))

/-- Adjoining an ell-th root preserves regular-divisor purity, with its geometric assertions.
The Noetherian, regular-immersion and invertibility witnesses in the conclusion only make
the already published class map evaluable; none is an additional hypothesis.
The complement map is the canonical restriction of the projection, and its domain is
identified with D(U), so it is precisely X' minus D'. Empty divisors are included.

Source: ILO XVI Proposition 3.4.5 and Lemmas 3.4.6--3.4.9, pp.246--248
(blueprint: lem-per-kummer-root-regular-divisor-purity).

Proof:
1. The monic power basis (lem-weil-pbc-monic-quotient-free) gives rank ell, finite local
   freeness (lem-weil-pbc-finite-free-algebra-spectrum) and Noetherianity
   (lem-weil-pbc-finite-algebra-noetherian). Multiplication by f is injective coefficientwise;
   U^ell=f makes multiplication by U injective. Evaluation at U=0 identifies C/(U)=B/(f).
   Every residue-field polynomial T^ell-f has a root in an algebraic closure, giving
   surjectivity, including on the complements. This covers zero rings and unit f.
2. Along U=0 apply lem-sbc-root-algebra-regular-at-root. Off U=0 use
   lem-sbc-root-split-away-cover-etale and lem-sbc-etale-regular-divisor-base-change with
   auxiliary element 1. Thus X' and its effective Cartier divisor D' are regular.
3. At a geometric point of D pass to the strict local ring. Use
   lem-sc-strict-henselization-regular, lem-sbc-strict-hensel-regular-divisor-quotient and
   lem-sc-strict-henselization-faithfully-flat (def-weil-pbc-flat-ring-map preserves the
   injection by f). The fibre Omega[U]/(U^ell) has one geometric point, so
   lem-trf-finite-base-strict-localization identifies the base-changed pair with the
   strict localization of the root pair.
4. Apply lem-per-kummer-classifying-purity-criterion and lem-exc-procyclic-two-term:
   the classifying comparison is invertible exactly when all complement cohomology
   groups in degrees at least two vanish. This holds for both strict local pairs.
5. The tower square and lem-per-kummer-relative-cone-functor give a triangulated
   relative functor F. Original purity tests F(A)=0 and root purity tests F(M)=0,
   where M is the direct image Map(G/ell G,A), not the inverse image of A.
6. With z=sigma-1, M=A[z]/(z^ell). The quotients M_i=A[z]/(z^i) give equivariant
   exact sequences 0 -> A -> M_i -> M_(i-1) -> 0, with M_0=0.
7. Apply lem-sf-derived-ses-triangle and lem-sf-derived-homology-long-exact. If F(A)=0,
   induction gives F(M)=0. Otherwise choose its first nonzero cohomology degree n;
   induction gives vanishing below n for F(M_i), and H^n F(A) injects into H^n F(M_i).
   Thus F(M) is nonzero. This proves equivalence of the two local tests.
8. Apply lem-per-divisor-purity-strict-local-criterion at all corresponding geometric
   points of D'=D to get the global equivalence. On an empty divisor both maps are
   isomorphisms in the zero sheaf category.
-/
theorem kummer_root_regular_divisor_purity
    (ℓ : ℕ) (hℓ : ℓ.Prime) (B : CommRingCat.{u}) [IsNoetherianRing B]
    (hB : IsRegularScheme (Spec B)) (hInv : IsUnit (ℓ : B))
    (f : B) (hf : IsSMulRegular B f)
    (hD : IsRegularScheme (Spec (.of (B ⧸ Ideal.span {f})))) :
    ∃ (_hN : IsNoetherian (divisorRootScheme B ℓ f))
      (_hND : IsNoetherian (divisorRootDivisor B ℓ f))
      (_hi' : IsClosedImmersion (divisorRootDivisorInclusion B ℓ f)),
      IsRegularScheme (divisorRootScheme B ℓ f) ∧
      IsRegularScheme (divisorRootDivisor B ℓ f) ∧
      IsSMulRegular (divisorRootAlgebra B ℓ f) (divisorRootCoordinate B ℓ f) ∧
      (divisorRootDivisorInclusion B ℓ f).ker.IsInvertible ∧
      (∃ e : divisorRootDivisor B ℓ f ≅ Spec (.of (B ⧸ Ideal.span {f})),
        e.hom ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {f}))) =
          divisorRootDivisorInclusion B ℓ f ≫ divisorRootProjection B ℓ f) ∧
      (∃ (hi : IsStalkRegularClosedImmersion
          (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {f})))) 1)
        (hi' : IsStalkRegularClosedImmersion (divisorRootDivisorInclusion B ℓ f) 1)
        (hX : IsUnit ((ℓ ^ 1 : ℕ) : Γ(Spec B, ⊤)))
        (hX' : IsUnit ((ℓ ^ 1 : ℕ) : Γ(divisorRootScheme B ℓ f, ⊤))),
        IsIso (punctualPurityClassMap ℓ hℓ
          (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {f})))) 1 hi hX) ↔
        IsIso (punctualPurityClassMap ℓ hℓ (divisorRootDivisorInclusion B ℓ f) 1 hi' hX')) ∧
      (divisorRootProjection B ℓ f).IsFiniteLocallyFreeOfDegree ℓ ∧
      Surjective (divisorRootProjection B ℓ f) ∧
      (divisorRootProjection B ℓ f ⁻¹ᵁ PrimeSpectrum.basicOpen f =
        PrimeSpectrum.basicOpen (divisorRootCoordinate B ℓ f)) ∧
      Surjective (morphismRestrict (divisorRootProjection B ℓ f) (PrimeSpectrum.basicOpen f)) ∧
      Etale (morphismRestrict (divisorRootProjection B ℓ f) (PrimeSpectrum.basicOpen f)) := by
  sorry

end AlgebraicGeometry.Etale
