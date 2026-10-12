/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group T2
-/
module

public import Sheaf.RingTheory.SingularIdeal
public import Mathlib.Algebra.MvPolynomial.CommRing
public import Mathlib.RingTheory.Ideal.Cotangent
public import Mathlib.Algebra.Module.LocalizedModule.Basic
public import Mathlib.RingTheory.Kaehler.Basic
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.RingTheory.FinitePresentation
public import Mathlib.Algebra.Algebra.Equiv
import Sheaf.RingTheory.SmoothAtPrimeFreeConormalBasis
import Mathlib.RingTheory.Finiteness.Nakayama

/-! # Prepared polynomial data for Popescu lifting

Source: Stacks Project, Tag 07CP, preparation (1)--(4).
(blueprint: lem-weil-pbc-popescu-lift-preparation).
-/

@[expose] public section

noncomputable section

universe a c

namespace Algebra

/-- Finite polynomial data; no algebra is chosen from an existence theorem. -/
structure PopescuLiftPresentation (R : Type a) (Cbar : Type c)
    [CommRing R] [CommRing Cbar] (π : R)
    [Algebra (R ⧸ Ideal.span ({π ^ 2} : Set R)) Cbar] where
  n : ℕ
  m : ℕ
  r : ℕ
  f : Fin m → MvPolynomial (Fin n) R
  a : Fin r → MvPolynomial (Fin n) R
  E : Fin r → Finset (Fin m)
  h : Fin r → Fin m → Fin m → MvPolynomial (Fin n) R
  g : Fin r → Fin m → MvPolynomial (Fin n) R
  ε : MvPolynomial (Fin n) (R ⧸ Ideal.span ({π ^ 2} : Set R)) →ₐ[
    R ⧸ Ideal.span ({π ^ 2} : Set R)] Cbar

namespace PopescuLiftPresentation

variable {R : Type a} {Cbar : Type c} [CommRing R] [CommRing Cbar] {π : R}
    [Algebra (R ⧸ Ideal.span ({π ^ 2} : Set R)) Cbar]

abbrev reduced (d : PopescuLiftPresentation R Cbar π) (u : MvPolynomial (Fin d.n) R) :=
  MvPolynomial.map (Ideal.Quotient.mk (Ideal.span ({π ^ 2} : Set R))) u

abbrev reducedIdeal (d : PopescuLiftPresentation R Cbar π) :=
  Ideal.span (Set.range (fun j ↦ d.reduced (d.f j)))

abbrev reducedQuotient (d : PopescuLiftPresentation R Cbar π) :=
  MvPolynomial (Fin d.n) (R ⧸ Ideal.span ({π ^ 2} : Set R)) ⧸ d.reducedIdeal

abbrev reducedElement (d : PopescuLiftPresentation R Cbar π) (k : Fin d.r) :=
  Ideal.Quotient.mk d.reducedIdeal (d.reduced (d.a k))

/-- The presentation, cover, conormal bases and cleared relations of (1)--(4). -/
structure Prepared [Algebra R Cbar]
    (d : PopescuLiftPresentation R Cbar π) : Prop where
  surjective : Function.Surjective d.ε
  kernel : RingHom.ker d.ε.toRingHom = d.reducedIdeal
  cover : ∀ q : PrimeSpectrum Cbar,
    IsSmoothAtPrime (R ⧸ Ideal.span ({π ^ 2} : Set R)) q →
    ∃ k : Fin d.r, d.ε (d.reduced (d.a k)) ∉ q.asIdeal
  smooth : ∀ k : Fin d.r,
    Smooth (R ⧸ Ideal.span ({π ^ 2} : Set R)) (Localization.Away (d.reducedElement k))
  card_le : ∀ k : Fin d.r, (d.E k).card ≤ d.n
  conormal : ∀ k : Fin d.r,
    ∃ b : Module.Basis (d.E k) (Localization.Away (d.reducedElement k))
        (LocalizedModule.Away (d.reducedElement k) d.reducedIdeal.Cotangent),
      ∀ j : d.E k, b j =
        LocalizedModule.mkLinearMap (Submonoid.powers (d.reducedElement k))
          d.reducedIdeal.Cotangent
          (d.reducedIdeal.toCotangent ⟨d.reduced (d.f j),
            Ideal.subset_span ⟨j, rfl⟩⟩)
  differentials : ∀ k : Fin d.r,
    Nonempty (Module.Basis (Fin (d.n - (d.E k).card))
      (Localization.Away (d.reducedElement k))
      (KaehlerDifferential (R ⧸ Ideal.span ({π ^ 2} : Set R))
        (Localization.Away (d.reducedElement k))))
  relation : ∀ (k : Fin d.r) (l : Fin d.m),
    d.a k * d.f l = ∑ j ∈ d.E k, d.h k l j * d.f j +
      MvPolynomial.C (π ^ 2) * d.g k l
  normalized_h : ∀ (k : Fin d.r) (l : Fin d.m), l ∈ d.E k →
    ∀ j : Fin d.m, d.h k l j = if l = j then d.a k else 0
  normalized_g : ∀ (k : Fin d.r) (l : Fin d.m), l ∈ d.E k → d.g k l = 0

abbrev polynomial (d : PopescuLiftPresentation R Cbar π) :=
  MvPolynomial (Fin d.n ⊕ Fin d.m) R

/-- The inclusion of the original polynomial variables. -/
def includeX (d : PopescuLiftPresentation R Cbar π) :
    MvPolynomial (Fin d.n) R →ₐ[R] d.polynomial :=
  MvPolynomial.rename Sum.inl

/-- The equations defining the lifting algebra, with original and auxiliary variables. -/
def equation (d : PopescuLiftPresentation R Cbar π) :
    Fin d.m ⊕ (Fin d.r × Fin d.m) → d.polynomial
  | .inl j => d.includeX (d.f j) - MvPolynomial.C π * MvPolynomial.X (.inr j)
  | .inr (k, l) => d.includeX (d.a k) * MvPolynomial.X (.inr l) -
      (∑ j ∈ d.E k, d.includeX (d.h k l j) * MvPolynomial.X (.inr j)) -
      MvPolynomial.C π * d.includeX (d.g k l)

abbrev definingIdeal (d : PopescuLiftPresentation R Cbar π) :=
  Ideal.span (Set.range d.equation)

/-- Explicit quotient; `ULift` gives the universe required by the original theorem. -/
abbrev liftingAlgebra (d : PopescuLiftPresentation R Cbar π) :=
  ULift.{c} (d.polynomial ⧸ d.definingIdeal)

/-- Original generators in the explicitly constructed lifting algebra. -/
def x (d : PopescuLiftPresentation R Cbar π) (i : Fin d.n) : d.liftingAlgebra :=
  ULift.up (Ideal.Quotient.mk d.definingIdeal (MvPolynomial.X (.inl i)))

/-- The displayed quotient has finitely many variables and finitely many equations. -/
theorem finitePresentation (d : PopescuLiftPresentation R Cbar π) :
    FinitePresentation R d.liftingAlgebra := by
  let : FinitePresentation R (d.polynomial ⧸ d.definingIdeal) :=
    FinitePresentation.quotient (Submodule.fg_span (Set.finite_range d.equation))
  exact FinitePresentation.equiv (ULift.algEquiv (R := R)).symm

end PopescuLiftPresentation

/-- Prepare the finite presentation and smooth charts used in the lifting construction.

Source: Stacks Project, Tag 07CP, proof through equations (1)--(4); Tag 07C6.
(blueprint: lem-weil-pbc-popescu-lift-preparation).

Proof: Choose a finite polynomial presentation over R/π² and lift its finitely many
relations to R[x]. Let ε be its surjective presentation map. The quotient Cbar is
Noetherian, since it is finite type over the Noetherian quotient R/π². At each smooth
prime apply Tag 07C6 to select a principal neighbourhood, a subset E of the given
relations forming a conormal basis, and a differential basis of complementary rank.
Select finitely many such neighbourhoods covering the smooth locus using Noetherianity.
For each chart, the selected relations generate I/I² after localization. Nakayama
applied to I/I_E gives an annihilator 1+b/a^N with b in I. Replace a by a(a^N+b);
in Cbar its image is a power of the old image, so the cover and bases persist, while
I and I_E now agree after localization. Clear denominators in the expressions for
all f_l in I_E modulo π², replacing a by a common positive power. Lift the coefficients
and the π² remainders to R[x]. For l in E choose h_{klj}=a_k δ_{lj} and g_{kl}=0.
These choices satisfy the displayed relations exactly and preserve every chart condition.
-/
theorem exists_popescu_lift_preparation (R : Type a) (Cbar : Type c)
    [CommRing R] [CommRing Cbar] [Algebra R Cbar] [IsNoetherianRing R] (π : R)
    [Algebra (R ⧸ Ideal.span ({π ^ 2} : Set R)) Cbar]
    [IsScalarTower R (R ⧸ Ideal.span ({π ^ 2} : Set R)) Cbar]
    [FinitePresentation (R ⧸ Ideal.span ({π ^ 2} : Set R)) Cbar] :
    ∃ d : PopescuLiftPresentation R Cbar π, d.Prepared := by sorry

end Algebra
