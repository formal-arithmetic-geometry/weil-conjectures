/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module

public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.FinitePresentation
public import Mathlib.RingTheory.FiniteStability
public import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
public import Mathlib.AlgebraicGeometry.ResidueField
public import WeilConjectures.RingTheory.CompleteIntersectionOverField
import WeilConjectures.RingTheory.SymmetricProjectivePresentationConormal
import WeilConjectures.RingTheory.SymmetricAlgebraSmooth
import WeilConjectures.RingTheory.RelativeGlobalCompleteIntersectionFlat
import WeilConjectures.AlgebraicGeometry.RelativeGlobalCompleteIntersectionPresentation
import WeilConjectures.AlgebraicGeometry.LiftProjectiveModuleEtale
import WeilConjectures.RingTheory.SymmetricAlgebraBaseChange
import Mathlib.LinearAlgebra.SymmetricAlgebra.Basic

/-!
# Lifting syntomic algebras along surjections

Source: Stacks Project, Smoothing Ring Maps, Tag 07M8, assertion (1), with
Algebra, Tags 00SL and 00S9 (blueprint: lem-sfb-syntomic-algebra-surjection-lift).
-/

@[expose] public section

universe u v w

open scoped TensorProduct

namespace Algebra

/-- A syntomic algebra lifts along any surjection of commutative rings.
Source: Stacks Project, Smoothing Ring Maps, Tag 07M8, assertion (1).
(blueprint: lem-sfb-syntomic-algebra-surjection-lift).

Syntomic means flat, finitely presented, with local complete intersection fibres
(Algebra, Tag 00SL). The zero algebra is allowed (Tag 00S9). The equation for `β`
expresses compatibility with the unique R₀-algebra structure on the quotient
induced by the surjection π; it is exactly an R₀-algebra isomorphism.

Proof: if B₀ is zero take B zero. Otherwise choose a finite polynomial presentation
of B₀. Its conormal P₀ is finite projective by
lem-sfb-syntomic-presentation-conormal-fibre-rank. Enlarge to C₀ = Sym(P₀).
The symmetric-projective-presentation-conormal and symmetric-algebra-finite-projective-smooth
lemmas give a smooth enlargement with free conormal; syntomic-smooth-composition
preserves syntomicity. The conormal-free-presentation-basis lemma supplies equations
forming a conormal basis. Their fibre dimensions are the number of variables minus
that of equations, by the conormal-fibre-rank lemma. Lift the coefficients to R and
use lem-sfb-equation-count-closed-fibre-localization to obtain a relative global
complete intersection C reducing to C₀. The relative-global-complete-intersection-flat
lemma gives flatness. The presentation gives finite presentation, and
presentation-base-change with the relative-global-complete-intersection definition
gives global complete intersection fibres, hence local complete intersection fibres.
Choose a finite projective complement Q₀ to P₀. Lift Q₀ tensor C₀ after an etale
extension C → C′ using lift-projective-module-etale, and put D = Sym over C′ of
that lift. Smoothness and syntomic-smooth-composition make D syntomic over R.
Symmetric-algebra-base-change and its universal property identify D/ID with a
polynomial algebra B₀[x₁,...,xᵣ]. Lift the variables and quotient by their lifts.
The syntomic-polynomial-fibre-cut lemma gives a principal localization B syntomic
over R, with the localizing element reducing to 1. Reduction therefore remains B₀.
The reduction map on fractions and the map sending a residue class to its image
with denominator 1 are inverse and preserve scalars, giving β. -/
theorem exists_syntomic_algebra_lift_of_surjective
    {R : Type u} {R₀ : Type v} [CommRing R] [CommRing R₀]
    (π : R →+* R₀) (hπ : Function.Surjective π)
    (B₀ : Type w) [CommRing B₀] [Algebra R₀ B₀]
    [Module.Flat R₀ B₀] [Algebra.FinitePresentation R₀ B₀]
    (hci₀ : ∀ p : PrimeSpectrum R₀,
      IsLocalCompleteIntersection p.asIdeal.ResidueField
        (p.asIdeal.ResidueField ⊗[R₀] B₀)) :
    ∃ (B : Type u) (_ : CommRing B) (_ : Algebra R B)
      (_ : Algebra.FinitePresentation R B),
      Module.Flat R B ∧
      (∀ p : PrimeSpectrum R,
        IsLocalCompleteIntersection p.asIdeal.ResidueField
          (p.asIdeal.ResidueField ⊗[R] B)) ∧
      ∃ β : (B ⧸ (RingHom.ker π).map (algebraMap R B)) ≃+* B₀,
        ∀ r : R,
          β (Ideal.Quotient.mk ((RingHom.ker π).map (algebraMap R B))
            (algebraMap R B r)) = algebraMap R₀ B₀ (π r) := by
  sorry

end Algebra
