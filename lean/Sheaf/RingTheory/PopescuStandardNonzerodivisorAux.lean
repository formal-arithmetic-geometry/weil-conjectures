module
public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.CategoryTheory.ObjectProperty.Ind
public import Sheaf.RingTheory.GRing
public import Mathlib.RingTheory.Smooth.Basic
public import Mathlib.RingTheory.Localization.Algebra
import Sheaf.RingTheory.ReducedNoetherianTotalRingFractions
import Sheaf.RingTheory.FilteredColimitSmoothProduct
import Mathlib.Algebra.Category.Ring.FinitePresentation
import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
import Mathlib.CategoryTheory.Filtered.Connected
@[expose] public section
open CategoryTheory
open Algebra
open scoped nonZeroDivisors
universe u v

/-- The field hypothesis gives a smooth factorization after localizing at nonzerodivisors.
Source: Stacks Project, Smoothing Ring Maps, Lemma Tag 07F5, third paragraph
(blueprint: lem-weil-pbc-popescu-standard-nonzerodivisor-aux).

Proof: Put S = R⁰ and Q = S⁻¹R. Since R is reduced and Noetherian, its total fraction
ring is a finite product of its localizations at minimal primes, which are fields.
Since R is nonzero there is at least one minimal prime. Each such localization is
canonically its residue field. Localization is base change, and tensor product
commutes with finite products, so S⁻¹Λ is the corresponding product of the fibres
Λᵢ = κ(qᵢ) ⊗[R] Λ. Each Λᵢ is Noetherian: it is a quotient of a localization of Λ.
Regularity of R → Λ says these fibres are geometrically regular. The map κ(qᵢ) → Λᵢ
is flat because its base is a field, and its sole fibre is Λᵢ itself, so it is regular.
The hypothesis therefore supplies a filtered colimit of smooth algebras for each Λᵢ.
Iterating `Algebra.ind_smooth_prod` gives such a colimit for their product over Q,
transported along the canonical product identifications. Finite presentation survives
base change, so S⁻¹A is finitely presented over Q. The finite-presentation factorization
lemma applied to S⁻¹α into this filtered colimit gives one smooth term B', a map β'
into it and its colimit coprojection γ', with γ'β' = S⁻¹α. The diagram and its terms
are in universe max u v, so B' has exactly the universe required here. The equality
of underlying ring homomorphisms expresses this same factorization. -/
theorem exists_localized_smooth_factorization
    (h : ∀ (k : Type u) (Λ : Type (max u v)) [Field k] [CommRing Λ] [Algebra k Λ]
      [IsNoetherianRing Λ],
      RingHom.IsRegular (algebraMap k Λ) →
        ObjectProperty.ind.{max u v}
          (fun B : CommAlgCat.{max u v} k ↦ Algebra.Smooth k B)
          (CommAlgCat.of k Λ))
    (R : Type u) (Λ : Type (max u v)) [CommRing R] [CommRing Λ] [Algebra R Λ]
    [IsNoetherianRing R] [IsNoetherianRing Λ] [Nontrivial R] [IsReduced R]
    (hreg : RingHom.IsRegular (algebraMap R Λ))
    (A : Type (max u v)) [CommRing A] [Algebra R A] [Algebra.FinitePresentation R A]
    (α : A →ₐ[R] Λ) :
    ∃ (B' : Type (max u v)) (_ : CommRing B')
      (_ : Algebra (Localization R⁰) B') (_ : Algebra.Smooth (Localization R⁰) B')
      (β' : Localization (Algebra.algebraMapSubmonoid A R⁰) →ₐ[Localization R⁰] B')
      (γ' : B' →ₐ[Localization R⁰]
        Localization (Algebra.algebraMapSubmonoid Λ R⁰)),
      γ'.toRingHom.comp β'.toRingHom =
        IsLocalization.map (Localization (Algebra.algebraMapSubmonoid Λ R⁰))
          α.toRingHom (Algebra.algebraMapSubmonoid_le_comap R⁰ α) := by
  sorry
