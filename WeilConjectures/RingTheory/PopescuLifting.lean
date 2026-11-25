/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.SingularIdeal
public import Mathlib.RingTheory.FinitePresentation
import WeilConjectures.RingTheory.PopescuLiftMaps
import WeilConjectures.RingTheory.PopescuLiftSmooth

/-! # Popescu lifting lemma

Let `R` be Noetherian with `Ann(π) = Ann(π²)` in `R` and in `Λ`, and let `Cbar` be a finitely
presented `R/π²`-algebra with a map `Cbar → Λ/π²Λ`. Then there is a finitely presented
`R`-algebra `D` with `D → Λ` and `Cbar → D/πD` compatible modulo `π`, such that `R → D` is
smooth away from `π` and at the primes over the smooth locus of `Cbar`, and `Cbar/πCbar → D/πD`
is smooth there too.

## Implementation details

The quotient maps in `popescu_lifting` are specified by their composites with the surjective
quotient projections, so they are the induced maps. The last smoothness clause uses the
algebra structure induced by `cmod` on `D / πD`.

In the Nakayama step (3) of the proof, Stacks replaces `a_k` by `a_k b_k`; since `b_k ∈ I`
maps to `0` in `Cbar`, the intended replacement is `a_k (a_k^N + b_k)`, which is what the
formalization uses.

## References

* [Stacks, Tag 07CP]
-/

@[expose] public section

universe a b c

namespace Algebra

/-- Popescu's lifting lemma: the map `Cbar → Λ/π²Λ` lifts to `D → Λ` for a finitely presented
`R`-algebra `D` that is smooth away from `π` and over the smooth locus of `Cbar`. -/
theorem popescu_lifting (R : Type a) (Λ : Type b) (Cbar : Type c)
    [CommRing R] [CommRing Λ] [CommRing Cbar]
    [Algebra R Λ] [Algebra R Cbar] [IsNoetherianRing R] (π : R)
    (hAnnR : Module.annihilator R (Ideal.span ({π} : Set R)) =
      Module.annihilator R (Ideal.span ({π ^ 2} : Set R)))
    (hAnnΛ : Module.annihilator Λ
        (Ideal.span ({algebraMap R Λ π} : Set Λ)) =
      Module.annihilator Λ
        (Ideal.span ({algebraMap R Λ (π ^ 2)} : Set Λ)))
    [Algebra (R ⧸ Ideal.span ({π ^ 2} : Set R)) Cbar]
    [IsScalarTower R (R ⧸ Ideal.span ({π ^ 2} : Set R)) Cbar]
    [Algebra.FinitePresentation (R ⧸ Ideal.span ({π ^ 2} : Set R)) Cbar]
    (j : Cbar →ₐ[R] (Λ ⧸ Ideal.span ({algebraMap R Λ (π ^ 2)} : Set Λ))) :
    ∃ (D : Type (max a c)) (_ : CommRing D) (_ : Algebra R D)
      (φ : D →ₐ[R] Λ)
      (ψ : (D ⧸ Ideal.span ({algebraMap R D π} : Set D)) →+*
        (Λ ⧸ Ideal.span ({algebraMap R Λ π} : Set Λ)))
      (red : (Λ ⧸ Ideal.span ({algebraMap R Λ (π ^ 2)} : Set Λ)) →+*
        (Λ ⧸ Ideal.span ({algebraMap R Λ π} : Set Λ)))
      (c : Cbar →ₐ[R] (D ⧸ Ideal.span ({algebraMap R D π} : Set D)))
      (cmod : (Cbar ⧸ Ideal.span ({algebraMap R Cbar π} : Set Cbar)) →+*
        (D ⧸ Ideal.span ({algebraMap R D π} : Set D))),
      Algebra.FinitePresentation R D ∧
      ψ.comp (Ideal.Quotient.mk _) = (Ideal.Quotient.mk _).comp φ.toRingHom ∧
      red.comp (Ideal.Quotient.mk _) = Ideal.Quotient.mk _ ∧
      ψ.comp c.toRingHom = red.comp j.toRingHom ∧
      cmod.comp (Ideal.Quotient.mk _) = c.toRingHom ∧
      (∀ q : PrimeSpectrum D, algebraMap R D π ∉ q.asIdeal → IsSmoothAtPrime R q) ∧
      (∀ q : PrimeSpectrum (D ⧸ Ideal.span ({algebraMap R D π} : Set D)),
        IsSmoothAtPrime (R ⧸ Ideal.span ({π ^ 2} : Set R))
          (PrimeSpectrum.comap c.toRingHom q) →
        IsSmoothAtPrime R (PrimeSpectrum.comap (Ideal.Quotient.mk _) q)) ∧
      (∀ q : PrimeSpectrum (D ⧸ Ideal.span ({algebraMap R D π} : Set D)),
        IsSmoothAtPrime (R ⧸ Ideal.span ({π ^ 2} : Set R))
          (PrimeSpectrum.comap c.toRingHom q) →
        @IsSmoothAtPrime (Cbar ⧸ Ideal.span ({algebraMap R Cbar π} : Set Cbar))
          (D ⧸ Ideal.span ({algebraMap R D π} : Set D)) _ _ cmod.toAlgebra q) := by
  obtain ⟨d, hd⟩ := exists_popescu_lift_preparation R Cbar π
  obtain ⟨φ, ψ, red, c, cmod, hψ, hred, hsquare, hcmod, hc⟩ :=
    exists_popescu_lift_maps R Λ Cbar π d hd hAnnΛ j
  obtain ⟨haway, hover, hmod⟩ := popescu_lift_smooth R Cbar π d hd hAnnR c cmod hc hcmod
  exact ⟨d.liftingAlgebra, inferInstance, inferInstance, φ, ψ, red, c, cmod,
    d.finitePresentation, hψ, hred, hsquare, hcmod, haway, hover, hmod⟩

end Algebra
