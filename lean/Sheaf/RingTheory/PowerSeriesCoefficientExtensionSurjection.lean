module

public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.RingTheory.MvPowerSeries.Inverse
import Mathlib.RingTheory.MvPowerSeries.Equiv
import WeilConjectures.RingTheory.PowerSeriesCombinedIdealCoefficients
import WeilConjectures.RingTheory.PowerSeriesAdicEvaluation

/-!
# A surjective coefficient extension of a power-series presentation

Source: Stacks Project, varieties.tex, Tag 0C54,
`lemma-base-change-complete-local-ring`, proof, the power-series surjection and quotient
square, abstracted to compatible complete local rings.
(blueprint: lem-trf-power-series-coefficient-extension-surjection).
-/

@[expose] public section

universe uF uK uR uC

namespace MvPowerSeries

/-- Extending coefficients in a chosen complete local power-series presentation gives a
surjection to the target complete local ring, with its quotient square and residue map.
The two algebra structures encode the specified coefficient-field sections. The ideal `J`
is exactly the ideal of transported relations; its displayed equality fixes it uniquely.
Adic continuity is expressed by containment of sufficiently high powers of the source ideal
in each power of the target ideal. The last equality expresses the identity on residues
under the specified identifications with `K`.

Source: Stacks Project, varieties.tex, Tag 0C54,
`lemma-base-change-complete-local-ring`, proof, variable generation, coefficient extension,
transported relations, and the commutative quotient square.
(blueprint: lem-trf-power-series-coefficient-extension-surjection).

Proof:
1. The power-series local-ring criterion (lem-weil-pbc-power-series-local-ring) and the
   combined-ideal coefficient criterion at exponent one and base ideal zero
   (lem-weil-pbc-power-series-combined-ideal-coefficients) identify the source maximal ideal
   with the variables ideal. Surjectivity of `φ` shows its variables generate the maximal
   ideal of `R`. Their images under `h` generate the maximal ideal of `C` by `hm`.
2. Apply lem-trf-coefficient-field-generator-presentation to `C`, its coefficient section,
   residue identification, and these variable images. This gives the continuous surjective
   `K`-algebra map `Ψ`.
3. The coefficientwise map preserves all powers of the variables ideal, so is continuous.
   The maps `Ψ ∘ map ι` and `h ∘ φ` agree on variables and constants by `hcompat`.
   Uniqueness in lem-weil-pbc-power-series-adic-evaluation makes them equal on all series.
4. Every transported relation maps to zero. The quotient universal property gives `θ`,
   surjective because `Ψ` is. The map from the `F`-series ring to this quotient kills the
   kernel of `φ`, so factors uniquely through `R` as `α`. The two factorizations give
   `θ ∘ α = h`.
5. By lem-weil-pbc-power-series-noetherian the `K`-series ring, hence its quotient, is
   Noetherian. Transported relations have zero constant coefficient. Constant coefficient
   descends to the quotient with kernel the ideal of variable classes. A class outside this
   ideal has a representative with nonzero constant coefficient and hence is a unit by the
   power-series local-ring criterion. Thus this is the unique maximal ideal, with residue
   field `K` and the stated normalized residue identification.
6. The images of the generators of the maximal ideal of `R` under `α` are the variable
   classes. Therefore `α` is local and its extended maximal ideal is the quotient maximal
   ideal. On constants `θ` is the given section of `K` into `C`. Every residue is represented
   by a constant, so reduction of `θ` under the two residue identifications is the identity.
-/
theorem exists_coefficient_extension_surjection
    {F : Type uF} {K : Type uK} [Field F] [Field K] (ι : F →+* K)
    {R : Type uR} {C : Type uC} [CommRing R] [CommRing C]
    [IsNoetherianRing R] [IsNoetherianRing C]
    [IsLocalRing R] [IsLocalRing C]
    [IsAdicComplete (IsLocalRing.maximalIdeal R) R]
    [IsAdicComplete (IsLocalRing.maximalIdeal C) C]
    [Algebra F R] [Algebra K C]
    (ρR : R ⧸ IsLocalRing.maximalIdeal R ≃+* F)
    (ρC : C ⧸ IsLocalRing.maximalIdeal C ≃+* K)
    (hσ : ∀ a : F, ρR (Ideal.Quotient.mk _ (algebraMap F R a)) = a)
    (hτ : ∀ a : K, ρC (Ideal.Quotient.mk _ (algebraMap K C a)) = a)
    (h : R →+* C)
    (hlocal : ∀ r ∈ IsLocalRing.maximalIdeal R, h r ∈ IsLocalRing.maximalIdeal C)
    (hcont : ∀ N : ℕ, ∃ M : ℕ, ∀ r ∈ (IsLocalRing.maximalIdeal R) ^ M,
      h r ∈ (IsLocalRing.maximalIdeal C) ^ N)
    (hm : Ideal.map h (IsLocalRing.maximalIdeal R) = IsLocalRing.maximalIdeal C)
    (hcompat : h.comp (algebraMap F R) = (algebraMap K C).comp ι)
    (n s : ℕ) (φ : MvPowerSeries (Fin n) F →ₐ[F] R)
    (hφ : Function.Surjective φ)
    (hφcont : ∀ N : ℕ, ∃ M : ℕ,
      ∀ g ∈ (Ideal.span (Set.range (X : Fin n → MvPowerSeries (Fin n) F))) ^ M,
        φ g ∈ (IsLocalRing.maximalIdeal R) ^ N)
    (f : Fin s → MvPowerSeries (Fin n) F)
    (hker : RingHom.ker φ.toRingHom = Ideal.span (Set.range f))
    (hrel : Ideal.span (Set.range f) ≤
      Ideal.span (Set.range (X : Fin n → MvPowerSeries (Fin n) F))) :
    ∃ J : Ideal (MvPowerSeries (Fin n) K),
      J = Ideal.span (Set.range (fun a : Fin s ↦ map ι (f a))) ∧
      ∃ Ψ : MvPowerSeries (Fin n) K →ₐ[K] C,
        Function.Surjective Ψ ∧
        (∀ N : ℕ, ∃ M : ℕ,
          ∀ g ∈ (Ideal.span (Set.range (X : Fin n → MvPowerSeries (Fin n) K))) ^ M,
            Ψ g ∈ (IsLocalRing.maximalIdeal C) ^ N) ∧
        (∀ i : Fin n, Ψ (X i) = h (φ (X i))) ∧
        Ψ.toRingHom.comp (map ι) = h.comp φ.toRingHom ∧
        J ≤ RingHom.ker Ψ.toRingHom ∧
        ∃ θ : (MvPowerSeries (Fin n) K ⧸ J) →ₐ[K] C,
          Function.Surjective θ ∧
          (∀ g : MvPowerSeries (Fin n) K, θ (Ideal.Quotient.mk J g) = Ψ g) ∧
          IsNoetherianRing (MvPowerSeries (Fin n) K ⧸ J) ∧
          ∃ _ : IsLocalRing (MvPowerSeries (Fin n) K ⧸ J),
            IsLocalRing.maximalIdeal (MvPowerSeries (Fin n) K ⧸ J) =
              Ideal.span (Set.range (fun i : Fin n ↦ Ideal.Quotient.mk J (X i))) ∧
            ∃ ρT : ((MvPowerSeries (Fin n) K ⧸ J) ⧸
                IsLocalRing.maximalIdeal (MvPowerSeries (Fin n) K ⧸ J)) ≃+* K,
              (∀ a : K, ρT (Ideal.Quotient.mk _ (Ideal.Quotient.mk J
                (MvPowerSeries.C a))) = a) ∧
              ∃ α : R →+* (MvPowerSeries (Fin n) K ⧸ J),
                (∀ r ∈ IsLocalRing.maximalIdeal R,
                  α r ∈ IsLocalRing.maximalIdeal (MvPowerSeries (Fin n) K ⧸ J)) ∧
                α.comp φ.toRingHom = (Ideal.Quotient.mk J).comp (map ι) ∧
                (∀ α' : R →+* (MvPowerSeries (Fin n) K ⧸ J),
                  α'.comp φ.toRingHom = (Ideal.Quotient.mk J).comp (map ι) → α' = α) ∧
                θ.toRingHom.comp α = h ∧
                Ideal.map α (IsLocalRing.maximalIdeal R) =
                  IsLocalRing.maximalIdeal (MvPowerSeries (Fin n) K ⧸ J) ∧
                (∀ x : MvPowerSeries (Fin n) K ⧸ J,
                  ρC (Ideal.Quotient.mk _ (θ x)) = ρT (Ideal.Quotient.mk _ x)) := by
  sorry

end MvPowerSeries
