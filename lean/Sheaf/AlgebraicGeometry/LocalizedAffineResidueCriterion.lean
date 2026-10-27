module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.AlgebraicIndependent.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import WeilConjectures.AlgebraicGeometry.QuasiFiniteMorphism
import Mathlib.AlgebraicGeometry.Artinian
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.RingTheory.TensorProduct.Maps
import WeilConjectures.AlgebraicGeometry.SpecLocalRingCanonicalMorphism

/-!
# The localized affine residue criterion for quasi-finiteness

Source: Stacks Project, Tag 0AB6, final paragraph of the proof of
`lemma-quasi-finite-in-codim-1`; Tags 00E5, 00E6, 00GA, 00KH, 01I4, 01K1 and 01TD
(blueprint: lem-sfb-localized-affine-residue-criterion-quasifinite).

The ring equivalences are specified on quotient classes and pure tensors. Their
compatibility with the residue map specifies the canonical residue-field actions.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory TensorProduct

namespace AlgebraicGeometry

/-- The localized coordinate algebra `A ⊗[R] Rₚ`. Source: Stacks Project, Tag 00E6
(blueprint: lem-sfb-localized-affine-residue-criterion-quasifinite). -/
abbrev localizedAffineCoordinateAlgebra (R A : Type u) [CommRing R] [CommRing A]
    [Algebra R A] (p : PrimeSpectrum R) :=
  A ⊗[R] Localization.AtPrime p.asIdeal

/-- The canonical right action of `Rₚ` on `A ⊗[R] Rₚ`. Source: Stacks Project,
Tag 00E6 (blueprint: lem-sfb-localized-affine-residue-criterion-quasifinite). -/
noncomputable instance localizedAffineCoordinateAlgebra_algebra
    (R A : Type u) [CommRing R] [CommRing A] [Algebra R A] (p : PrimeSpectrum R) :
    Algebra (Localization.AtPrime p.asIdeal) (localizedAffineCoordinateAlgebra R A p) :=
  Algebra.TensorProduct.rightAlgebra

/-- The canonical residue scalar action on `C/P` for a prime over the maximal ideal.
Source: Stacks Project, Tag 00E6
(blueprint: lem-sfb-localized-affine-residue-criterion-quasifinite). -/
noncomputable instance localizedAffinePrimeQuotient_algebra
    (R A : Type u) [CommRing R] [CommRing A] [Algebra R A] (p : PrimeSpectrum R)
    (P : Ideal (localizedAffineCoordinateAlgebra R A p))
    [P.LiesOver (IsLocalRing.maximalIdeal (Localization.AtPrime p.asIdeal))] :
    Algebra p.asIdeal.ResidueField (localizedAffineCoordinateAlgebra R A p ⧸ P) :=
  Ideal.Quotient.algebraOfLiesOver P
    (IsLocalRing.maximalIdeal (Localization.AtPrime p.asIdeal))

/-- The quotient `C/mC`, where `C = A ⊗[R] Rₚ` and `m` is the maximal ideal of `Rₚ`.
Source: Stacks Project, Tag 00E6
(blueprint: lem-sfb-localized-affine-residue-criterion-quasifinite). -/
abbrev localizedAffineFibreQuotient (R A : Type u) [CommRing R] [CommRing A]
    [Algebra R A] (p : PrimeSpectrum R) :=
  localizedAffineCoordinateAlgebra R A p ⧸
    (IsLocalRing.maximalIdeal (Localization.AtPrime p.asIdeal)).map
      (algebraMap (Localization.AtPrime p.asIdeal) (localizedAffineCoordinateAlgebra R A p))

/-- The full single-fibre residue criterion, with the original affine charts.
Source: Stacks Project, Tag 0AB6, final paragraph, and Tags 00E5, 00E6, 00GA, 00KH,
01I4, 01K1 and 01TD (blueprint: lem-sfb-localized-affine-residue-criterion-quasifinite).

Proof:
1. By `lem-weil-pbc-lft-affine-pairs`, the compatible affine charts give a finite-type
   ring map. Its finitely many algebra generators still generate after tensoring with k
   (`def-weil-pbc-finite-type-algebra`).
2. The tensor pushout universal property gives `[c] ↦ c ⊗ 1` and
   `c ⊗ residue(b) ↦ [bc]`, mutually inverse by the balancing relations. It also gives
   `(a ⊗ b) ⊗ x ↦ a ⊗ residue(b)x` and `a ⊗ x ↦ (a ⊗ 1) ⊗ x`.
   These preserve multiplication and the k-actions
   (`lem-weil-pbc-algebra-tensor-pushout-universal-property`,
   `def-weil-pbc-algebra-hom-quotient`).
3. Quotient prime correspondence identifies primes of C/mC with primes containing mC.
   Since m is maximal, these are exactly the primes lying over m. The quotient rings
   `F/(P/mC)` and `C/P` agree, hence so do their fraction fields and k-actions
   (`def-weil-pbc-algebra-hom-quotient`, `def-weil-pbc-localization-at-prime`).
4. Transcendence degree zero makes every element of each fraction field algebraic
   (`def-kun-transcendence-degree`). A nonzero element of the domain F/Q satisfies a
   least-degree polynomial whose constant coefficient is nonzero. Its equation expresses
   the inverse in F/Q, so Q is maximal. This also treats the empty spectrum.
5. `lem-weil-pbc-spec-local-ring-canonical-morphism` identifies the canonical map from
   Spec k with Spec of R → Rₚ → k. Apply `lem-weil-pbc-fibre-product-affine-spectra`
   and step 2 to obtain the fibre isomorphism, with its two projections. Step 1 gives
   finite type over k; the spectrum is quasi-compact by
   `lem-weil-pbc-spec-basic-opens-unit-ideal-quasi-compact`. Maximality of all primes
   gives dimension at most zero, using `def-weil-pbc-krull-dimension-ring` and
   `lem-weil-pbc-spec-topological-krull-dimension-ring`.
6. `lem-weil-pbc-finite-type-dim-zero-artinian` makes Spec F finite and discrete.
   The fibre homeomorphism of `def-pc-scheme-fibre` gives finiteness in the affine chart.
7. `lem-weil-pbc-fibre-ring-primes-bijection` identifies each prime over p with an
   isolated fibre point. Apply `def-weil-pbc-ring-map-quasi-finite-at-prime`, then use
   the original affine open immersions as the witnesses in `pqf-def-quasifinite`.
-/
theorem localizedAffineResidueCriterion
    (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]
    (Z S : Scheme.{u}) (g : Z ⟶ S) [LocallyOfFiniteType g]
    (iU : Spec (.of A) ⟶ Z) [IsOpenImmersion iU]
    (iV : Spec (.of R) ⟶ S) [IsOpenImmersion iV]
    (hchart : Spec.map (CommRingCat.ofHom (algebraMap R A)) ≫ iV = iU ≫ g)
    (p : PrimeSpectrum R)
    (hres : ∀ (P : Ideal (localizedAffineCoordinateAlgebra R A p)) [P.IsPrime]
      [P.LiesOver (IsLocalRing.maximalIdeal (Localization.AtPrime p.asIdeal))],
      Algebra.trdeg p.asIdeal.ResidueField
        (FractionRing (localizedAffineCoordinateAlgebra R A p ⧸ P)) = 0) :
    ∃ (t : p.asIdeal.ResidueField →+* localizedAffineFibreQuotient R A p)
      (e₁ : localizedAffineFibreQuotient R A p ≃+*
        (localizedAffineCoordinateAlgebra R A p ⊗[Localization.AtPrime p.asIdeal]
          p.asIdeal.ResidueField))
      (e₂ : (localizedAffineCoordinateAlgebra R A p ⊗[Localization.AtPrime p.asIdeal]
          p.asIdeal.ResidueField) ≃+* (A ⊗[R] p.asIdeal.ResidueField)),
      (∀ b : Localization.AtPrime p.asIdeal,
        t (IsLocalRing.residue _ b) = algebraMap _ (localizedAffineFibreQuotient R A p)
          (algebraMap _ (localizedAffineCoordinateAlgebra R A p) b)) ∧
      (∀ c : localizedAffineCoordinateAlgebra R A p,
        e₁ (algebraMap _ (localizedAffineFibreQuotient R A p) c) = c ⊗ₜ 1) ∧
      (∀ (a : A) (b : Localization.AtPrime p.asIdeal) (x : p.asIdeal.ResidueField),
        e₂ ((a ⊗ₜ[R] b) ⊗ₜ x) = a ⊗ₜ[R] (IsLocalRing.residue _ b * x)) ∧
      (∀ x : p.asIdeal.ResidueField, e₁ (t x) = 1 ⊗ₜ x) ∧
      (∀ x : p.asIdeal.ResidueField, e₂ (1 ⊗ₜ x) = 1 ⊗ₜ[R] x) ∧
      (∃ eU : (Spec.map (CommRingCat.ofHom (algebraMap R A))).fiber p ≅
          Spec (.of (localizedAffineFibreQuotient R A p)),
        eU.hom ≫ Spec.map (CommRingCat.ofHom t) =
          (Spec.map (CommRingCat.ofHom (algebraMap R A))).fiberToSpecResidueField p ≫
            Spec.map (Scheme.Spec.residueFieldIso (.of R) p).inv ∧
        eU.hom ≫ Spec.map (CommRingCat.ofHom
          ((algebraMap (localizedAffineCoordinateAlgebra R A p)
            (localizedAffineFibreQuotient R A p)).comp
              (Algebra.TensorProduct.includeLeft :
                A →ₐ[R] localizedAffineCoordinateAlgebra R A p).toRingHom)) =
          (Spec.map (CommRingCat.ofHom (algebraMap R A))).fiberι p) ∧
      Function.Injective (PrimeSpectrum.comap
        (algebraMap (localizedAffineCoordinateAlgebra R A p)
          (localizedAffineFibreQuotient R A p))) ∧
      (Set.range (PrimeSpectrum.comap
        (algebraMap (localizedAffineCoordinateAlgebra R A p)
          (localizedAffineFibreQuotient R A p))) =
        {P : PrimeSpectrum (localizedAffineCoordinateAlgebra R A p) |
          P.asIdeal.comap (algebraMap (Localization.AtPrime p.asIdeal)
            (localizedAffineCoordinateAlgebra R A p)) =
              IsLocalRing.maximalIdeal (Localization.AtPrime p.asIdeal)}) ∧
      (∀ Q : PrimeSpectrum (localizedAffineFibreQuotient R A p),
        Function.Bijective (Ideal.ResidueField.map
          (Q.comap (algebraMap (localizedAffineCoordinateAlgebra R A p)
            (localizedAffineFibreQuotient R A p))).asIdeal Q.asIdeal
          (algebraMap (localizedAffineCoordinateAlgebra R A p)
            (localizedAffineFibreQuotient R A p)) rfl)) ∧
      LocallyOfFiniteType (Spec.map (CommRingCat.ofHom t)) ∧
      QuasiCompact (Spec.map (CommRingCat.ofHom t)) ∧
      (∀ Q : PrimeSpectrum (localizedAffineFibreQuotient R A p),
        IsClosed ({Q} : Set (PrimeSpectrum (localizedAffineFibreQuotient R A p)))) ∧
      Finite (PrimeSpectrum (localizedAffineFibreQuotient R A p)) ∧
      DiscreteTopology (PrimeSpectrum (localizedAffineFibreQuotient R A p)) ∧
      Set.Finite {z : Z | z ∈ Set.range iU ∧ g z = iV p} ∧
      (∀ z : Z, z ∈ Set.range iU → g z = iV p → g.IsQuasiFiniteAtPoint z) := by
  sorry

end AlgebraicGeometry
