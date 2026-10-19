/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q08
-/
module

public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.RingTheory.Localization.FractionRing
public import WeilConjectures.AlgebraicGeometry.QuasiFiniteMorphism
public import WeilConjectures.Mathlib.Topology.KrullDimension

import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.RingTheory.AlgebraicIndependent.Basic
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.TensorProduct.MvPolynomial
import WeilConjectures.AlgebraicGeometry.QuasiFiniteLocallyQuasiFinite
import Sheaf.Paper.QuasiFiniteOverPolynomialAlgebra
import Sheaf.RingTheory.FibrePrimesResidueFields
import WeilConjectures.RingTheory.FiniteRingMapQuasiFinite
import WeilConjectures.RingTheory.LocalizationPrimeResidueFieldIso
import Sheaf.RingTheory.QuasiFiniteAtPrimePrincipalLocalization
import Sheaf.RingTheory.QuasiFiniteLocusOpen
import WeilConjectures.AlgebraicGeometry.Morphisms.ProperQuasiFinite
import Sheaf.RingTheory.QuasiFiniteComposition
import Sheaf.TraceFormula.RefinedNoetherNormalizationPrime
import WeilConjectures.RingTheory.QuasiFiniteAtPrime

/-!
# Refined quasi-finite affine-space charts

Source: Stacks Project, Algebra, Tag 0520,
`lemma-refined-quasi-finite-over-polynomial-algebra`, and More on Morphisms,
Tag 052E, first paragraph of the proof of `lemma-local-structure-finite-type`.
(blueprint: lem-trf-refined-quasi-finite-polynomial-pure-transcendental)
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- A finite type morphism of affine schemes has, near a marked point, a
quasi-finite chart in affine space of dimension equal to the topological fibre
dimension at that point. The residue field of the image is a rational function
field in at most that many variables over the base residue field. The displayed
ring equivalence commutes with the canonical map of residue fields, so it is an
isomorphism over that base field. Restriction to the open `U` identifies its base
residue field canonically with the residue field at `p z` in `S`.

Source: Stacks Project, Algebra, Tag 0520, and More on Morphisms, Tag 052E,
first paragraph of the proof of `lemma-local-structure-finite-type`.
(blueprint: lem-trf-refined-quasi-finite-polynomial-pure-transcendental)

Proof:
1. Write the affine schemes as spectra. The affine fibre formula
   (`lem-weil-pbc-fibre-product-affine-spectra`) and the fibre prime correspondence
   (`lem-weil-pbc-fibre-ring-primes-residue-fields`) identify the marked fibre
   point and its topological dimension. Apply
   `lem-weil-pbc-quasi-finite-over-polynomial-algebra` to obtain an initial
   quasi-finite polynomial chart after localizing the source away from the point.
2. Pass to the image prime in this polynomial chart and then its special-fibre
   prime. Use `lem-weil-pbc-polynomial-scalar-extension` and
   `lem-trf-refined-noether-normalization-prime` to make this prime the coordinate
   ideal `(x_(r+1), ..., x_n)` under a finite polynomial-algebra map over the
   residue field. This uses the residue field of the image, not of the source.
3. Clear the finitely many coefficient denominators away from the base prime.
   Lift the normalized coordinates over `R_f`; the polynomial universal property
   gives the lifted ring map. Fibre prime correspondence identifies its image
   prime with the inverse image of the special-fibre coordinate prime.
4. The fibre of the lifted map is the scalar extension of the finite normalized
   special-fibre map: the tensor isomorphisms send `d ⊗ a` to `d_bar ⊗ a` and
   `(d ⊗ b) ⊗ a` to `d ⊗ ba`. Finite module generators remain generators after
   tensoring. Thus `lem-weil-pbc-finite-ring-map-quasi-finite` isolates the marked
   fibre prime. Apply `lem-weil-pbc-ring-quasi-finite-locus-open` to shrink to a
   principal open on which the lifted map is quasi-finite everywhere.
5. Localize the original chart at the same base and polynomial elements using
   `lem-weil-pbc-quasi-finite-at-prime-principal-localization`; compose using
   `lem-trf-quasi-finite-composition`. The iterated source localization is a
   principal localization of the original source: write the last inverted
   element as `a/(gf)^N` and invert `gfa`. The principal-localization open
   immersion lemma supplies affine neighbourhoods containing the marked points.
6. Compute the final image prime by testing each polynomial after setting the
   last `n-r` variables to zero. Its coefficients vanish in the residue field
   exactly when they belong to the base prime. Hence the image prime is
   `(p R_f, x_(r+1), ..., x_n)`. Localization extension-contraction and the fibre
   prime correspondence justify the computation, rather than identifying it
   with the image prime of the original chart.
7. Translate the ring map into the displayed morphism over `U`. The affine
   quasi-finite-at-every-prime condition gives local quasi-finiteness. Basic open
   inverse images are affine and quasi-compact, so
   `pqf-lem-qf-locqf-qc` gives quasi-finiteness. The fibres are finite by
   `pqf-lem-qf-finitefibres` and discrete by their isolated-point description.
8. The quotient of the special-fibre polynomial ring by its coordinate prime
   is the polynomial ring in the first `r` variables. Its residue field is its
   fraction field. The fibre and localization residue-field comparisons
   identify this with the residue field of the final image over the base field.
   Its transcendence degree satisfies `r ≤ n`, since the original polynomial
   residue field is generated as a field by the images of `n` variables.
-/
theorem exists_refined_quasiFinite_polynomial_pureTranscendental
    {Z S : Scheme.{u}} [IsAffine Z] [IsAffine S]
    (p : Z ⟶ S) [LocallyOfFiniteType p] [QuasiCompact p] (z : Z) :
    ∃ n : ℕ, topologicalKrullDimAt (p.asFiber z) = (n : WithBot ℕ∞) ∧
      ∃ (U : S.Opens) (V : Z.Opens),
        IsAffineOpen U ∧ p z ∈ U ∧ IsAffineOpen V ∧
        ∃ (z₀ : V.toScheme)
          (q : V.toScheme ⟶ AffineSpace (ULift.{u} (Fin n)) U.toScheme),
          V.ι z₀ = z ∧
          q ≫ (AffineSpace (ULift.{u} (Fin n)) U.toScheme ↘ U.toScheme) ≫ U.ι =
            V.ι ≫ p ∧
          q.IsQuasiFinite ∧
          ∃ r : ℕ, r ≤ n ∧
            ∃ e : (AffineSpace (ULift.{u} (Fin n)) U.toScheme).residueField (q z₀) ≃+*
                FractionRing (MvPolynomial (Fin r)
                  (U.toScheme.residueField
                    ((AffineSpace (ULift.{u} (Fin n)) U.toScheme ↘ U.toScheme) (q z₀)))),
              ∀ a : U.toScheme.residueField
                  ((AffineSpace (ULift.{u} (Fin n)) U.toScheme ↘ U.toScheme) (q z₀)),
                e ((Scheme.Hom.residueFieldMap
                  (AffineSpace (ULift.{u} (Fin n)) U.toScheme ↘ U.toScheme)
                  (q z₀)).hom a) = algebraMap _ _ a := by
  sorry

end AlgebraicGeometry
