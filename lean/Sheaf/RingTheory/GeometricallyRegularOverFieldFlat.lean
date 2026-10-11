/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K1
-/
import Sheaf.RingTheory.GRing
import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.RingTheory.Kaehler.Basic
import Mathlib.LinearAlgebra.Basis.Defs

/-!
# Flatness over a polynomial localization from a differential basis

Source: Stacks Project, More on Algebra, Lemma 07E6 and its proof
(blueprint: lem-weil-pbc-geometrically-regular-over-field-flat).
-/

universe u v

namespace Algebra

/-- A differential basis in a finitely generated residue subfield gives a flat polynomial
localization map and a regular local closed fibre. Source: Stacks Project, More on Algebra,
Lemma 07E6 (blueprint: lem-weil-pbc-geometrically-regular-over-field-flat).

Proof: (1) Put `R = k[y]`, `p = φ⁻¹(m)` and `A₀ = Rₚ`. Elements outside `p` map to units,
so `φ` has a unique extension to `A₀`. Its residue field `K₀` embeds in `F`, and `pA = m₀A`.
Noetherianity follows from finite type and localization
(lem-weil-pbc-finite-type-algebra-noetherian, lem-weil-pbc-localization-noetherian).
(2) The polynomial differential basis and its localization make Ω[A₀/k] free on `dyᵢ`.
The residue differential map is surjective; applying Ω[K₀/k] → Ω[F/k] to a relation proves
injectivity using the given basis (lem-weil-pbc-polynomial-ring-kahler-basis,
lem-weil-pbc-kahler-differentials-localization, lem-weil-pbc-jacobi-zariski-differential-maps).
(3) Every finite purely inseparable scalar extension of `A₀` is a localization of a polynomial
ring over a field, hence regular (lem-weil-pbc-polynomial-scalar-extension,
lem-weil-pbc-polynomial-ring-smooth, lem-weil-pbc-field-regular-ring,
lem-weil-pbc-regular-ring-smooth-ascent, lem-weil-pbc-localization-of-regular-ring).
(4) Proposition 07E5 gives injectivity of H₁(L[K₀/k]) → m₀/m₀² and regularity of `A₀`.
The Jacobi–Zariski sequence and (2) give surjectivity, hence an isomorphism
(lem-weil-pbc-geometrically-regular-h1-injective,
lem-weil-pbc-jacobi-zariski-homology-sequence, lem-weil-pbc-jacobi-zariski-surjection-h1).
(5) Functoriality gives the commutative square comparing this map with H₁(L[K/k]) → m/m².
Its left side is injective by 07E2, and its bottom by 07E5, so its right side is injective;
07E5 also makes `A` regular (lem-weil-pbc-nl-presentation-h1-functoriality,
lem-weil-pbc-transitivity-gamma, lem-weil-pbc-geometrically-regular-h1-injective).
(6) Nakayama identifies minimal generators with cotangent bases. Extend the images of a
parameter system of `A₀` to a parameter system of `A`. These form a regular sequence,
and quotienting by the initial segment is regular local
(lem-weil-pbc-nakayama-local-generators, lem-weil-pbc-noetherian-local-dimension-le-generators,
lem-weil-pbc-regular-local-generators-regular-sequence).
(7) The local flatness criterion 07DY gives flatness, and `pA = m₀A` gives the stated quotient
(lem-weil-pbc-flat-over-regular). The extension is specified by its restriction to `R`;
the universal property of localization makes it the induced map in the source. -/
theorem exists_flat_polynomialLocalization_of_isGeometricallyRegular
    (k : Type u) (A : Type v) [Field k] [CommRing A] [Algebra k A]
    [IsLocalRing A] [IsNoetherianRing A] (pchar : ℕ) [Fact pchar.Prime] [CharP k pchar]
    (hreg : IsGeometricallyRegular k A)
    (F : IntermediateField k (IsLocalRing.ResidueField A)) (hF : F.FG)
    (m : ℕ) (φ : MvPolynomial (Fin m) k →ₐ[k] A)
    (a : Fin m → F)
    (ha : ∀ i : Fin m, (a i : IsLocalRing.ResidueField A) =
      IsLocalRing.residue A (φ (MvPolynomial.X i)))
    (b : Module.Basis (Fin m) F (KaehlerDifferential k F))
    (hb : ∀ i : Fin m, b i = KaehlerDifferential.D k F (a i)) :
    let p := (IsLocalRing.maximalIdeal A).comap φ.toRingHom
    ∃ ψ : Localization.AtPrime p →+* A,
      ψ.comp (algebraMap (MvPolynomial (Fin m) k) (Localization.AtPrime p)) = φ.toRingHom ∧
      ψ.Flat ∧ IsRegularLocalRing (A ⧸ p.map φ.toRingHom) := by
  sorry

end Algebra
