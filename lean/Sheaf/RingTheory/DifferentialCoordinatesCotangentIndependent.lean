/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V2
-/
module

public import Sheaf.RingTheory.GRing
public import Mathlib.RingTheory.Ideal.Cotangent
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.RingTheory.Kaehler.Basic
public import Mathlib.LinearAlgebra.Basis.Defs
import Sheaf.RingTheory.GeometricallyRegularH1Injective
import Sheaf.RingTheory.JacobiZariskiHomologySequence
import Sheaf.RingTheory.TransitivityGamma
import Mathlib.RingTheory.Kaehler.Polynomial
import Mathlib.RingTheory.Etale.Kaehler
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.TensorProduct.MvPolynomial
import WeilConjectures.Mathlib.RingTheory.RegularLocalRing.Defs

/-!
# Cotangent independence from differential coordinates

Source: Stacks Project, More on Algebra, Tag 07E6, proof before the final application
of Algebra, Tags 07DY and 00NQ.
-/

@[expose] public section

set_option autoImplicit false
universe u v
namespace Algebra

/-- A residue differential basis preserves independence of cotangent classes from the
polynomial localization after extending coefficients to the target residue field.
Source: Stacks Project, More on Algebra, Tag 07E6, proof, the differential comparison
and the commutative square, before extending a regular system of parameters.
(blueprint: lem-weil-pbc-differential-coordinates-cotangent-independent).

Proof: Write R = k[y], p = φ⁻¹(m), A₀ = R_p, and K₀ for the residue field of A₀.
The restriction equation for ψ identifies its residue-field map with the embedding
of Frac(R/p) in K. Its image lies in F because the residue images of the variables
lie in F. Polynomial differentials and localization identify Ω[A₀/k] with a free
module on dy_i. The residue comparison Ω[A₀/k] ⊗ K₀ → Ω[K₀/k] is surjective.
A relation among d(y_i) in Ω[K₀/k] maps to a relation in Ω[F/k]; the supplied basis
makes every coefficient zero. Thus this comparison is an isomorphism.
The ring A₀ is geometrically regular: after a finite purely inseparable field
extension it is a localization of a polynomial ring over that field, hence regular.
Proposition 07E5 gives injectivity of H₁(L[K₀/k]) → m₀/m₀². Jacobi-Zariski and the
isomorphic residue differential comparison give surjectivity, hence an isomorphism.
The right-hand comparison sends the class of z tensored with c to c times the class
of ψ(z). The square with bottom H₁(L[K/k]) → m/m² commutes as follows. The two
composites from the presentation k[K₀] to A[K] factor respectively through A₀[K₀]
and k[K]. They induce the same map on H₁ by independence of presentation morphisms
and compatibility with composition. The surjection-to-conormal equivalences are
compatible with these maps: choose a section of A → K agreeing on K₀ with ψ of a
section of A₀ → K₀. Evaluation of a relation then gives ψ of its old evaluation,
so its conormal class maps to the class of ψ(z). Tensoring yields the square.
Its top is an isomorphism; its left is injective by 07E2 and its bottom by 07E5
for A. Thus its right is injective, because every source element comes from the
top and equality of its images forces equality along the left and bottom.
An independent family of classes in m₀/m₀² stays independent under field scalar
extension. The injective right-hand map therefore takes it to independent cotangent
classes in m/m², proving the assertion. Arbitrary independent sets are allowed: the
same argument applies to each finite relation. Empty sets and an empty differential
basis are included; no finiteness of K over k is assumed. -/
theorem linearIndepOn_of_residue_differential_basis
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
    ∀ (ψ : Localization.AtPrime p →+* A) [IsLocalHom ψ],
      ψ.comp (algebraMap (MvPolynomial (Fin m) k) (Localization.AtPrime p)) =
        φ.toRingHom →
      ∀ s : Set (IsLocalRing.maximalIdeal (Localization.AtPrime p)),
        LinearIndepOn (IsLocalRing.ResidueField (Localization.AtPrime p))
          (IsLocalRing.maximalIdeal (Localization.AtPrime p)).toCotangent s →
        LinearIndepOn (IsLocalRing.ResidueField A)
          (fun x : IsLocalRing.maximalIdeal (Localization.AtPrime p) ↦
            (IsLocalRing.maximalIdeal A).toCotangent
            ⟨ψ x, map_nonunit ψ x x.2⟩) s := by sorry

end Algebra
