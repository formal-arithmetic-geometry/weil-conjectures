/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Finite.FiniteCoefficientPoint
public import WeilConjectures.SmoothPurity.FiniteFieldDatum.FrobeniusDetailed
public import WeilConjectures.AlgebraicGeometry.SixFunctors.InverseImagePullbackComparison
public import WeilConjectures.SmoothPurity.Supporting.IsomorphismDerivedPullback
public import WeilConjectures.AlgebraicGeometry.CompletedIntegralConstantMapOfUniverses
public import WeilConjectures.SmoothPurity.Completed.CompletedIntegralCoefficientGerm
import Mathlib.Algebra.CharP.CharAndCard
import Mathlib.Algebra.CharP.Invertible
import WeilConjectures.TraceFormula.Integral.IntegralPullbackReductionCounit

/-!
# Point transport along geometric Frobenius

Source: Deligne, Weil II (1.1.7), pp. 150--151; the explicit restriction,
comma-coprojection and sheafification construction in the blueprint
(blueprint: def-weil-frobenius-point-transport).

The canonical sectionwise model of inverse image along an isomorphism identifies
its comma coprojection followed by sheafification with the identity on sections.
Thus sigma is the restriction along g_s in that model. The finite comparison is
the recorded tensor-unit map; the integral comparison is the recorded Roos lift,
not tensor extension by the completed coefficient sheaf. Rational transport is
scalar extension of the integral arrow. The algebraic-closure arrow is represented
at the object's own coefficient stage. No naturality or invertibility is asserted.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048

universe u v w
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale
namespace WeilConjectures

attribute [local irreducible] frobeniusPointIso frobeniusPointRestriction

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The same excluded characteristic makes l a unit in the residue fields.
Source: finite-field datum (blueprint: def-weil-frobenius-point-transport).
Proof: the unique point has residue field canonically k, of characteristic p.
The image of l is nonzero because l and p are distinct primes, hence invertible. -/
theorem frobeniusPointPrimeResidueUnit (D : FiniteFieldDatum.{u}) (l : ℕ)
    [Fact l.Prime] (_hl : l ≠ D.p) :
    ∀ x : Spec (.of D.k), IsUnit (l : (Spec (.of D.k)).residueField x) := by
  intro x
  let : Fintype D.k₀ := Fintype.ofFinite D.k₀
  let : Fact D.p.Prime := ⟨D.prime⟩
  have hc : Fintype.card D.k₀ = D.p ^ D.a := by
    simpa only [Nat.card_eq_fintype_card] using D.card_base.trans D.cardinality_eq
  let : CharP D.k₀ D.p := charP_of_card_eq_prime_pow hc
  have hu : IsUnit (l : D.k₀) := (CharP.isUnit_natCast_iff D.prime).2 (by
    intro hdiv
    exact _hl ((Nat.prime_dvd_prime_iff_eq D.prime (Fact.out : l.Prime)).1 hdiv).symm)
  have hk : IsUnit (l : D.k) := by
    simpa only [map_natCast] using hu.map (algebraMap D.k₀ D.k)
  have h := hk.map
    ((StructureSheaf.toStalk (CommRingCat.of D.k) x) ≫ (Spec (.of D.k)).residue x).hom
  simpa only [map_natCast] using h

/-- The canonical inverse of the residue-field unit; no extra hypothesis on s.
Source: finite-field datum (blueprint: def-weil-frobenius-point-transport). -/
@[instance_reducible]
def frobeniusPointPrimeInvertible (x : Spec (.of D.k)) :
    Invertible (l : (Spec (.of D.k)).residueField x) :=
  (frobeniusPointPrimeResidueUnit D l hl x).invertible

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
  WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective in
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
  WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective in
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
  WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective in
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
  WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective in
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
  WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective in
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
  WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective in
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
  WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective in
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
  WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective in
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
  WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective in
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
  WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective in
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
  WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective in
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
  WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective in
variable (Ω : Type u) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]

end WeilConjectures
