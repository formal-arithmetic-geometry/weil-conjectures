/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import WeilConjectures.FourierTransform.ArtinSchreier
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
import WeilConjectures.AlgebraicGeometry.FiniteCharacterIntegralAffine
import WeilConjectures.AlgebraicGeometry.FiniteCharacterIntegralCompactification
public import Mathlib.AlgebraicGeometry.AffineSpace
import WeilConjectures.Compactification.Affine

/-!
# Finite integral character vanishing

Source: latest blueprint, `sec-fourier-transform/sk-lem-wft-character-integral`,
`lem-fd-character-integral.proof.md`, nontrivial-character and linear-form calculation;
the finite-level expansion is the DAG node's eight-step proof.
(blueprint: lem-fd-character-integral-finite)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option linter.style.haveILetI false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.Etale

/-- Reduction of the integral additive character along the coefficient quotient map.
Source: latest blueprint, `sk-lem-wft-character-integral`, coefficient calculation;
finite-coefficient expansion in the DAG statement.
(blueprint: lem-fd-character-integral-finite) -/
def reducedCharacter (k₀ : Type u) [AddMonoid k₀] (p ell : ℕ) [Fact p.Prime] [Fact ell.Prime]
    (E : Type (u + 1)) [Field E] [Algebra (Padic ell) E]
    [FiniteDimensional (Padic ell) E] (n : ℕ)
    (ψ : AddChar k₀ (Padic.coefficientExtensionIntegers ell E)ˣ) :
    AddChar k₀ (Padic.coefficientExtensionRing ell E n)ˣ :=
  MonoidHom.compAddChar
    (Units.map (Ideal.Quotient.mk (Padic.coefficientExtensionIdeal ell E n)).toMonoidHom) ψ

/-- The finite-field cardinality is invertible in the coefficient quotient when its
characteristic differs from the coefficient prime.
Source: latest blueprint, `lem-fd-character-integral-finite` (blueprint:
lem-fd-character-integral-finite). -/
@[instance_reducible] noncomputable def finiteCard_invertible
    (p ell : ℕ) [Fact p.Prime] [Fact ell.Prime] (hpell : p ≠ ell)
    (k₀ : Type u) [Field k₀] [Fintype k₀] [CharP k₀ p]
    (E : Type (u + 1)) [Field E] [Algebra (Padic ell) E]
    [FiniteDimensional (Padic ell) E] (n : ℕ) (_hn : 1 ≤ n) :
    Invertible (Fintype.card k₀ : Padic.coefficientExtensionRing ell E n) := by
  have h := (Padic.extension_integers_dvr ell E (Padic.coefficientExtensionAbsoluteValue ell E)
    (spectralNorm_extends (K := Padic ell) (L := E))).choose_spec.choose_spec
  have hv : Padic.coefficientExtensionAbsoluteValue ell E (p : E) = 1 := by
    have he := spectralNorm_extends (K := Padic ell) (L := E) (p : Padic ell)
    have hn' : ‖(p : Padic ell)‖ = 1 := Padic.norm_natCast_eq_one_iff.2
      ((Nat.coprime_primes (Fact.out : ell.Prime) (Fact.out : p.Prime)).2 hpell.symm)
    change spectralNorm (Padic ell) E (p : E) = 1
    simpa only [map_natCast, hn'] using he
  have hu : IsUnit (p : Padic.coefficientExtensionIntegers ell E) :=
    (h.2.2.1 _).2 hv
  have hq : IsUnit (p : Padic.coefficientExtensionRing ell E n) := by
    simpa using hu.map (Ideal.Quotient.mk (Padic.coefficientExtensionIdeal ell E n))
  let hcardExists := FiniteField.card (K := k₀) p
  let m : ℕ := (Classical.choose hcardExists : ℕ+)
  have hcard : Fintype.card k₀ = p ^ m := (Classical.choose_spec hcardExists).2
  have hcardUnit : IsUnit (Fintype.card k₀ : Padic.coefficientExtensionRing ell E n) := by
    rw [hcard]
    simpa [hcard] using hq.pow m
  exact hcardUnit.invertible


/-- The ordinary etale character sheaf of the coefficient-presented linear form
`sum_i c_i x_i` on affine r-space over Omega. This is the inverse image of the
q-degree Artin--Schreier projector sheaf along the linear form and the base map.
Source: latest blueprint, `sk-lem-wft-character-integral`, higher-dimension paragraph;
finite-coefficient expansion in the DAG statement.
(blueprint: lem-fd-character-integral-finite) -/
def finiteLinearCharacterSheaf
    (p ell : ℕ) [Fact p.Prime] [Fact ell.Prime] (hpell : p ≠ ell)
    (k₀ : Type u) [Field k₀] [Fintype k₀] [CharP k₀ p]
    (E : Type (u + 1)) [Field E] [Algebra (Padic ell) E]
    [FiniteDimensional (Padic ell) E] (n : ℕ) (hn : 1 ≤ n)
    (ψ : AddChar k₀ (Padic.coefficientExtensionIntegers ell E)ˣ)
    (Ω : Type u) [Field Ω] [Algebra k₀ Ω]
    (r : ℕ) (c : Fin r → Ω) :
    Sheaf (𝔸(ULift.{u} (Fin r); Spec (CommRingCat.of Ω))).smallEtaleTopology
      (ModuleCat.{u + 1} (Padic.coefficientExtensionRing ell E n)) :=
  let A := Padic.coefficientExtensionRing ell E n
  letI : Invertible (Fintype.card k₀ : A) := finiteCard_invertible p ell hpell k₀ E n hn
  let X := 𝔸(ULift.{u} (Fin r); Spec (CommRingCat.of Ω))
  letI : X.Over (Spec (.of k₀)) :=
    ⟨X ↘ Spec (.of Ω) ≫ Spec.map (CommRingCat.ofHom (algebraMap k₀ Ω))⟩
  artinSchreierSheafOf X
    (MonoidHom.compAddChar (Units.coeHom A) (reducedCharacter k₀ p ell E n ψ))
    (∑ i : ULift.{u} (Fin r),
      AffineSpace.coord (Spec (.of Ω)) i *
        (X ↘ Spec (.of Ω)).appTop ((Scheme.ΓSpecIso (.of Ω)).inv.hom (c i.down)))

/-- Compactly supported etale vanishing for a nontrivial finite integral
Artin--Schreier character and a nonzero linear form.
Source: latest blueprint,
`sec-fourier-transform/sk-lem-wft-character-integral/lem-fd-character-integral.proof.md`,
nontrivial-character, linear-form and higher-dimension paragraphs; the finite-level
argument is expanded in the eight proof steps of this DAG node.
(blueprint: lem-fd-character-integral-finite)

Proof: The given open immersion into the proper scheme computes compact support,
independently of the compactification. Since p differs from ell, q is a unit in
A_n. Write the integral character as a nontrivial prime-field character composed
with a scaled trace, using the field-coefficient Artin--Schreier trace comparison,
and reduce this identity to A_n. The corresponding q-degree projector sheaf is
the nontrivial character summand of the prime-degree Artin--Schreier cover.
The compact cohomology of the constant sheaf on the affine line is A_n(-1)[-2]
by the affine-space trace; translations act trivially because the trace is
invariant and invertible. Finite direct image and compact-support composition
identify the compact cohomology of the covering pushforward with that of its
source, equivariantly for deck translations (compact-support base-change pasting).
The character projector therefore acts by the scalar p^{-1} sum_b Psi(-b), which
is zero: the sum is already zero in E by translation reindexing and then in O_E
and A_n by reduction. Thus the nontrivial summand has zero compact cohomology.
Scaling the line by a nonzero coefficient transports this result to every
nonzero one-dimensional linear form. In higher dimension choose a nonzero
coefficient c_i and change coordinates to t=sum_j c_j x_j together with x_j for
j unequal to i; the inverse solves x_i=c_i^{-1}(t-sum_{j≠i}c_j x_j).
The finite-coefficient open tensor comparison, proper projection formula,
compact-support base change and affine-space trace identify integration along
the other r-1 coordinates with the twist and shift (-r+1)[-2r+2]. Hence the
higher-dimensional compact cohomology vanishes too, and the compactification
comparison gives the displayed object on Z. -/
theorem finite_character_integral
    (p ell : ℕ) [Fact p.Prime] [Fact ell.Prime] (hpell : p ≠ ell)
    (k₀ : Type u) [Field k₀] [Fintype k₀] [CharP k₀ p]
    (E : Type (u + 1)) [Field E] [Algebra (Padic ell) E]
    [FiniteDimensional (Padic ell) E] (n : ℕ) (hn : 1 ≤ n)
    (ψ : AddChar k₀ (Padic.coefficientExtensionIntegers ell E)ˣ)
    (Ω : Type u) [Field Ω] [Algebra k₀ Ω] [IsAlgClosed Ω]
    (r : ℕ) (_hr : 1 ≤ r) (c : Fin r → Ω) (hc : c ≠ 0)
    (Z : Scheme.{u}) [Z.Over (Spec (.of Ω))]
    (a : 𝔸(ULift.{u} (Fin r); Spec (CommRingCat.of Ω)) ⟶ Z)
    [IsOpenImmersion a] [IsProper (Z ↘ Spec (CommRingCat.of Ω))]
    (hψ : reducedCharacter k₀ p ell E n ψ ≠ 1) :
    IsZero ((rightDerivedGlobalSections
      (ModuleCat.{u + 1} (Padic.coefficientExtensionRing ell E n)) Z).obj
        (((a)_!open[
          ModuleCat.{u + 1} (Padic.coefficientExtensionRing ell E n)]).mapDerivedCategory.obj
            ((DerivedCategory.singleFunctor _ 0).obj
              (finiteLinearCharacterSheaf p ell hpell k₀ E n hn ψ Ω r c)))) := by
  let X := 𝔸(ULift.{u} (Fin r); Spec (CommRingCat.of Ω))
  let S := Spec (CommRingCat.of Ω)
  let F := finiteLinearCharacterSheaf p ell hpell k₀ E n hn ψ Ω r c
  letI : HasCompactification (X ↘ S) := HasCompactification.affineSpace_over _ S
  letI : Finite (Padic.coefficientExtensionRing ell E n) :=
    Padic.finite_coefficientExtensionRing ell E n hn
  letI : Invertible (Fintype.card k₀ : Padic.coefficientExtensionRing ell E n) :=
    finiteCard_invertible p ell hpell k₀ E n hn
  have hcore : IsZero ((R(X ↘ S)_![ModuleCat.{u + 1}
      (Padic.coefficientExtensionRing ell E n)]).obj
      ((DerivedCategory.singleFunctor _ 0).obj F)) := by
    apply finite_character_integral_affine_core p ell hpell k₀ E n hn
      (reducedCharacter k₀ p ell E n ψ) hψ Ω r _hr c hc F
    rfl
  exact finite_character_integral_compactification_transfer
    (Padic.coefficientExtensionRing ell E n) Ω r F hcore Z a

end AlgebraicGeometry.Etale
