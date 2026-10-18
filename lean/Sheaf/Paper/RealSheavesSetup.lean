/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q158
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.NumberTheory.Padics.PadicNumbers
public import Mathlib.Analysis.Complex.Basic
public import Sheaf.AlgebraicGeometry.PureDimension
public import WeilConjectures.AlgebraicGeometry.BaseChangeConventions
public import WeilConjectures.Mathlib.FieldTheory.Finite.Basic
public import WeilConjectures.PointCount
public import WeilConjectures.AlgebraicGeometry.Curve

/-!
# Fields, curves and Frobenius for real sheaves

Source: blueprint main-20261015, sec-purity-real-sheaves/sk-d-real-setup,
Definition d-real-setup, order 2920 (blueprint: d-real-setup).

The field choices, curve predicate, closed-point notation and affine-open predicate
use the existing field, scheme, pure-dimension, base-change and Frobenius definitions.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v w

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace RealSheaves

set_option linter.checkUnivs false in
/-- The field and coefficient choices of the chapter, with a plain field embedding into `ℂ`.
There is no continuity or surjectivity requirement on this embedding.
Source: blueprint main-20261015, d-real-setup, first paragraph (blueprint: d-real-setup). -/
structure Setup where
  p : ℕ
  p_prime : p.Prime
  a : ℕ
  a_pos : 1 ≤ a
  k₀ : Type u
  [baseField : Field k₀]
  [baseFintype : Fintype k₀]
  card_eq : Fintype.card k₀ = p ^ a
  k : Type u
  [closureField : Field k]
  [closureAlgebra : Algebra k₀ k]
  [closure : IsAlgClosure k₀ k]
  l : ℕ
  [l_prime : Fact l.Prime]
  l_ne_p : l ≠ p
  Qbar : Type v
  [coefficientField : Field Qbar]
  [coefficientAlgebra : Algebra ℚ_[l] Qbar]
  [coefficientClosure : IsAlgClosure ℚ_[l] Qbar]
  iota : Qbar →+* ℂ

attribute [instance] Setup.baseField Setup.baseFintype Setup.closureField
  Setup.closureAlgebra Setup.closure Setup.l_prime Setup.coefficientField
  Setup.coefficientAlgebra Setup.coefficientClosure

/-- The fixed cardinality `q = p^a`.
Source: blueprint main-20261015, d-real-setup, first paragraph (blueprint: d-real-setup). -/
abbrev Setup.q (D : Setup.{u, v}) : ℕ := D.p ^ D.a

/-- Scalar extension to the chosen algebraic closure, using the recorded fibre product.
Source: blueprint main-20261015, d-real-setup, curve paragraph (blueprint: d-real-setup). -/
abbrev Setup.geometricCurve (D : Setup.{u, v}) (C₀ : Scheme.{u})
    [C₀.Over (Spec (.of D.k₀))] : Scheme.{u} :=
  pullback (C₀ ↘ Spec (.of D.k₀))
    (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))

/-- Precisely the chapter's curve convention: nonempty, separated, smooth and finite type,
of pure dimension one, and connected after extension to the chosen algebraic closure.
Source: blueprint main-20261015, d-real-setup, curve paragraph (blueprint: d-real-setup). -/
def Setup.IsCurve (D : Setup.{u, v}) (C₀ : Scheme.{u})
    [C₀.Over (Spec (.of D.k₀))] : Prop :=
  Nonempty C₀ ∧ IsSeparated (C₀ ↘ Spec (.of D.k₀)) ∧
    Smooth (C₀ ↘ Spec (.of D.k₀)) ∧ LocallyOfFiniteType (C₀ ↘ Spec (.of D.k₀)) ∧
    QuasiCompact (C₀ ↘ Spec (.of D.k₀)) ∧ C₀.IsPureDimension 1 ∧
    ConnectedSpace (D.geometricCurve C₀)

/-- Closed-point degree `e_x = [κ(x) : k₀]`, using the recorded residue-degree definition.
Source: blueprint main-20261015, d-real-setup, closed points (blueprint: d-real-setup). -/
abbrev Setup.closedPointDegree (D : Setup.{u, v}) (C₀ : Scheme.{u})
    [C₀.Over (Spec (.of D.k₀))] (x : closedPoints C₀) : ℕ :=
  (C₀ ↘ Spec (.of D.k₀)).residueDegree x.1

/-- The local cardinality notation `q_x = q^(e_x)`.
Source: blueprint main-20261015, d-real-setup, closed points (blueprint: d-real-setup). -/
abbrev Setup.closedPointCardinality (D : Setup.{u, v}) (C₀ : Scheme.{u})
    [C₀.Over (Spec (.of D.k₀))] (x : closedPoints C₀) : ℕ :=
  D.q ^ D.closedPointDegree C₀ x

/-- Geometric Frobenius on the chosen algebraic closure, reusing the inverse of arithmetic
Frobenius, which raises elements to `#k₀ = q`.
Source: blueprint main-20261015, d-real-setup, Frobenius paragraph (blueprint: d-real-setup). -/
abbrev Setup.frobenius (D : Setup.{u, v}) : D.k ≃ₐ[D.k₀] D.k :=
  FiniteField.geometricFrobeniusAlgEquivOfAlgebraic D.k₀ D.k

/-- The local geometric Frobenius on any chosen algebraic closure of `κ(x)`.
The finite residue field is supplied by the existing closed-point finiteness theorem,
so the caller need not assume its finiteness separately. The underlying arithmetic
Frobenius raises elements to `#κ(x) = q_x`.
Source: blueprint main-20261015, d-real-setup, Frobenius paragraph (blueprint: d-real-setup). -/
def Setup.localFrobenius (D : Setup.{u, v}) (C₀ : Scheme.{u})
    [C₀.Over (Spec (.of D.k₀))] [LocallyOfFiniteType (C₀ ↘ Spec (.of D.k₀))]
    (x : closedPoints C₀) (Ω : Type w) [Field Ω] [Algebra (C₀.residueField x.1) Ω]
    [IsAlgClosure (C₀.residueField x.1) Ω] : Ω ≃ₐ[C₀.residueField x.1] Ω :=
  letI := ((C₀ ↘ Spec (.of D.k₀)).residueFieldAlgebraMap x.1).toAlgebra
  letI := (C₀ ↘ Spec (.of D.k₀)).finite_residueField_of_isClosed x.1 x.2
  letI := Module.finite_of_finite D.k₀ (M := C₀.residueField x.1)
  letI := Fintype.ofFinite (C₀.residueField x.1)
  FiniteField.geometricFrobeniusAlgEquivOfAlgebraic (C₀.residueField x.1) Ω

/-- An affine open is a nonempty open subscheme isomorphic over the base field to the
spectrum of a finitely generated base algebra. The algebra structure and the equation
on structure maps make the isomorphism an isomorphism over `k₀`.
Source: blueprint main-20261015, d-real-setup, final paragraph (blueprint: d-real-setup). -/
def Setup.IsAffineOpen (D : Setup.{u, v}) {C₀ U₀ : Scheme.{u}}
    [C₀.Over (Spec (.of D.k₀))] [U₀.Over (Spec (.of D.k₀))] (j : U₀ ⟶ C₀) : Prop :=
  Nonempty U₀ ∧ IsOpenImmersion j ∧
    j ≫ (C₀ ↘ Spec (.of D.k₀)) = (U₀ ↘ Spec (.of D.k₀)) ∧
    ∃ (A : Type u) (_ : CommRing A) (_ : Algebra D.k₀ A),
      Algebra.FiniteType D.k₀ A ∧
      ∃ e : U₀ ≅ Spec (.of A),
        e.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap D.k₀ A)) =
          (U₀ ↘ Spec (.of D.k₀))

/-- The chosen finite field has the stated characteristic p.
Source: blueprint main-20261015, d-real-setup, first paragraph (blueprint: d-real-setup).
Proof: FiniteField.card writes the cardinality as a positive power of the prime
ringChar k_0. Compare with card_eq = p^a; both exponents are positive. Unique prime
factorization forces ringChar k_0 = p. -/
theorem Setup.ringChar_eq (D : Setup.{u, v}) : ringChar D.k₀ = D.p := by
  sorry

/-- The existing Weil-sheaf API's coefficient-prime instance, derived from the datum's
l != p and its characteristic equality, with no extra mathematical assumption.
Source: blueprint main-20261015, d-real-setup, first paragraph (blueprint: d-real-setup). -/
instance Setup.coefficientCharFact (D : Setup.{u, v}) : Fact (ringChar D.k₀ ≠ D.l) :=
  ⟨fun h ↦ D.l_ne_p (h.symm.trans D.ringChar_eq)⟩

/-- A nonempty open in a chapter curve has the ordinary separated finite-type curve structure.
This supplies the structure needed by the existing Weil fundamental representation API;
it adds no hypothesis to the chapter's curve convention.
Source: blueprint main-20261015, d-real-setup, curve convention, and d-real-boundary,
nonempty open subcurve (blueprint: d-real-setup).
Proof: The finite-type scheme over the finite field is Noetherian. Hence its open subspace
is quasi-compact, so restriction of the structure morphism is again of finite type.
Separatedness restricts to an open subscheme. Pure dimension one gives ambient dimension
one: every irreducible closed subset lies in an irreducible component, whose dimension is
one by the definition. The open embedding induces an embedding of chains of irreducible
closed subsets by taking their closures, so its Krull dimension is at most one. These are
exactly the four fields of AlgebraicGeometry.IsCurve. -/
theorem Setup.openIsCurve (D : Setup.{u, v}) (C₀ : Scheme.{u})
    [C₀.Over (Spec (.of D.k₀))] (hC : D.IsCurve C₀)
    (U₀ : C₀.Opens) (hU : Nonempty U₀) :
    AlgebraicGeometry.IsCurve (U₀.toScheme ↘ Spec (.of D.k₀)) := by
  sorry

end RealSheaves
