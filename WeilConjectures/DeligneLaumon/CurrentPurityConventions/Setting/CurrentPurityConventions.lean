/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
public import WeilConjectures.AlgebraicGeometry.PurityTransport.Coefficient.TransportCoefficients
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ExceptionalInverseImageCurrent
public import WeilConjectures.AlgebraicGeometry.Internal.InternalSignedTateTwist
public import WeilConjectures.AlgebraicGeometry.IntegralCtfEqualsBc
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedCoefficientUnitConstructible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.DetSfCompBaseChangeDefs
public import WeilConjectures.PoincareDuality.ProjectionFormula
public import WeilConjectures.SmoothPurity.FiniteFieldDatum.FrobeniusDetailed
public import Mathlib.Algebra.CharP.CharAndCard
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-!
# Current purity coefficient conventions

Source: literature/blueprint/latest/blueprint/part-six-operations/sec-six-functors/
sec-n-change/sk-prop-qlbar-two-colimit/def-pur-conventions.md, all five paragraphs, corrected by
Wei Yang #1441, item 27 (blueprint: def-pur-conventions).

All categories below are the published full subcategories of the ordinary derived
category of internal modules over p_X^* Lambda. The coefficient presentation is the
existing PurityTransport.Coefficient: its finite constructor accepts every finite
commutative ell-primary ring. The distinguished quotients are only notation for
integral reduction. The integer and rational constructors are the E = Q_ell cases.
The coefficient comparisons and purity transport are theorems about these categories.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.ProEtale
open AlgebraicGeometry.ProEtale.CondensedRing AlgebraicGeometry.ProEtale.PurityTransport
open scoped CategoryTheory.Obj

namespace WeilConjectures.CurrentPurityConventions

/-- The global datum, coefficient prime and a presentation of one of A, O_E, E or Qbar.
A finite presentation includes its finite carrier and a positive annihilating power;
it need not arise from a valuation-ring quotient. Finite subextensions use the fixed
PadicAlgCl representative of the coefficient datum's algebraic closure.
Source: Coefficients, Wei Yang #1441 item 27 (blueprint: def-pur-conventions). -/
structure Setting where
  field : FiniteFieldDatum.{u}
  coefficients : field.CoefficientDatum
  coefficient : Coefficient coefficients.l

namespace Setting

variable (P : Setting.{u})

/-- The existing commutative condensed ring. Integral and rational rings use continuous
functions; the closure uses functions valued in a finite subextension.
Source: Coefficients (blueprint: def-pur-conventions). -/
abbrev ring := P.coefficient.obj.{u} P.coefficients.l

/-- Lambda_X is the inverse image from the profinite point, with its transported ring data.
Source: Coefficients (blueprint: def-pur-conventions). -/
abbrev coefficientSheaf (X : Scheme.{u}) := condensedRingObj P.ring X

/-- The ordinary unbounded derived category of internal Lambda_X-modules.
Source: Coefficients (blueprint: def-pur-conventions). -/
abbrev derived (X : Scheme.{u}) := P.coefficient.derived P.coefficients.l X

/-- Bounded complexes with constructible cohomology, with their ambient morphisms.
Source: Coefficients (blueprint: def-pur-conventions). -/
abbrev boundedConstructible (X : Scheme.{u}) := ConstantModelBoundedConstructible P.ring X

/-- The full subcategory additionally imposing finite Tor amplitude. This condition
is retained at arbitrary finite A, including nonregular A.
Source: Coefficients (blueprint: def-pur-conventions). -/
abbrev constructibleFiniteTor (X : Scheme.{u}) := P.coefficient.ctf P.coefficients.l X

/-- Total derived module inverse image, using the actual coefficient pullback map.
Source: Operations (blueprint: def-pur-conventions). -/
abbrev pullback {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  (CondensedRing.upperStar P.ring f).leftDerivedFunctor

/-- Total derived direct image, right adjoint to the derived inverse image.
Source: Operations (blueprint: def-pur-conventions). -/
abbrev directImage {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  (CondensedRing.lowerStar P.ring f).rightDerivedFunctor

/-- The ordinary relative derived tensor, with its published monoidal structure.
Source: Operations (blueprint: def-pur-conventions). -/
abbrev tensor (X : Scheme.{u}) := CondensedRing.derivedTensor P.ring X

/-- Compact support is the specified proper/open compactification composite.
Source: Operations (blueprint: def-pur-conventions). -/
abbrev compactSupport {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) :=
  rightDerivedLowerShriekOfCompactification P.ring c

/-- The proper exchange mate on the literal pullback square. The open comparison
and the proper/open composite are the public dependency's specified maps.
Source: Operations (blueprint: def-pur-conventions). -/
abbrev properExchange {Z Y Y' : Scheme.{u}} (p : Z ⟶ Y) (v : Y' ⟶ Y) :=
  detSfProperBaseChangeMap P.ring p v

/-- The positive Tate line supplied by the existing root-tower construction. At finite
A it is the root module tensored with A at a positive annihilating exponent.
Source: Twists (blueprint: def-pur-conventions). -/
abbrev firstTwist (X : Scheme.{u}) := P.coefficient.firstLine P.coefficients.l X

/-- Signed Tate lines use tensor powers, the coefficient unit at zero, and duals
at negative integers, through the published section/internal-module equivalence.
Source: Twists (blueprint: def-pur-conventions). -/
abbrev twistLine (X : Scheme.{u}) (m : ℤ) :=
  spInternalSignedTwist X (P.coefficientSheaf X) (P.firstTwist X) m

/-- K(m) is exactly derived tensor with Lambda_X(m) placed in degree zero.
Source: Twists, displayed formula (blueprint: def-pur-conventions). -/
abbrev twist (X : Scheme.{u}) (K : P.derived X) (m : ℤ) :=
  spInternalComplexTwist X (P.coefficientSheaf X) (P.firstTwist X) K m

/-- Certificate for the already constructed coefficient presentation.
Source: coefficient list and Brown hypotheses (blueprint: def-pur-conventions). -/
abbrev coefficientAdmissible (ell : ℕ) [Fact ell.Prime] (c : Coefficient ell) :
    IsLocalizingAdmissibleCoefficient ell (c.obj.{u} ell) := by
  cases c with
  | finite A fin n hA =>
    let : TopologicalSpace A := ⊥
    let : DiscreteTopology A := discreteTopology_bot A
    exact Or.inl ⟨A, inferInstance, inferInstance, inferInstance, inferInstance,
      fin, ⟨n + 1, fun x ↦ by simp only [nsmul_eq_mul, Nat.cast_pow, hA, zero_mul]⟩,
      ⟨Iso.refl _⟩⟩
  | integers => exact Or.inr (Or.inl ⟨Iso.refl _⟩)
  | rationals => exact Or.inr (Or.inr (Or.inl ⟨Iso.refl _⟩))
  | integral E => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨E, ⟨Iso.refl _⟩⟩))))
  | rational E => exact Or.inr (Or.inr (Or.inr (Or.inl ⟨E, ⟨Iso.refl _⟩⟩)))
  | closure => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨Iso.refl _⟩))))

/-- The specified Brown adjunction, restricted to Dctf. All characteristic and
cohomological-dimension inputs are derived from the global datum. No ambient
exceptional adjoint, flatness of A over an annihilating ring, or uniform bound over A
is assumed. The right adjoint is determined by this adjunction to the fixed left one.
Source: Operations, sk-thm-existence (3)--(4) (blueprint: def-pur-conventions). -/
def exceptionalData
    {X Y : Over (Spec (.of P.field.k))}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    (f : X ⟶ Y) : CurrentConstructibleExceptionalData P.ring f := by
  classical
  let : Fintype P.field.k₀ := Fintype.ofFinite _
  let : Fact P.field.p.Prime := ⟨P.field.prime⟩
  let : CharP P.field.k₀ P.field.p := charP_of_card_eq_prime_pow (f := P.field.a)
    (by simpa only [Nat.card_eq_fintype_card] using
      P.field.card_base.trans P.field.cardinality_eq)
  let : CharP P.field.k P.field.p := charP_of_injective_algebraMap' P.field.k₀ P.field.p
  let : Fact (ringChar P.field.k).Prime :=
    ⟨(ringChar.eq P.field.k P.field.p).symm ▸ P.field.prime⟩
  let : Fact (ringChar P.field.k ≠ P.coefficients.l) :=
    ⟨(ringChar.eq P.field.k P.field.p).symm ▸ P.coefficients.different.symm⟩
  exact currentConstructibleExceptionalData P.ring P.coefficients.l P.field.k
    (Or.inr (IsAlgClosure.isAlgClosed P.field.k₀)) f
      (coefficientAdmissible P.coefficients.l P.coefficient)

/-- The coefficient complex, the regular module placed in degree zero.
Source: Coefficients and dualizing objects (blueprint: def-pur-conventions). -/
abbrev coefficientUnit (X : Scheme.{u}) : P.derived X :=
  constantCoefficientObject P.ring X

/-- The full-subcategory coefficient unit, retaining the actual degree-zero complex.
Source: dualizing objects (blueprint: def-pur-conventions). -/
def constructibleUnit (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X] :
    P.constructibleFiniteTor X :=
  ⟨P.coefficientUnit X, constantCoefficientObject_mem P.ring X⟩

/-- Omega_Y,Lambda = Ra^! Lambda, for the structure morphism of the given
separated finite-type scheme; it uses precisely the specified restricted Brown functor.
Source: Frobenius and dualizing objects (blueprint: def-pur-conventions). -/
def dualizing
    (Y : Over (Spec (.of P.field.k)))
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom] :
    P.constructibleFiniteTor Y.left := by
  let S := Spec (.of P.field.k)
  let T : Over S := Over.mk (𝟙 S)
  letI : LocallyOfFiniteType T.hom := inferInstanceAs (LocallyOfFiniteType (𝟙 S))
  letI : QuasiCompact T.hom := inferInstanceAs (QuasiCompact (𝟙 S))
  letI : IsSeparated T.hom := inferInstanceAs (IsSeparated (𝟙 S))
  exact (P.exceptionalData (Over.homMk Y.hom : Y ⟶ T)).right.obj
    (P.constructibleUnit S)

/-- The geometric Frobenius is the actual inverse arithmetic field Frobenius on the
geometric fibre. Its action on roots is the published pullback-of-units map.
Source: Frobenius normalization (blueprint: def-pur-conventions). -/
abbrev geometricFrobenius (Y₀ : Over (Spec (.of P.field.k₀)))
    [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom] := P.field.geometricFrobenius Y₀

end Setting

end WeilConjectures.CurrentPurityConventions
