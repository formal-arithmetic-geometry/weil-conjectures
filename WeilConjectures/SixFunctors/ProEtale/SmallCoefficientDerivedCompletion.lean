/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.DerivedCompletionSupplement
public import WeilConjectures.Topology.ProfiniteCondensedRing
public import WeilConjectures.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
import WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalars
public import Mathlib.Algebra.Field.Shrink
public import Mathlib.Algebra.Algebra.Shrink
public import Mathlib.RingTheory.Finiteness.Small

/-!
# Derived completion on the canonical small coefficient presentation

Source: blueprint, sec-proetale-coefficients,
`sk-def-pe-derived-completion/_section.md`, canonical reduction and normalized towers
(blueprint: def-sfb-small-coefficient-derived-completion).

Finite dimensionality makes E small in every scheme universe. The existing continuous
coefficient and Roos constructions are applied to its canonical Shrink presentation.
No second tensor product, quotient tower, or completion construction is introduced.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v

open CategoryTheory

namespace AlgebraicGeometry.ProEtale.SmallAdicCompletion

namespace Coefficients

variable (l : ℕ) [Fact l.Prime] (E : Type v) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- The canonical small presentation, in the scheme universe.
Source: blueprint, finite coefficient presentation
(blueprint: def-sfb-small-coefficient-derived-completion). -/
def field : Type u :=
  letI : Small.{0} E := Module.Finite.small (R := Padic l) (M := E)
  letI : Small.{u} E := small_map (equivShrink.{0} E)
  Shrink.{u} E

/-- The field structure transported along the canonical Shrink equivalence.
Source: blueprint, finite coefficient presentation
(blueprint: def-sfb-small-coefficient-derived-completion). -/
instance fieldField : Field (field.{u} l E) :=
  letI : Small.{0} E := Module.Finite.small (R := Padic l) (M := E)
  letI : Small.{u} E := small_map (equivShrink.{0} E)
  inferInstanceAs (Field (Shrink.{u} E))

/-- The transported p-adic algebra structure.
Source: blueprint, finite coefficient presentation
(blueprint: def-sfb-small-coefficient-derived-completion). -/
instance fieldAlgebra : Algebra (Padic l) (field.{u} l E) :=
  letI : Small.{0} E := Module.Finite.small (R := Padic l) (M := E)
  letI : Small.{u} E := small_map (equivShrink.{0} E)
  inferInstanceAs (Algebra (Padic l) (Shrink.{u} E))

/-- Finite dimensionality is preserved by the canonical small presentation.
Source: blueprint, finite coefficient presentation
(blueprint: def-sfb-small-coefficient-derived-completion). -/
instance fieldFinite : FiniteDimensional (Padic l) (field.{u} l E) :=
  letI : Small.{0} E := Module.Finite.small (R := Padic l) (M := E)
  letI : Small.{u} E := small_map (equivShrink.{0} E)
  inferInstanceAs (FiniteDimensional (Padic l) (Shrink.{u} E))

/-- The canonical algebra equivalence from the small presentation to E.
Source: blueprint, finite coefficient presentation
(blueprint: def-sfb-small-coefficient-derived-completion). -/
def fieldEquiv : field.{u} l E ≃ₐ[Padic l] E :=
  letI : Small.{0} E := Module.Finite.small (R := Padic l) (M := E)
  letI : Small.{u} E := small_map (equivShrink.{0} E)
  Shrink.algEquiv (Padic l) E

/-- The spectral norm on the small presentation.
Source: blueprint, finite coefficient presentation
(blueprint: def-sfb-small-coefficient-derived-completion). -/
abbrev fieldNorm := (Padic.coefficientExtensionAbsoluteValue l (field.{u} l E)).toNormedField

/-- The valuation ring of the small presentation.
Source: blueprint, finite coefficient presentation
(blueprint: def-sfb-small-coefficient-derived-completion). -/
abbrev integers := Padic.coefficientExtensionIntegers l (field.{u} l E)

/-- The continuous condensed valuation ring, with sections C(S, O).
Source: blueprint, continuous coefficients and inverse image
(blueprint: def-sfb-small-coefficient-derived-completion). -/
abbrev integerRing :=
  DerivedNakayama.integerRing l (field.{u} l E)

/-- The continuous finite quotient ring sheaf.
Source: blueprint, continuous coefficients and inverse image
(blueprint: def-sfb-small-coefficient-derived-completion). -/
abbrev quotientRingSheaf (n : ℕ) :=
  DerivedNakayama.quotientRingSheaf l (field.{u} l E) n

/-- The internal finite quotient ring.
Source: blueprint, continuous coefficients and inverse image
(blueprint: def-sfb-small-coefficient-derived-completion). -/
abbrev quotientRing (n : ℕ) :=
  DerivedNakayama.quotientRing l (field.{u} l E) n

/-- The canonical quotient morphism of continuous ring objects.
Source: blueprint, continuous coefficients and inverse image
(blueprint: def-sfb-small-coefficient-derived-completion). -/
abbrev reductionRing (n : ℕ) :=
  DerivedNakayama.reductionRing l (field.{u} l E) n

/-- The quotient with its restricted integral action.
Source: blueprint, continuous coefficients and inverse image
(blueprint: def-sfb-small-coefficient-derived-completion). -/
abbrev quotientModule (n : ℕ) :=
  DerivedNakayama.quotientModule l (field.{u} l E) n

/-- Inverse image from the point on internal modules.
Source: blueprint, continuous coefficients and inverse image
(blueprint: def-sfb-small-coefficient-derived-completion). -/
abbrev pullback (X : Scheme.{u}) :=
  DerivedNakayama.pullback l (field.{u} l E) X

/-- The canonical regular-module comparison under inverse image.
Source: blueprint, continuous coefficients and inverse image
(blueprint: def-sfb-small-coefficient-derived-completion). -/
abbrev regularPullbackIso (X : Scheme.{u}) :=
  DerivedNakayama.regularPullbackIso l (field.{u} l E) X

end Coefficients

variable (l : ℕ) [Fact l.Prime] (E : Type v) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- The pulled-back continuous integral ring.
Source: blueprint, canonical reduction and normalized towers
(blueprint: def-sfb-small-coefficient-derived-completion). -/
abbrev ring (X : Scheme.{u}) :=
  AdicCompletion.ring l (Coefficients.field.{u} l E) X

/-- Internal modules over the pulled-back integral ring.
Source: blueprint, canonical reduction and normalized towers
(blueprint: def-sfb-small-coefficient-derived-completion). -/
abbrev Modules (X : Scheme.{u}) :=
  AdicCompletion.Modules l (Coefficients.field.{u} l E) X

/-- The pulled-back positive-level quotient at exponent n+1.
Source: blueprint, canonical reduction and normalized towers
(blueprint: def-sfb-small-coefficient-derived-completion). -/
abbrev finiteRing (X : Scheme.{u}) (n : ℕ) :=
  AdicCompletion.finiteRing l (Coefficients.field.{u} l E) X n

/-- The actual quotient morphism pulled back from the point.
Source: blueprint, canonical reduction and normalized towers
(blueprint: def-sfb-small-coefficient-derived-completion). -/
abbrev quotient (X : Scheme.{u}) (n : ℕ) :=
  AdicCompletion.quotient l (Coefficients.field.{u} l E) X n

/-- Continuous postcomposition with the consecutive quotient transition.
Source: blueprint, canonical reduction and normalized towers
(blueprint: def-sfb-small-coefficient-derived-completion). -/
abbrev transitionRingSheaf (n : ℕ) :=
  AdicCompletion.transitionRingSheaf l (Coefficients.field.{u} l E) n

/-- The quotient topology on each finite ring of the small presentation.
Source: blueprint, continuous finite coefficients
(blueprint: def-sfb-small-coefficient-derived-completion). -/
abbrev finiteTopology (n : ℕ) :=
  AdicCompletion.finiteTopology l (Coefficients.field.{u} l E) n

/-- The consecutive transition of condensed ring objects.
Source: blueprint, canonical reduction and normalized towers
(blueprint: def-sfb-small-coefficient-derived-completion). -/
abbrev transitionRing (n : ℕ) :=
  AdicCompletion.transitionRing l (Coefficients.field.{u} l E) n

/-- The quotient transition after inverse image.
Source: blueprint, canonical reduction and normalized towers
(blueprint: def-sfb-small-coefficient-derived-completion). -/
abbrev transition (X : Scheme.{u}) (n : ℕ) :=
  AdicCompletion.transition l (Coefficients.field.{u} l E) X n

/-- The tensor-unit quotient map on the point.
Source: blueprint, canonical reduction and normalized towers
(blueprint: def-sfb-small-coefficient-derived-completion). -/
abbrev quotientUnit (n : ℕ) :=
  AdicCompletion.quotientUnit l (Coefficients.field.{u} l E) n

/-- The transition with the integral scalar action.
Source: blueprint, canonical reduction and normalized towers
(blueprint: def-sfb-small-coefficient-derived-completion). -/
abbrev quotientStep (n : ℕ) :=
  AdicCompletion.quotientStep l (Coefficients.field.{u} l E) n

/-- The pulled-back quotient as an integral module.
Source: blueprint, canonical reduction and normalized towers
(blueprint: def-sfb-small-coefficient-derived-completion). -/
abbrev finiteModule (X : Scheme.{u}) (n : ℕ) :=
  AdicCompletion.finiteModule l (Coefficients.field.{u} l E) X n

/-- The canonical tensor-unit map on X.
Source: blueprint, canonical reduction and normalized towers
(blueprint: def-sfb-small-coefficient-derived-completion). -/
abbrev finiteUnit (X : Scheme.{u}) (n : ℕ) :=
  AdicCompletion.finiteUnit l (Coefficients.field.{u} l E) X n

/-- Termwise tensor reduction, used on K-flat representatives.
Source: blueprint, canonical reduction and normalized towers
(blueprint: def-sfb-small-coefficient-derived-completion). -/
abbrev level (X : Scheme.{u}) (n : ℕ) :=
  AdicCompletion.level l (Coefficients.field.{u} l E) X n

/-- The unbounded derived category at positive level n+1.
Source: blueprint, canonical reduction and normalized towers
(blueprint: def-sfb-small-coefficient-derived-completion). -/
abbrev FiniteDerived (X : Scheme.{u}) (n : ℕ) :=
  AdicCompletion.FiniteDerived l (Coefficients.field.{u} l E) X n

/-- Canonical derived extension to positive level n+1.
Source: blueprint, canonical reduction and normalized towers
(blueprint: def-sfb-small-coefficient-derived-completion). -/
abbrev derivedReduction (X : Scheme.{u}) (n : ℕ) :=
  AdicCompletion.derivedReduction l (Coefficients.field.{u} l E) X n

/-- Exact derived restriction from positive level n+1.
Source: blueprint, canonical reduction and normalized towers
(blueprint: def-sfb-small-coefficient-derived-completion). -/
abbrev restrict (X : Scheme.{u}) (n : ℕ) :=
  AdicCompletion.restrict l (Coefficients.field.{u} l E) X n

/-- Consecutive derived extension from exponent n+2 to n+1.
Source: blueprint, canonical reduction and normalized towers
(blueprint: def-sfb-small-coefficient-derived-completion). -/
abbrev finiteExtend (X : Scheme.{u}) (n : ℕ) :=
  AdicCompletion.finiteExtend l (Coefficients.field.{u} l E) X n

/-- Exact restriction along the consecutive quotient.
Source: blueprint, canonical reduction and normalized towers
(blueprint: def-sfb-small-coefficient-derived-completion). -/
abbrev finiteRestrict (X : Scheme.{u}) (n : ℕ) :=
  AdicCompletion.finiteRestrict l (Coefficients.field.{u} l E) X n

/-- The canonical composition comparison for restrictions.
Source: blueprint, canonical reduction and normalized towers
(blueprint: def-sfb-small-coefficient-derived-completion). -/
abbrev restrictComp (X : Scheme.{u}) (n : ℕ) :=
  AdicCompletion.restrictComp l (Coefficients.field.{u} l E) X n

/-- The canonical derived reduction association.
Source: blueprint, canonical reduction and normalized towers
(blueprint: def-sfb-small-coefficient-derived-completion). -/
abbrev reductionComp (X : Scheme.{u}) (n : ℕ) :=
  AdicCompletion.reductionComp l (Coefficients.field.{u} l E) X n

/-- The strict transition on tensor reductions.
Source: blueprint, canonical reduction and Roos construction
(blueprint: def-sfb-small-coefficient-derived-completion). -/
abbrev levelStep (X : Scheme.{u}) (P : CochainComplex (Modules.{u} l E X) ℤ) (n : ℕ) :=
  AdicCompletion.levelStep l (Coefficients.field.{u} l E) X P n

/-- The tensor-unit augmentation at each level.
Source: blueprint, canonical reduction and Roos construction
(blueprint: def-sfb-small-coefficient-derived-completion). -/
abbrev levelUnit (X : Scheme.{u}) (P : CochainComplex (Modules.{u} l E X) ℤ) (n : ℕ) :=
  AdicCompletion.levelUnit l (Coefficients.field.{u} l E) X P n

/-- The termwise product of the strict reduction tower.
Source: blueprint, canonical reduction and Roos construction
(blueprint: def-sfb-small-coefficient-derived-completion). -/
abbrev product (X : Scheme.{u}) (P : CochainComplex (Modules.{u} l E X) ℤ) :=
  AdicCompletion.product l (Coefficients.field.{u} l E) X P

/-- The specified one minus shift endomorphism.
Source: blueprint, canonical reduction and Roos construction
(blueprint: def-sfb-small-coefficient-derived-completion). -/
abbrev oneSubShift (X : Scheme.{u}) (P : CochainComplex (Modules.{u} l E X) ℤ) :=
  AdicCompletion.oneSubShift l (Coefficients.field.{u} l E) X P

/-- The two Roos coordinates in degree i.
Source: blueprint, canonical reduction and Roos construction
(blueprint: def-sfb-small-coefficient-derived-completion). -/
abbrev roosX (X : Scheme.{u}) (P : CochainComplex (Modules.{u} l E X) ℤ) (i : ℤ) :=
  AdicCompletion.roosX l (Coefficients.field.{u} l E) X P i

/-- The differential (dx,(1-s)x-dy).
Source: blueprint, canonical reduction and Roos construction
(blueprint: def-sfb-small-coefficient-derived-completion). -/
abbrev roosD (X : Scheme.{u}) (P : CochainComplex (Modules.{u} l E X) ℤ) (i : ℤ) :=
  AdicCompletion.roosD l (Coefficients.field.{u} l E) X P i

/-- The specified Roos complex.
Source: blueprint, canonical reduction and Roos construction
(blueprint: def-sfb-small-coefficient-derived-completion). -/
abbrev roos (X : Scheme.{u}) (P : CochainComplex (Modules.{u} l E X) ℤ) :=
  AdicCompletion.roos l (Coefficients.field.{u} l E) X P

/-- The product of the tensor-unit maps.
Source: blueprint, canonical reduction and Roos construction
(blueprint: def-sfb-small-coefficient-derived-completion). -/
abbrev unitProduct (X : Scheme.{u}) (P : CochainComplex (Modules.{u} l E X) ℤ) :=
  AdicCompletion.unitProduct l (Coefficients.field.{u} l E) X P

/-- The specified augmentation (c,0).
Source: blueprint, canonical reduction and Roos construction
(blueprint: def-sfb-small-coefficient-derived-completion). -/
abbrev augmentation (X : Scheme.{u}) (P : CochainComplex (Modules.{u} l E X) ℤ) :=
  AdicCompletion.augmentation l (Coefficients.field.{u} l E) X P

/-- The canonical transition between derived reductions.
Source: blueprint, canonical reduction and Roos construction
(blueprint: def-sfb-small-coefficient-derived-completion). -/
abbrev derivedStep (X : Scheme.{u}) (K : DerivedCategory (Modules.{u} l E X)) (n : ℕ) :=
  AdicCompletion.derivedStep l (Coefficients.field.{u} l E) X K n

/-- Completeness is invertibility of the specified K-flat Roos augmentation.
Source: blueprint, derived adic completeness
(blueprint: def-sfb-small-coefficient-derived-completion). -/
def IsDerivedComplete (l : ℕ) [Fact l.Prime] (E : Type v) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (X : Scheme.{u})
    (K : DerivedCategory (Modules.{u} l E X)) : Prop :=
  AlgebraicGeometry.ProEtale.IsDerivedComplete l (Coefficients.field.{u} l E) X K

/-- A tower is normalized when each transition-induced derived extension is invertible.
This is a condition on derived objects, with no ordinary-tensor requirement on cohomology.
Source: blueprint, normalized towers
(blueprint: def-sfb-small-coefficient-derived-completion). -/
def IsNormalized (X : Scheme.{u})
    (M : ∀ n : ℕ, FiniteDerived.{u} l E X n)
    (t : ∀ n : ℕ, M (n + 1) ⟶ (finiteRestrict.{u} l E X n).obj (M n)) : Prop :=
  AdicCompletion.IsNormalized l (Coefficients.field.{u} l E) X M t

end AlgebraicGeometry.ProEtale.SmallAdicCompletion
