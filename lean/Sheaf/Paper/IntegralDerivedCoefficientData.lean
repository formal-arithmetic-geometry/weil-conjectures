/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q35
-/
module

public import Sheaf.Paper.DerivedNakayamaResolution

/-!
# Integral derived coefficient data

Source: blueprint main-20261015, sec-six-functors-basics/sk-cor-int-compactness-ii,
coefficient setup used by `det-cor-int-compactness-ii-extension-zero`
(blueprint: def-sfb-integral-derived-coefficient-data).

The declarations below are canonical names for the coefficient ring, its unbounded derived
category on a scheme, and its derived reduction. Their data is delegated to the definitions in
`DerivedNakayamaResolution`; this module introduces no second coefficient construction.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory
open AlgebraicGeometry Scheme

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- The condensed integral coefficient ring used by the integral six-functor statements.
Source: coefficient setup in `sk-cor-int-compactness-ii`
(blueprint: def-sfb-integral-derived-coefficient-data). -/
abbrev integralCoefficientRing (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] :
    Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1} :=
  DerivedNakayama.integerRing l E

/-- The ordinary unbounded derived category of integral module objects on a scheme.
Source: coefficient setup in `sk-cor-int-compactness-ii`
(blueprint: def-sfb-integral-derived-coefficient-data). -/
abbrev integralDerived (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (X : Scheme.{u}) :=
  DerivedNakayama.Derived l E X

/-- Derived reduction modulo the canonical uniformizer-power quotient.
Source: coefficient setup in `sk-cor-int-compactness-ii`
(blueprint: def-sfb-integral-derived-coefficient-data). -/
abbrev integralReductionFunctor (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (X : Scheme.{u})
    (n : ℕ) : integralDerived l E X ⥤ integralDerived l E X :=
  DerivedNakayama.reductionFunctor l E X n

end AlgebraicGeometry.ProEtale.CondensedRing
