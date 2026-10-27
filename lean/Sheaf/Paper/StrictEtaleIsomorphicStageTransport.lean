/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G3
-/
module

public import Sheaf.Paper.EtaleCoefficientTransportInterfaces

/-!
# Strict étale transport at isomorphic coefficient stages

Source: Zheng, Construction 4.1 and Proposition 2.29(2)
(blueprint: lem-pur-strict-etale-isomorphic-stage-projection).

This is the coefficient-system part of the projection theorem.  It isolates the
construction of the exact transport and its finite-level equivalences from the
compact-support projection assembly.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genInjectivity false
set_option genSizeOfSpec false
set_option genSizeOf false
set_option genCtorIdx false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor SheafOfModules
namespace AlgebraicGeometry
attribute [local instance 5000] strictEtaleSystemDerived strictEtaleLevelDerived

/-- Isomorphic quotient stages admit an exact strict coefficient transport.

Proof: define extension of scalars on each evaluated level using the bijective
ring map, and define the successor arrows by tensor interchange.  The generator
formula for the coefficient change gives the system relations.  Exactness and
the equivalence of each derived level follow from the inverse quotient map;
localization and the universal counits provide the recorded derived and
representative fields.  This is the coefficient-only part of the geometric
construction, before compact-support mates are assembled.
Source: Zheng, Construction 4.1 and Proposition 2.29(2)
(blueprint: lem-pur-strict-etale-isomorphic-stage-transport).
-/
theorem nonempty_strictEtaleCoefficientTransport_of_bijective
    {O O' : Type (u + 1)} [CommRing O] [CommRing O'] {ell : O} {mu : O'}
    {phi : O →+* O'} {index : ℕ →o ℕ}
    (a : StrictEtaleCoefficientChange O O' ell mu phi index)
    (_ha : ∀ n, Function.Bijective (a.ring n))
    {T : Scheme.{u}}
    (PA : StrictEtaleEvaluation T O ell) (PB : StrictEtaleEvaluation T O' mu) :
    ∃ U : StrictEtaleCoefficientTransport a T PA PB,
      ∀ n, (U.level n).derived.IsEquivalence := by
  sorry

end AlgebraicGeometry
