/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
-/
module

public import Sheaf.Paper.PurityDivisorClass
public import Sheaf.Paper.SupportedCupFunctoriality

/-! # Pullback of arbitrary normalized divisor families

Source: blueprint Cartier Kummer map, Cartier-preserving pullback;
Stacks 03PL and 0A45 (blueprint: lem-pur-normalized-divisor-family-pullback).
-/
@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry
namespace WeilConjectures.PurityFiniteSetting

/-- Any two fully normalized divisor families are compatible with supported etale
pullback on a Cartesian square whose two immersions are Cartier.

Source: blueprint lem-amb-cartier-kummer-map, Cartier-preserving pullback paragraph;
lem-pur-cartier-class-agreement, Step 7
(blueprint: lem-pur-normalized-divisor-family-pullback).

Proof: apply `Etale.supported_kummer_boundary_pullback` to `C.classOf i hI` and
`C'.classOf i' hI'` with their full relative normalizations. Use the roots-normalized
transport `p1DecompositionTwistTransport` in degree one. The closed constant exchange
agrees with `functorialCupExchange` because both preserve the constant quotient;
its uniqueness is `functorialCupExchange_existsUnique`. Apply Ext.hom to the Ext
square. The identities `Ext.comp_hom`, `Ext.mk₀_hom`, and
`Ext.mapExactFunctor_hom` identify the square with the derived pullback formula after
cancelling the degree-zero image of the source exchange. The target comparison is
the same roots-normalized twist comparison. Finally `C.realizes` and `C'.realizes`
identify its endpoints with the recorded Hom classes. This argument retains the
relative section, applies to empty divisors, and uses only Cartier preservation. -/
theorem normalizedDivisorFamily_pullback (P : PurityFiniteSetting.{u})
    {D T D' T' : Scheme.{u}} (a : T ⟶ Spec (.of P.field.k))
    (a' : T' ⟶ Spec (.of P.field.k))
    (C : P.DivisorEtaleClasses T) (C' : P.DivisorEtaleClasses T')
    (hC : P.DivisorEtaleNormalized T a C)
    (hC' : P.DivisorEtaleNormalized T' a' C')
    (i : D ⟶ T) (i' : D' ⟶ T') [IsClosedImmersion i] [IsClosedImmersion i']
    (h : T' ⟶ T) (w : D' ⟶ D) (sq : ChosenCartesianSquare w i' i h)
    (hI : i.ker.IsInvertible) (hI' : i'.ker.IsInvertible) :
    P.functorialCupPullback false i i' h w sq a 2 1 (C.homClassOf i hI) =
      C'.homClassOf i' hI' := by
  sorry

end WeilConjectures.PurityFiniteSetting
