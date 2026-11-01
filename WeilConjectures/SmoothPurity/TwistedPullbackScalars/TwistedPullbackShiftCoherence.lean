/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SmoothPurity.TwistedPullbackScalars.TwistedPullbackScalarShifts

/-! # Shift coherence of the twisted pullback scalar families

Source: blueprint sec-smooth-purity/sk-thm-purity-transport, purity transport,
shift and no-extra-sign clauses of the base-change coherence
(blueprint: def-pur-twisted-pullback-shift-coherence).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option genInjectivity false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genCtorIdx false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Endofunctor AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures.TwistedPullbackScalars
variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (L : Type u) [Field L] [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
  (i : E →ₐ[Padic l] L)
variable {X X' Y Y' : Scheme.{u}}
  [∀ x : X, Invertible (l : X.residueField x)]
  [∀ x : X', Invertible (l : X'.residueField x)]
  [∀ y : Y, Invertible (l : Y.residueField y)]
  [∀ y : Y', Invertible (l : Y'.residueField y)]



attribute [local irreducible] D rationalDerivedPullback

section Final
variable (Ω : Type u) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]

set_option maxHeartbeats 1000000 in
-- Elaborating the twelve component types expands the same composite functors repeatedly.
/-- Canonical D-shifts at the two output schemes, together with all seven shifted
comparison equations. The integral normalization is part of ShiftData.
Source: purity transport, shift and no-extra-sign clauses
(blueprint: def-pur-twisted-pullback-shift-coherence). -/
structure ShiftCoherence (u : X' ⟶ X) (f : X ⟶ Y) (f' : X' ⟶ Y')
    (v : Y' ⟶ Y) (d : ℕ) where
  atX : ∀ R : Fields l Ω, ShiftData l R.val X d
  atX' : ∀ R : Fields l Ω, ShiftData l R.val X' d
  qX : ShiftCompatible l Ω (qFamily l Ω X d) (fun R ↦ (atX R).rationalShift)
  qX' : ShiftCompatible l Ω (qFamily l Ω X' d) (fun R ↦ (atX' R).rationalShift)
  pu : ShiftCompatible l Ω (pFamily l Ω u) (fun R ↦ fieldRationalPullShift l R.val u)
  pf : ShiftCompatible l Ω (pFamily l Ω f) (fun R ↦ fieldRationalPullShift l R.val f)
  pf' : ShiftCompatible l Ω (pFamily l Ω f') (fun R ↦ fieldRationalPullShift l R.val f')
  pv : ShiftCompatible l Ω (pFamily l Ω v) (fun R ↦ fieldRationalPullShift l R.val v)
  pU : ShiftCompatible l Ω (compositeFamily l Ω u f)
    (fun R ↦ twoPullShift l R.val u f)
  pV : ShiftCompatible l Ω (compositeFamily l Ω f' v)
    (fun R ↦ twoPullShift l R.val f' v)
  af : ShiftCompatible l Ω (aFamily l Ω f d)
    (fun R ↦ twistedPullShift l R.val f d (atX R).rationalShift)
  af' : ShiftCompatible l Ω (aFamily l Ω f' d)
    (fun R ↦ twistedPullShift l R.val f' d (atX' R).rationalShift)
  ra : ShiftCompatible l Ω (rAFamily l Ω u f d)
    (fun R ↦ leftRouteShift l R.val u f d (atX R).rationalShift)
  rb : ShiftCompatible l Ω (rBFamily l Ω f' v d)
    (fun R ↦ rightRouteShift l R.val f' v d (atX' R).rationalShift)

end Final
end WeilConjectures.TwistedPullbackScalars
