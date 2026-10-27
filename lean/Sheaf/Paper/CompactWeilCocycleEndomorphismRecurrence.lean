/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q03
-/
module

public import Sheaf.Paper.TraceFormulaCoefficientConventions
public import Sheaf.SixFunctors.SchemeFrobenius
public import Sheaf.Paper.DerivedPullbackTensorHom
public import WeilConjectures.Compactification.RefinementCategory
public import Sheaf.TraceFormula.CompactFrobeniusTransportComposition
public import Sheaf.SixFunctors.FrobeniusCohomologyTransport
public import Sheaf.Paper.TraceFormulaStrictWeilComplex
public import Sheaf.Paper.IteratedWeilMap
import Sheaf.Paper.IteratedWeilCocycle

/-!
# Recurrence for direct compact-support Weil endomorphisms

Source: main-20261015 blueprint, sec-trace-formula/sk-d-weil,
lem-trf-frobenius-operator-compact-description.proof.md, first two sentences;
expanded coefficient-complex calculation in the docstring of
FrobeniusOperatorCompactDescription.lean, paragraph (4)
(blueprint: lem-trf-compact-weil-cocycle-endomorphism-recurrence).

The coefficient exponent is `n + 1`, covering every positive level. The endomorphisms
use the recorded direct power transports, with one compactification for every power.
The pullback presentation comparison identifies their targets with the domains of the
specified iterated Weil isomorphisms; it introduces no independent comparison map.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme

namespace WeilConjectures
open AlgebraicallyClosedCoefficients

/-- The endomorphism `U_r = H(phi^[r]) tau^(r)` of the actual compact-support
coefficient complex. The first factor is the specified direct power transport from
`compactPowerTransport`, not a recursive degree-one transport. The intervening
`pointPowerPullbackModel` is the recorded change to intrinsic pullback coordinates.
Source: main-20261015 blueprint, compact-description proof, first two sentences;
FrobeniusOperatorCompactDescription.lean, docstring paragraph (4)
(blueprint: lem-trf-compact-weil-cocycle-endomorphism-recurrence). -/
def compactWeilCocycleEndomorphism (D : FiniteFieldDatum.{u})
    (C : D.CoefficientDatum) (E : Padic.FiniteCoefficientFields C.l C.Qbar)
    (X₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    [IsSeparated X₀.hom] (c₀ : Compactification X₀.hom) (n : ℕ)
    (K : (TraceFormulaCoefficientConventions.mk D C E (n + 1) (Nat.succ_pos n)
      X₀).strictWeilComplex) (r : ℕ) (hr : 1 ≤ r) :
    End ((compactPowerCohomology D C.l (Coefficient.{u} C.l C.Qbar E) X₀ c₀ n).obj
      K.obj.carrier) :=
  compactPowerTransport D C.l C.different (Coefficient.{u} C.l C.Qbar E)
      X₀ c₀ n r K.obj.carrier ≫
    (compactPowerCohomology D C.l (Coefficient.{u} C.l C.Qbar E) X₀ c₀ n).map
      ((pointPowerPullbackModel C.l (Coefficient.{u} C.l C.Qbar E) n
        ((End.of (D.geometricGaloisFrobenius X₀)) ^ r)).hom.app K.obj.carrier ≫
        ((TraceFormulaCoefficientConventions.mk D C E (n + 1) (Nat.succ_pos n)
          X₀).iteratedWeilIsomorphism K r hr).hom)

/-- The direct compact-support endomorphisms have the stated degree-one value and
satisfy `U_(r+1) = U_1 ∘ U_r`, as morphisms of the derived coefficient complex.
Lean's `≫` writes composition in the order of traversal.
Source: main-20261015 blueprint, compact-description proof, first two sentences;
FrobeniusOperatorCompactDescription.lean, docstring paragraph (4)
(blueprint: lem-trf-compact-weil-cocycle-endomorphism-recurrence).

Proof:
1. By def-trf-iterated-weil-map the one-factor iterate is phi itself, after the
   specified presentation comparison and the equality g^1 = g. By
   lem-trf-compact-frobenius-transport-composition the direct degree-one transport
   is the degree-one compact transport. Substituting gives the first equality.
2. Fix r >= 1. By lem-trf-compact-frobenius-transport-composition, with M = K,
   tau^(r+1) = H(b_r) tau^(1)_(P_r K) tau^(r), where b_r is the inverse of
   the canonical pullback-composition comparison. All powers retain this same c₀.
3. Apply lem-trf-iterated-weil-cocycle at (1,r). With that same comparison it says
   phi^[r+1] b_r = phi P_1(phi^[r]). Both indices are positive.
4. Put v = phi^[r]. Naturality of the degree-one compact transport of
   def-weil-frobenius-cohomology-transport gives
   H(P_1 v) tau^(1)_(P_r K) = tau^(1)_K H(v).
   K is bounded constructible, and P_r K is too since v is an isomorphism to K.
5. Substituting steps 2, 3 and 4, functoriality of H and associativity give
   U_(r+1) = H(phi) tau^(1)_K H(v) tau^(r)_K = U_1 U_r.
   These are equalities before applying any cohomology functor. -/
theorem compact_weil_cocycle_endomorphism_recurrence (D : FiniteFieldDatum.{u})
    (C : D.CoefficientDatum) (E : Padic.FiniteCoefficientFields C.l C.Qbar)
    (X₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    [IsSeparated X₀.hom] (c₀ : Compactification X₀.hom) (n : ℕ)
    (K : (TraceFormulaCoefficientConventions.mk D C E (n + 1) (Nat.succ_pos n)
      X₀).strictWeilComplex) :
    compactWeilCocycleEndomorphism D C E X₀ c₀ n K 1 (by decide) =
      frobeniusCompactTransportFinite D C.l C.different (Coefficient.{u} C.l C.Qbar E)
          X₀ c₀ n K.obj.carrier ≫
        (compactPowerCohomology D C.l (Coefficient.{u} C.l C.Qbar E) X₀ c₀ n).map
          ((TraceFormulaCoefficientConventions.mk D C E (n + 1) (Nat.succ_pos n)
            X₀).strictWeilFrobenius K).hom ∧
    ∀ (r : ℕ) (hr : 1 ≤ r),
      compactWeilCocycleEndomorphism D C E X₀ c₀ n K (r + 1)
          (Nat.le_trans hr (Nat.le_succ r)) =
        compactWeilCocycleEndomorphism D C E X₀ c₀ n K r hr ≫
          compactWeilCocycleEndomorphism D C E X₀ c₀ n K 1 (by decide) := by
  sorry

end WeilConjectures
