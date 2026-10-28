/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group D9
-/
module

public import Sheaf.SixFunctors.CoefTowerEvaluationPairingData
public import Sheaf.Paper.CompactSupportNativeSystemEvaluation

/-! # Ordinary quotient-module operations determined by scalar restriction -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- The ordinary open and proper functors of a pairing system are the native
quotient-module operations.

Source: prop-coef-integral-dualizing, second proof paragraph, scalar restriction
before taking compact support; Stacks 03DI and 03D2.
(blueprint: lem-coef-pairing-native-operations).

Proof: at each positive level, restriction from the constant quotient ring sheaf
A_n to constant R-module sheaves is fully faithful. A map linear over R is linear
over A_n: locally every section of the quotient ring lifts to a constant R scalar,
and sheaf separatedness descends the scalar law. The same argument for each
vertical slice, with the existing horizontal maps, proves full faithfulness for
strict systems. Native open extension commutes with this restriction by its
extension-by-zero adjunction, and native direct image does so by its section
formula. Compose these restriction comparisons with G.openRestriction and
G.properRestriction, and lift the resulting natural isomorphisms through the
fully faithful restriction functors. Naturality and both inverse equations are
reflected by faithfulness. These are comparisons of ordinary functors, before
localizing or taking inverse limits. The proof includes the zero module, empty
open, identity maps, and the first quotient. -/
theorem coefPairing_native_operations
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (S : CoefficientDerivedSystemCalculus l E X) (G : CoefPairingSystem l E c S) :
    ∃ (j : G.openModules ≅ ProEtale.VaryingRing.extension
        (compactSupportSystemLevel l E) (compactSupportSystemQuotient l E) c.i),
      Nonempty (G.properModules ≅ ProEtale.VaryingRing.push
        (compactSupportSystemLevel l E) (compactSupportSystemQuotient l E) c.g) := by sorry

end WeilConjectures
