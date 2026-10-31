/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.PurIntegralTower.PurStrictIntegralExchangeData

/-! # PurIntegralCompletedCoherence -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe t
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

/-- The strict identity and pasting equations reconstruct to the specified completed
compact-support comparisons.

Source: constituent compatibility, strict integral normalization steps 5--6,
9--12 and 15 (blueprint: lem-pur-integral-completed-coherence).

Proof: apply functorial derived inverse limit to the strict identity and horizontal
pasting equations, retaining their order. The normalized direct-image/limit and
open/limit comparisons commute with the quotient augmentation, so the outside
comparisons are exactly completedPullId and completedPullComp. Adjacent comparison
isomorphisms cancel. Open extension and proper image preserve completeness, and
completed pullback is complete by quotient reconstruction; these give the
existential proof arguments in the identity and horizontal clauses. They are
proofs of properties of already specified objects, not chosen corner maps. For
vertical pasting apply inverse limit to strict proper/open interchange and the
compatible-tower composition comparison. The retained compatible etale-origin
witnesses make both composition maps invertible. The same unit normalizations
identify all four outside arrows with cbcExchange and cbcTowerCompositionMap.
Naturality cancels the intermediate reconstruction comparisons and yields the
stated vertical equation. No origins are needed for identity or horizontal
pasting; only the vertical inversion retains them. All operations commute with
identity maps and zero objects, including empty schemes and empty ideal tuples. -/
theorem purIntegralCompletedCoherence (P : WeilConjectures.PurityFiniteSetting.{t}) :
    PurIntegralCompletedCoherence (pbcIntegralDatum P.coefficients.l P.extension)
      (Spec (.of P.field.k)) := by sorry

end AlgebraicGeometry.Scheme
