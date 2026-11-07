/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Submission.WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.EtaleOrigin
public import Submission.WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.EtaleReadingUpperShriek

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-!
# The étale reading lands in objects of étale origin

For every bounded constructible condensed `𝒪_E ⧸ ℓⁿ`-complex `M` on `X`, the pro-étale complex
`Φ(M)` is of étale origin (`ProEtale.CondensedRing.etaleOriginReading`): this is
`ProEtale.isEtaleOrigin_of_isConstructible` (blueprint `lem-sf-proetale-constructible-origin`)
at the finite coefficient ring `𝒪_E ⧸ ℓⁿ`.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] (E : Type) [Field E]
  [Algebra E (PadicAlgCl ℓ)] [Algebra ℚ_[ℓ] E] [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)]
  [FiniteDimensional ℚ_[ℓ] E] (n : ℕ)

/-- **The étale reading lands in objects of étale origin**: for every bounded constructible
condensed `𝒪_E ⧸ ℓⁿ`-complex `M` on `X`, the pro-étale complex `Φ(M)` is of étale origin
(`ProEtale.isEtaleOrigin_of_isConstructible`, blueprint
`lem-sf-proetale-constructible-origin`). -/
theorem etaleOriginReading (X : Over (Spec (.of k))) : EtaleOriginReading ℓ E n X := fun M ↦
  isEtaleOrigin_of_isConstructible _ M.property

end AlgebraicGeometry.ProEtale.CondensedRing
