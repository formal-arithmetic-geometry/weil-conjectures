/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.TwistedPullbackReductionData

/-! # Normalized signed Tate-line reduction

Source: blueprint integral-adjunction-bijection, Purity paragraph.
(blueprint: lem-sp-twisted-pullback-tate-reduction).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.ProEtale
namespace WeilConjectures.SpTwistedPullback

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- The ordinary and derived signed Tate reductions with their prescribed formulas.
Source: blueprint integral-adjunction-bijection, Purity paragraph; Stacks 03EK,
07A4; Bhatt--Scholze 3.4.12.
(blueprint: lem-sp-twisted-pullback-tate-reduction).

Proof: the completed Tate line is the scalar extension of the compatible root
system. Reduce its defining quotient map to obtain first, sending 1 tensor x
to 1 tensor x; this gives first_unit. Apply signedLineComparison to this first
comparison. The zero power is multiplication, positive powers are reassociated
balanced tensor products, and negative powers are the dual comparison carrying
phi tensor c to the functional x tensor t mapped to residue(phi(x))*c*t.
These formulas give signed and signed_normalized. Identify ordinary scalar
extension with the recorded tensor-extension presentation by its universal
property. Its generator formula gives ordinary_normalized. Every signed power
is locally free of rank one, hence flat; its degree-zero complex is K-flat.
Define level to be the composite in level_formula: the single-complex
localization comparison, reduction evaluation, the K-flat reduction counit,
and ordinary. Each factor is an isomorphism. This construction works for zero,
positive and negative powers and for the empty scheme. -/
theorem twistedPullbackTateReduction (X : Scheme.{u})
    [∀ x : X, Invertible (l : X.residueField x)] :
    Nonempty (TateReduction l E X) := by sorry

end WeilConjectures.SpTwistedPullback
