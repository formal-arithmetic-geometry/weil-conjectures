/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.AdicNormalizedPurity.AdicNormalizedPuritySystems
import WeilConjectures.SixFunctors.FiniteExceptional.FiniteExceptional
import WeilConjectures.SmoothPurity.PurityFiniteSetting.Reduction.FiniteReductionOfPurity

/-! # The exceptional quotient normalization is the actual transition mate -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace WeilConjectures.AdicNormalizedPurity

variable (D : FiniteFieldDatum.{u}) (C : D.CoefficientDatum)
  (E : IntermediateField (Padic C.l) C.Qbar) [FiniteDimensional (Padic C.l) E]
  {X Y : Scheme.{u}}
  [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
  [IsSeparated (X ↘ Spec (.of D.k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
  [IsSeparated (Y ↘ Spec (.of D.k))]
  (f : X ⟶ Y) [f.IsOver (Spec (.of D.k))]
  [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
  (d : ℕ) [SmoothOfRelativeDimension d f]

/-- The finite exceptional coefficient comparison followed by the normalized input
map transposes to the transition of the actual exceptional coefficient system.

Source: latest blueprint, smooth-purity transport coefficient-change proof (1),
`det-sp-tower-gamma` and `det-sp-reduction-compatibilities` (1), (3);
original normalized-purity-lift node, proof step 3.
(blueprint: lem-pur-adic-exceptional-normalization-mate).

Proof: express the actual etale system right adjoint transition using its adjunction
Hom bijection. Its transpose is the compact-support coefficient comparison followed
by the finite counit and the input quotient normalization. The finite exceptional
comparison is characterized by this same counit equation. The site-coordinate and
intrinsic-realization isomorphisms used in purAdicExceptionalEvaluation preserve
that equation. Injectivity of the Hom bijection therefore equates the two transposes.
Undo the coordinate isomorphisms and the identity-on-sections quotient restriction
comparison. This is precisely the displayed heterogeneous equality. Equal indices
reduce to the identity quotient and its unit; the argument also applies to zero
objects and the empty scheme. No arbitrary comparison of endpoints is chosen. -/
theorem exceptional_normalization_mate
    (K : DerivedCategory (scalarReductionSource C.l E Y))
    (hK : finiteTorConstructibleIntegral C.l E Y K) {m n : ℕ} (h : n ≤ m) :
    HEq (((purAdicFiniteSetting D C E m).finiteReductionAdjunction (n + 1)
        (Nat.succ_pos n) (Nat.add_le_add_right h 1) X).homEquiv _ _
          (exceptionalNormalization D C E f d K hK h))
        (exceptionalTransition D C E f d K hK h ≫
          (purAdicQuotientRestrictionIso D C E X h).hom.app _) := by sorry

end WeilConjectures.AdicNormalizedPurity
