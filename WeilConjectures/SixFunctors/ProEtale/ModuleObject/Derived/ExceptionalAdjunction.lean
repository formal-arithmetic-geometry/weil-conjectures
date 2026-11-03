/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ExceptionalInverseImage
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.DerivedConstructibleLowerShriek

/-! # Exceptional adjunction for the chosen compactification

Source: literature/blueprint/latest/blueprint/sec-six-functors-basics/
sk-thm-existence/def-sfb-dc-upper-shriek-adjunction.md
(blueprint: def-sfb-dc-upper-shriek-adjunction).

The chosen lower and upper shrieks use the same compactification `c_f`. Their adjunction is
`Adjunction.comp` applied to the open-immersion adjunction and the chosen adjunction for its
proper pushforward. An adjunction supplies the left- and right-adjoint assertions directly.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]
  (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k]
  [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
  {X Y : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  (H : PreservesBoundedConstructiblePushforwards Λ k) (f : X ⟶ Y)

/-- The adjunction `Rf_! ⊣ Rf^!` is the compactification adjunction evaluated at the recorded
chosen compactification `c_f`. Its data are the composite of `i_! ⊣ Li^*` and the chosen
`Rp_* ⊣ Rp^!`, in that order. Consequently its `.isLeftAdjoint` and `.isRightAdjoint` express
that the chosen lower shriek is a left adjoint and the chosen upper shriek is a right adjoint.
The preservation input for the proper leg is obtained by evaluating `H` on that leg.

Source: literature/blueprint/latest/blueprint/sec-six-functors-basics/
sk-thm-existence/def-sfb-dc-upper-shriek-adjunction.md, entire definition
(blueprint: def-sfb-dc-upper-shriek-adjunction). -/
noncomputable def boundedConstructibleExceptionalAdjunction
    [(exceptionalInverseImageProperPushforward Λ f
      (H (exceptionalInverseImageCompactification f).overG)).IsLeftAdjoint] :
    boundedConstructibleLowerShriekOfPreserves Λ ℓ H f ⊣
      boundedConstructibleUpperShriekOfRightAdjoint Λ ℓ f
        (H (exceptionalInverseImageCompactification f).overG) :=
  (boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction Λ ℓ
    (exceptionalInverseImageCompactification f).overI).comp
    (Adjunction.ofIsLeftAdjoint (exceptionalInverseImageProperPushforward Λ f
      (H (exceptionalInverseImageCompactification f).overG)))

end AlgebraicGeometry.ProEtale.CondensedRing
