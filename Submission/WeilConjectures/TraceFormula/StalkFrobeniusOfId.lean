/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Submission.WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Sections
public import Submission.WeilConjectures.TraceFormula.BaseChange.WeilObject
public import Submission.WeilConjectures.TraceFormula.WeilIdentityStructureOfId

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-!
# The Frobenius on the stalks of a module object with the identity Weil structure

A module object `M` on a scheme `X` over `Spec k` is a Weil sheaf for the identity of `X`, with
the identity structure `(𝟙)^* M ≅ M` (`ProEtale.CondensedRing.WeilSheaf.ofId`). For the base
`X = Spec k`, at a geometric point `x̄ : Spec k̄ ⟶ Spec k`, the `(n + 1)`-st Frobenius of the
stalk `x̄^* M` acts on the global sections `𝟙_ ⟶ x̄^* M` by pullback along `σⁿ⁺¹`
(`ProEtale.CondensedRing.comp_frobeniusStalk_ofId_str_hom`): it sends `v` to
`𝟙_ ≅ (σⁿ⁺¹)^* 𝟙_ ⟶ (σⁿ⁺¹)^* x̄^* M ≅ (σⁿ⁺¹ ≫ x̄)^* M = x̄^* M`
(`ProEtale.CondensedRing.upperStarSectionMap`).

## Implementation notes

The transports along equalities of morphisms are written as `eqToHom` of objects
(`congrArg (fun s ↦ s^* M)`), and the identities `g = 𝟙` are never substituted: comparing the
components of transports of pullback functors along different equalities makes the kernel
unfold the pullbacks.
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory Endofunctor

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k]

section OfId

variable {X : Over (Spec (.of k))}

end OfId

section Identity

variable {Y : Scheme.{u}}
  (M : CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
    (condensedRingObj (Profinite.padicAlgClRingObj ℓ) Y))

end Identity

section Point

variable {X : Over (Spec (.of k))} (hX : ∀ g : X ⟶ X, g.left = 𝟙 X.left)
  (M : CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology X.left) Ab.{u + 1})
    (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X.left))



end Point

section Stalk

variable {S Y : Scheme.{u}}
  (M : CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
    (condensedRingObj (Profinite.padicAlgClRingObj ℓ) Y))

end Stalk

/-- The isomorphism `σ^* ≅ 𝟭` over a separably closed point is, at the unit, the inverse of the
unit comparison of `σ^*`, written with the unit in the form of the type of `ε`. -/
lemma upperStarIsoIdOfIsSepClosed_inv_app_tensorUnit {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (σ : Spec (.of Ω) ⟶ Spec (.of Ω)) :
    (upperStarIsoIdOfIsSepClosed (Profinite.padicAlgClRingObj ℓ) σ).inv.app
        𝟙ₘ =
      (Functor.Monoidal.εIso (σ)^*⟦Profinite.padicAlgClRingObj ℓ⟧).hom := by
  have e : (upperStarIsoIdOfIsSepClosed (Profinite.padicAlgClRingObj ℓ) σ).app
      𝟙ₘ =
        (Functor.Monoidal.εIso (σ)^*⟦Profinite.padicAlgClRingObj ℓ⟧).symm :=
    Iso.ext (upperStarIsoIdOfIsSepClosed_hom_app_unit _ σ)
  exact congrArg Iso.inv e

section Stalk

variable {S Y : Scheme.{u}}
  (M : CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
    (condensedRingObj (Profinite.padicAlgClRingObj ℓ) Y))

end Stalk

section PointStalk


end PointStalk

end AlgebraicGeometry.ProEtale.CondensedRing
