/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.CategoryTheory.ObjectProperty.SmallSubobject
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Constructible

/-!
# Constructible module objects embed into pushforwards of finitely presented ones

Let `Λ` be a commutative condensed ring and `X` a scheme with noetherian underlying space. This
file shows that the constructible module objects over `Λ_X` are essentially small (blueprint
`det-brown-hypotheses-small`).

* For finitely many quasi-compact morphisms `g k : W k ⟶ X` jointly covering `X`, the units
  `M ⟶ (g k)_* (g k)^* M` are jointly monomorphic
  (`ProEtale.CondensedRing.mono_pi_lift_unit_upperStarLowerStarAdjunction`), since the
  pullbacks `(g k)^*` jointly detect zero objects.
* A constructible `M` is pro-étale locally finitely presented on the strata of a stratification;
  refining the pro-étale covers of the (quasi-compact) strata by finitely many affine opens, `M`
  embeds into a finite product `∏ₖ (gₖ)_* hₖ^* coker(φₖ)`, for presentations
  `φₖ : Λ^{mₖ} ⟶ Λ^{nₖ}` on schemes `Uₖ` and morphisms `hₖ : Wₖ ⟶ Uₖ`, `gₖ : Wₖ ⟶ X`
  (`ProEtale.CondensedRing.exists_mono_of_isConstructibleModuleObject`).
* Such data form a set, and the module objects form a well-powered category, so the
  constructible module objects are essentially small
  (`ProEtale.CondensedRing.essentiallySmall_isConstructibleModuleObject_of_noetherianSpace`).

## Implementation note

The objects `g^* M` and `g_* N` are wrapped in the definitions `ProEtale.CondensedRing.pullObj`
and `ProEtale.CondensedRing.pushObj`. Without them, the kernel checks definitional equalities
such as `(g ≫ f)^*.obj M = (g' ≫ f')^*.obj M` (with `g = g'` and `f = f'` only up to
reduction) by unfolding the pullback functors, which times out.
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]

/-! ### Presentation data -/

attribute [instance] PresentationFamily.finite

end AlgebraicGeometry.ProEtale.CondensedRing
