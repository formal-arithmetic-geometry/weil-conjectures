/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.TwoColimit

/-!
# Compatibility: descent of `Dᵇc(X, ℚ̄_ℓ)` to finite subextensions

Blueprint `sk-thm-sfb-qlbar-two-colimit`, stated in the form used by the uniform `Ext` bound for
`ℚ̄_ℓ` (blueprint `det-uniform-constructible-ext-rational`).
-/

@[expose] public section

universe u

open CategoryTheory Limits MonObj

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

open Scheme PadicAlgCl

variable (X : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime] [TopologicalSpace.NoetherianSpace X]

/-- Compatibility from blueprint `sk-thm-sfb-qlbar-two-colimit` (objects): every bounded
constructible `ℚ̄_ℓ`-complex is the extension of scalars of a bounded constructible
`E`-complex for some finite subextension `E`. -/
lemma uniformExtBoundCompat_essSurjObj : (constructibleCocone X ℓ).EssSurjObj :=
  constructibleCocone_essSurjObj X ℓ

/-- Compatibility from blueprint `sk-thm-sfb-qlbar-two-colimit` (morphisms): every morphism
between extensions of scalars to `ℚ̄_ℓ` comes from some finite subextension. -/
lemma uniformExtBoundCompat_homSurj : (constructibleCocone X ℓ).HomSurj :=
  constructibleCocone_homSurj X ℓ


end AlgebraicGeometry.ProEtale
