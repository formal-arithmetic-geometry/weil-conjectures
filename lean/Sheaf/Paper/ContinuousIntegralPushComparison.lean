/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A2
-/
module

public import Sheaf.Paper.ContinuousIntegralScalarExact

/-! # Integral localization commutes with bounded qcqs derived pushforward -/

@[expose] public section

universe u
open CategoryTheory Limits
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E]

/-- The specified scalar-extension/pushforward mate is invertible on integral bounded
constructible complexes for a qcqs map.
Source: Hemo--Richarz--Scholbach, Lemma 5.3(1), and Bhatt--Scholze, Lemma 6.8.2.
(blueprint: lem-weil-pbc-continuous-integral-push-comparison).

Proof in words. Express the restricted regular E coefficient module as the sequential
colimit O --ℓ--> O --ℓ--> ..., with nth map a ↦ a/ℓⁿ. The compact-test localization
calculation and exact monoidal inverse image identify this colimit on every scheme.
Tensoring a complex with this coefficient module is therefore its localization telescope.
Exactness of filtered colimits and integralScalarExtension_exact identify derived scalar
extension with this termwise operation. Choose a good truncation of a representative of K
below its lower cohomological bound. Every term of its telescope has this same lower bound.
Apply condensed_qcqs_pushforward_continuity in every cohomological degree. It makes the
natural map from the telescope of Rf_*K to Rf_* of the telescope an isomorphism in every
degree. The map so obtained is the specified derivedPushHom: both are adjoint to the
restriction-of-scalars/pushforward comparison, and on the nth localization leg they are
induced by the same unit and division by ℓⁿ. Homology detects isomorphisms in the derived
category, and the exact faithful restriction functor reflects isomorphisms. No proper base
change theorem or completed pushforward is used. The zero complex and empty schemes give
the same zero-object comparison. -/
theorem integralScalarPushHom_isIso {X Y : Scheme.{u}} (f : X ⟶ Y)
    [QuasiCompact f] [QuasiSeparated f] (K : integralConstructible ℓ E X) :
    IsIso ((derivedPushHom (integralScalarMap ℓ E) f).app K.obj) := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
