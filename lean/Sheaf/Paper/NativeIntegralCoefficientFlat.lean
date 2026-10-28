/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Y2
-/
module

public import Sheaf.Paper.LocallyFiniteAdicRealizationData

/-! # Flatness of the normalized integral-to-native coefficient map

Source: Bhatt--Scholze, Lemma 6.8.2 and Proposition 6.8.14(2).
(blueprint: lem-sf-native-integral-coefficient-flat).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [local irreducible] HasDerivedCategory.standard

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme
open scoped Obj

namespace WeilConjectures.LocallyFiniteAdicRealization

/-- Ordinary extension along the normalized integral coefficient map preserves finite limits.

Source: Bhatt--Scholze, Lemma 6.8.2 and Proposition 6.8.14(2).
(blueprint: lem-sf-native-integral-coefficient-flat).

Proof in words: transport through C.integral, which is a ring isomorphism.
The normalized integral inclusion is sheaf localization at a uniformizer: its
normalization identifies it with the continuous-function inclusion, and C.localization
identifies the localization with the rational coefficient sheaf. Localization is flat.
The normalized rational inclusion is the finite-field inclusion into the locally finite
algebraic-closure coefficient. On the profinite basis the latter coefficient is the
filtered union of finite extensions. Each finite extension is finite free over the given
field, using a continuous coordinate basis. Exactness of filtered colimits of module
sheaves shows that this inclusion is flat. The section-action equivalence retains these
scalar maps and tensors, so its ordinary scalar extension is exact. Composing these
three exact extensions gives extension along C.integralMap by balanced tensor
associativity. Colimits are also preserved by the scalar-extension adjunction. Empty
schemes and zero modules use the same sheaf-local argument, without nonempty sections.
-/
theorem nativeIntegralCoefficient_flat
    (l : ℕ) [Fact l.Prime] (X : Scheme.{u}) [IsNoetherian X]
    [IsCommMonObj (abRing l X)]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (i : E →ₐ[Padic l] PadicAlgCl l) (C : CoefficientPresentation l X E i) :
    PreservesFiniteLimits (pbcExtend (C.integralMap l X)) := by sorry

end WeilConjectures.LocallyFiniteAdicRealization
