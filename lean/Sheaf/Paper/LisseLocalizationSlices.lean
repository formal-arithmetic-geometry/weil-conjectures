/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F6
-/
module

public import Sheaf.Paper.LisseLocalizationData

/-! # Normalized exact localization on pro-etale slices

Source: Bhatt--Scholze 6.8.2; Stacks 04IX, 03EL, 0941 and 08TC.
(blueprint: lem-tw-lisse-localization-slices).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped TensorProduct ChangeOfRings
open SheafOfModules WeilConjectures.LisseLocalizationInterfaces
attribute [-instance] WeilConjectures.integralOperationsSiteSmall
namespace WeilConjectures.LisseLocalization
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The normalized coefficient, scalar-extension and strict-limit comparisons
on a single pro-etale chart, with both localization models specified in advance.
Source: Bhatt--Scholze 6.8.2; Stacks 04IX, 03EL, 0941 and 08TC
(blueprint: lem-tw-lisse-localization-slices).

Proof: apply completedRingMap_slice to the identity of X and U; retain the integral
and residue isomorphisms, their projection equations and constant-section equations.
Joint injectivity of the completed projections identifies the restricted uniformizer.
Localize this integral isomorphism. Restriction commutes with sheafification, so the
sectionwise map b/t^n ↦ b|U/t^n gives the rational isomorphism, unit equation and
fraction normalization. The slice equivalence and exact module restriction give the
six exactness and additivity fields. Sheafified scalar extension restricts by the
map a tensor m ↦ a|U tensor m|U; its inverse uses the inverse coefficient comparison.
Tensor generation and the sheafification unit prove naturality and the tensor equation.
Map this ordinary comparison termwise and descend through quasi-isomorphisms.
Uniqueness of the two universal derived pairs identifies their counits, proving the
derived comparison and its stated normalization. The slice strict-derived-limit
theorem supplies exact restrictions, universal limits and every projection equation.
Compare its derived limits with the K-injective strict-tower Roos realizations by
uniqueness of right derived pairs; the counit normalization transports the Roos
projections and triangles, giving StrictLimitRealizes on both sites.
All constructions are on arbitrary site objects; no finite-type chart is used. -/
theorem localization_slice {X : Scheme.{u}} (dx : LocalizationData l E X)
    (U : X.ProEt) (du : LocalizationData l E U.left) :
    ∃ c : SliceCoefficients l E U,
      Nonempty (SliceLocalization l E dx U du c) ∧
      SliceLimitCompatibility U (X.adicLisseForget.obj (integralRing l E X)) := by
  sorry

end WeilConjectures.LisseLocalization
