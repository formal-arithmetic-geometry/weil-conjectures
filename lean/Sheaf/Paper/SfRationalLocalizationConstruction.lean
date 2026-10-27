/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group W4
-/
module

public import Sheaf.Paper.SfLocalizationData

import Sheaf.Paper.SfRationalSupportedAdjointTransport

/-! # SfRationalLocalizationConstruction

Source: current blueprint, sec-smooth-purity/sk-prop-sf-localization,
prop-sf-localization-all-stages.proof.md.
(blueprint: lem-sf-rational-localization-construction). -/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u v

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open AlgebraicGeometry AlgebraicGeometry.Scheme

namespace WeilConjectures

/-- Transport one integral supported localization through raw scalar localization.
Source: supported localization proof, (2) and (3), uniqueness of the right adjoint,
and the rational coefficient passage
(blueprint: lem-sf-rational-localization-construction).

Proof: the integral closed and open direct images are the restrictions of the
ordinary completed-ring operations, through I.closed_push and I.open_push.
The canonical completed-coefficient action makes these R-linear exact functors.
The two pullbacks have the exact monoidal shifts of the recorded pullbacks.
Give the exceptional right adjoint the unique shift compatible with the closed
adjunction; adjoint additivity, linearity and exactness then apply. The supported
triangle and orthogonality give its unique natural boundary. Apply
sfRationalSupportedAdjointTransport to these integral functors and adjunctions.
Identify its raw scalar localization with the published rational category, using
the specified tensor Hom coordinates and image triangulation. Uniqueness in
rationalDerivedPullback_existsUnique identifies the two transported pullbacks
with the recorded ones. Its natural functor comparisons and its unit and counit
normalizations give the closed_push, open_push, exceptional, open_pull_localization,
counit_localization, open_unit_localization and unit_localization fields.
The original integral record is retained as the integral field.
-/
theorem sfRationalLocalizationConstruction
    (k : Type u) [Field k] (l : ℕ) [Fact l.Prime] (hl : IsUnit (l : k))
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (X : Scheme.{u}) (t : X ⟶ Spec (.of k))
    [IsSeparated t] [LocallyOfFiniteType t] [QuasiCompact t]
    {Z U : Scheme.{u}} (i : Z ⟶ X) (j : U ⟶ X)
    [IsClosedImmersion i] [IsOpenImmersion j]
    (hij : Set.range j = (Set.range i)ᶜ)
    (I : SfIntegralLocalization l E k hl t i j) :
    Nonempty (SfRationalLocalization l E k hl t i j) := by sorry

end WeilConjectures
