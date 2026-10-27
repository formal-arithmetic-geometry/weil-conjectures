/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F3
-/
module

public import Sheaf.Paper.ClassicalRawLisseOperations
public import Sheaf.Paper.LissePullbackNormalization
public import Sheaf.Paper.LisseFieldNormalization

/-! # Actual finite-level scalar extension and restriction -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096
universe u v
open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures.ClassicalRawLisse
variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)

/-- Construct the finite scalar and locally closed restriction operations.
Source: Bhatt--Scholze, Proposition 6.8.4(1),(3),(4), Remark 6.8.15
(blueprint: lem-zl-classical-raw-lisse-finite-operations).

Proof: At a coefficient inclusion of ramification e, take at level m the actual
balanced tensor of level (m+e)/e-1 with the target quotient ring. Tensoring a finite
local basis proves finite freeness; base change of the quotient maps proves the
normalization of the resulting system. The adjunction tensor units define the level
units. Their compatibility with transitions induces the integralUnit by the universal
property of the completion cone, with precisely the asserted projection equation.
For restriction, apply the actual etale inverse image levelwise, with its adjunction
unit. The site-comparison adjoint mate induces the map of completion cones, giving
the specified integralUnit and projection equation. Local finite bases prove that
both operations commute with module inverse image and coefficient extension.
Extend their compatible-family maps by scalar localization; the balanced relation
gives the stated fraction formulas, and additivity and functoriality follow on pure
tensors. The prescribed raw realization comparison is obtained from these actual
module comparisons using the normalized lisse pullback and field comparisons of a.
On local generators 1 tensor x the comparison is the completion-cone map just
constructed; this proves ordinary_tensor and normalization. The same construction
on finite stalks and their inverse limit gives the scalar fibre isomorphism. -/
theorem classical_raw_lisse_finite_operations
    (a : LisseRealization.Family D l hl) (b : ContinuousRational.Family.{u} l)
    (s : Family D l hl a b)
    (hr : ∀ (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
      {X Y : LisseRealization.Base D l hl} (f : X.scheme ⟶ Y.scheme),
      Nonempty (LisseRealization.PullNormalized D l hl E f
        (a.realization E X) (a.realization E Y) (a.along E f)))
    (hf : ∀ (E F : Type u) [Field E] [Field F] [Algebra ℚ_[l] E] [Algebra ℚ_[l] F]
      [FiniteDimensional ℚ_[l] E] [FiniteDimensional ℚ_[l] F]
      (i : E →ₐ[ℚ_[l]] F) (X : LisseRealization.Base D l hl),
      Nonempty (LisseRealization.FieldNormalized D l hl E F i X
        (a.realization E X) (a.realization F X) (a.fieldChange E F i X))) :
    Nonempty (Operations D l hl a b s) := by
  sorry

end WeilConjectures.ClassicalRawLisse
