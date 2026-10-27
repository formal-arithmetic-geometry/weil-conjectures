/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K9
-/
module

public import Sheaf.Paper.CondensedERealizationDefinitions

/-! # Ordered exchange for a normalized realization system

Source: Bhatt--Scholze, Proposition 6.8.14(2) and Remark 6.8.15.
(blueprint: lem-weil-pbc-condensed-e-system-exchange)
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
namespace WeilConjectures

/-- The ordered exchange comparison for any normalized realization system.
Source: Bhatt--Scholze, Remark 6.8.15; Stacks Project, Tags 099N and 0E48.
(blueprint: lem-weil-pbc-condensed-e-system-exchange)

Proof. For each square, conjugate the ordered ambient completed exchange by the
specified pull and push comparisons. The fully faithful integral inclusion lifts this
natural transformation uniquely, giving its required ambient normalization. Form the
integral pullback square using the specified compositors and equality of composite
morphisms. Its right mate is the same transformation: the normalized units, counits
and compositors rewrite its ambient image to the ordinary exchange followed by the
completion units. The completed-exchange unit equation rewrites the ordered formula
to the same expression. On complete constructible inputs the completion unit is
invertible, so cancel it. Tensor localization preserves composition and sends each
unit, compositor, and counit to its tensor with one. The rational mate is consequently
one tensor the constructed integral exchange. Finally the system's unit and counit
comparison laws and its composition law identify its realization with the continuous
mate: composition coherence identifies the pullback square; naturality moves the
comparison maps through it; the counit equations give the mate equality by adjunction.
No exchange map is claimed invertible. The argument uses only the displayed laws of
the supplied system and also covers zero objects and empty squares. -/
theorem condensedE_realization_system_exchange
    (l : ℕ) [Fact l.Prime] (E : Type u) [NormedField E] [NormedAlgebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] (k : Type u) [Field k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ l)] (D : CondensedERealization.Data l E k) :
    Nonempty (CondensedERealization.Exchange l E k D) := by
  sorry

end WeilConjectures
