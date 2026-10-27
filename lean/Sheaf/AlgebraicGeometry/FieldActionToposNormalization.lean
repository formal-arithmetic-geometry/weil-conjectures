module

public import Sheaf.Paper.FieldActionToposCoefficients

/-! # The normalized field-action topos interface

Source: Bhatt--Scholze Examples 4.1.9--4.1.10 and the normalized free-subsite
construction. (blueprint: def-sfb-field-action-topos-normalization)
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u

namespace AlgebraicGeometry.ProEtale.FieldActionTransport

/-- The existing normalized field-action topos datum, re-exported for scalar transport.
Source: Bhatt--Scholze Examples 4.1.9--4.1.10
(blueprint: def-sfb-field-action-topos-normalization). -/
abbrev FieldActionToposNormalization (k Ω : Type u) [Field k] [Field Ω]
    [Algebra k Ω] [IsSepClosure k Ω] :=
  AlgebraicGeometry.ProEtale.FieldActionTopos.Normalization k Ω

end AlgebraicGeometry.ProEtale.FieldActionTransport
