module

public import Sheaf.Paper.GeometricSectionsAdjunction

/-! # Underlying set functors of normalized geometric sections

Source: Stacks Tags 00YV and 03D7; the geometric section adjunction supplies the
underlying set functors used by scalar transport.
(blueprint: def-sfb-geometric-section-functors)
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u

namespace AlgebraicGeometry.ProEtale.FieldActionTransport

/-- The existing field-module underlying set functor.
Source: Stacks Tag 00YV (blueprint: def-sfb-geometric-section-functors). -/
abbrev fieldActionFieldSets (k : Type u) [Field k]
    (R : CategoryTheory.CondensedBar.Ring.{u}) :=
  AlgebraicGeometry.ProEtale.GeometricSectionsAdjunction.fieldSets k R

/-- The existing action-module underlying set functor.
Source: Bhatt--Scholze Example 4.1.10 (blueprint: def-sfb-geometric-section-functors). -/
abbrev fieldActionActionSets (k Ω : Type u) [Field k] [Field Ω]
    [Algebra k Ω] [IsSepClosure k Ω]
    (R : CategoryTheory.CondensedBar.Ring.{u}) :=
  AlgebraicGeometry.ProEtale.GeometricSectionsAdjunction.actionSets k Ω R

/-- The existing action-underlying functor in the normalized small model.
Source: Bhatt--Scholze Example 4.1.10 (blueprint: def-sfb-geometric-section-functors). -/
abbrev fieldActionActionUnderlying (k Ω : Type u) [Field k] [Field Ω]
    [Algebra k Ω] [IsSepClosure k Ω] :=
  AlgebraicGeometry.ProEtale.GeometricSectionsAdjunction.actionUnderlying k Ω

end AlgebraicGeometry.ProEtale.FieldActionTransport
