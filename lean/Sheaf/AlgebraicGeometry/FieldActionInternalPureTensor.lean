module

public import Sheaf.CategoryTheory.InternalSectionTensorComparison

/-! # Internal pure tensors for field-action transport

Source: Stacks Project, Modules on Sites, Tag 03EK; the field-action scalar transport
node uses the same internal balanced pairing.
(blueprint: def-sfb-field-action-internal-pure-tensor)
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u v w
open CategoryTheory CategoryTheory.MonoidalCategory

namespace AlgebraicGeometry.ProEtale.FieldActionTransport

/-- The existing internal relative pure tensor, re-exported at the field-action boundary.
Source: Stacks Tag 03EK (blueprint: def-sfb-field-action-internal-pure-tensor). -/
abbrev fieldActionInternalPureTensor
    {C : Type v} [Category.{w} C] (J : GrothendieckTopology C)
    [UnivLE.{max v w, u}] [HasSheafify J AddCommGrpCat.{u}]
    [(J.W (A := AddCommGrpCat.{u})).IsMonoidal]
    (R : Sheaf J AddCommGrpCat.{u}) [MonObj R] [IsCommMonObj R]
    (M N : Mod (Sheaf J AddCommGrpCat.{u}) R) (U : Cᵒᵖ)
    (x : M.X.obj.obj U) (y : N.X.obj.obj U) : (M ⊗ N).X.obj.obj U :=
  CategoryTheory.InternalAbelianSheafModule.comparison_internalTmul J R M N U x y

end AlgebraicGeometry.ProEtale.FieldActionTransport
