/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NK
-/
module

public import Sheaf.CategoryTheory.SheafTensor
public import WeilConjectures.CategoryTheory.RingObjects.Ab
import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify

/-! # Canonical tensor instance interfaces for abelian sheaves

Source: Weil conjectures blueprint, `sk-def-sfb-sheaf-tensor`, Ab specialization,
and `sk-prop-sf-open-closed-triangle/lem-sfb-modobj-grothendieck.proof.md`,
the fixed-factor tensor hypotheses
(blueprint: def-sfb-abelian-sheaf-tensor-instances).

These definitions expose the existing sheafified tensor over the integers as instances.
They specialize `sfbSheafTensorStructure` and its recorded properties; they construct
no second tensor. Sheafification is transported from the small model of the site.
-/

@[expose] public section

set_option autoImplicit false

universe uC vC w

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

namespace CategoryTheory

/-- Left exact abelian sheafification on the essentially small site, transported from its
small model in the coefficient universe.
Source: blueprint `sk-def-sfb-sheaf-tensor`, Ab specialization, with
sheafification as in `sk-def-sfb-sheaf-tensor`
(blueprint: def-sfb-abelian-sheaf-tensor-instances). -/
noncomputable instance abelianSheafTensorSheafify
    {C : Type uC} [Category.{vC} C] [EssentiallySmall.{w} C]
    (J : GrothendieckTopology C) : HasSheafify J AddCommGrpCat.{w} := by
  let : HasSheafify ((equivSmallModel.{w} C).inverse.inducedTopology J)
      AddCommGrpCat.{w} := GrothendieckTopology.hasSheafify_of_isGrothendieckAbelian _ _
  exact hasSheafifyEssentiallySmallSite J AddCommGrpCat.{w}

/-- The canonical sheafified tensor over the integers of `sk-def-sfb-sheaf-tensor`.
Source: blueprint `sk-def-sfb-sheaf-tensor`, Ab specialization, using
`sk-def-sfb-sheaf-tensor` (blueprint: def-sfb-abelian-sheaf-tensor-instances). -/
noncomputable instance abelianSheafTensorMonoidal
    {C : Type uC} [Category.{vC} C] [EssentiallySmall.{w} C]
    (J : GrothendieckTopology C) : MonoidalCategory (Sheaf J AddCommGrpCat.{w}) :=
  (sfbSheafTensorStructure (A := AddCommGrpCat.{w}) J).monoidal

/-- The symmetry of the same canonical sheaf tensor.
Source: blueprint `sk-def-sfb-sheaf-tensor`, Ab specialization, using
`sk-def-sfb-sheaf-tensor` (blueprint: def-sfb-abelian-sheaf-tensor-instances). -/
noncomputable instance abelianSheafTensorSymmetric
    {C : Type uC} [Category.{vC} C] [EssentiallySmall.{w} C]
    (J : GrothendieckTopology C) : SymmetricCategory (Sheaf J AddCommGrpCat.{w}) :=
  (sfbSheafTensorStructure (A := AddCommGrpCat.{w}) J).symmetric

/-- Closedness of the canonical sheaf tensor, from the recorded properties theorem of
`sk-def-sfb-sheaf-tensor`. Not an instance: it only serves to derive the Prop-valued
additivity below. A right adjoint of a fixed functor; the tensor itself is not chosen.
Source: blueprint `sk-def-sfb-sheaf-tensor`, Ab specialization, using
`sk-def-sfb-sheaf-tensor` (blueprint: def-sfb-abelian-sheaf-tensor-instances). -/
@[instance_reducible]
noncomputable def abelianSheafTensorClosed
    {C : Type uC} [Category.{vC} C] [EssentiallySmall.{w} C]
    (J : GrothendieckTopology C) : MonoidalClosed (Sheaf J AddCommGrpCat.{w}) :=
  (sfbSheafTensor_properties.{uC, vC, w + 1, w, 0, 0}
    (A := AddCommGrpCat.{w}) J).2.1.some

/-- Additivity of the canonical sheaf tensor in each variable (proof step 3).
Source: blueprint `sk-def-sfb-sheaf-tensor`, Ab specialization, using
`sk-def-sfb-sheaf-tensor` (blueprint: def-sfb-abelian-sheaf-tensor-instances). -/
noncomputable instance abelianSheafTensorPreadditive
    {C : Type uC} [Category.{vC} C] [EssentiallySmall.{w} C]
    (J : GrothendieckTopology C) : MonoidalPreadditive (Sheaf J AddCommGrpCat.{w}) :=
  letI := abelianSheafTensorClosed J
  sfbSheafTensor_monoidalPreadditive

/-- Left tensor with a sheaf preserves finite colimits (closedness, proof step 3).
Source: blueprint `sk-def-sfb-sheaf-tensor`, Ab specialization, using
`sk-def-sfb-sheaf-tensor` (blueprint: def-sfb-abelian-sheaf-tensor-instances). -/
noncomputable instance abelianSheafTensorLeftColimits
    {C : Type uC} [Category.{vC} C] [EssentiallySmall.{w} C]
    (J : GrothendieckTopology C) (F : Sheaf J AddCommGrpCat.{w}) :
    PreservesFiniteColimits (tensorLeft F) :=
  ((sfbSheafTensor_properties.{uC, vC, w + 1, w, 0, 0}
    (A := AddCommGrpCat.{w}) J).2.2 F).2.2.1

end CategoryTheory
