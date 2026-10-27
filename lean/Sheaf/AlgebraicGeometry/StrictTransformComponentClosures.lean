/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Z9
-/
module

public import WeilConjectures.Compactification.StrictTransform
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.Topology.KrullDimension

import WeilConjectures.Compactification.StrictTransformBlowup
import WeilConjectures.Blowup.Proper
import WeilConjectures.RingTheory.FiniteTypeDomainDimensionTrdeg
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.RingTheory.Spectrum.Prime.Topology

/-! # Component closures in a blowup

Source: Stacks Project, Divisors, Tags 0804 and 080E; Varieties, Tag 0A21.
This isolates steps 4--5 of the component-rigidity argument in ILO VIII 2.3.13.
(blueprint: lem-trf-strict-transform-component-closures).
-/

@[expose] public section
set_option autoImplicit false

universe u
open CategoryTheory

namespace AlgebraicGeometry.HilbertSamuel

/-- The components of a blowup are exactly the closures of the unchanged parts of the
original components that meet the complement of the centre. Each such closure has the
original component's dimension. No condition on components contained in the centre is
imposed: these have empty unchanged part and contribute no component.

Source: Stacks Project, Divisors, Tags 0804 and 080E; Varieties, Tag 0A21;
ILO VIII 2.3.13, p.94, component argument steps 4--5.
(blueprint: lem-trf-strict-transform-component-closures).

Proof:
1. Finite type over the field makes X Noetherian, with finitely many irreducible
   components. Every affine ideal is finitely generated. The blowup is proper and thus
   finite type; identify it with the scheme-theoretic strict transform by Tag 080E.
2. The strict transform is the scheme-theoretic closure of the unchanged open. That
   open is reduced, so its scheme-theoretic closure is reduced, and its underlying set
   is its topological closure. Over the complement of the centre the projection is an
   isomorphism. In particular the unchanged open is dense in the strict transform.
3. Intersect each original component W with this complement and lift it along that
   isomorphism. If nonempty, this is an irreducible component of the unchanged open.
   Its closure is irreducible. The finitely many such closures cover the strict
   transform, because closure commutes with finite unions. No one contains another:
   restriction to the unchanged open would give containment between two distinct
   components there. They are therefore exactly the irreducible components upstairs.
4. Give a surviving component and its closure their reduced induced scheme structures.
   They are integral and finite type over the field. Their nonempty unchanged opens
   are isomorphic over the field, identifying their function fields. On a nonempty
   affine open, the dimension equals the transcendence degree of its fraction field
   by finiteType_domain_ringKrullDim_eq_trdeg. Every nonempty affine open in an integral
   scheme locally of finite type over a field has that same dimension (Tag 0A21).
   Thus the component dimensions agree. Empty X, the unit ideal and the zero ideal
   give respectively no components, the identity blowup, and the empty blowup. -/
theorem strictTransform_component_closures {k : Type u} [Field k] {X : Scheme.{u}}
    (q : X ⟶ Spec (.of k)) [IsReduced X]
    [LocallyOfFiniteType q] [QuasiCompact q] (I : X.IdealSheafData) :
    (∀ W' : Set (I.strictTransform (𝟙 X)),
      W' ∈ irreducibleComponents (I.strictTransform (𝟙 X)) ↔
        ∃ W : Set X, W ∈ irreducibleComponents X ∧
          (W \ (I.support : Set X)).Nonempty ∧
          W' = closure
            (strictTransformToSource (𝟙 X) I.blowupMap I.support.compl ⁻¹'
              (W \ (I.support : Set X)))) ∧
    ∀ W : Set X, W ∈ irreducibleComponents X → (W \ (I.support : Set X)).Nonempty →
      topologicalKrullDim
          (closure (strictTransformToSource (𝟙 X) I.blowupMap I.support.compl ⁻¹'
            (W \ (I.support : Set X)))) = topologicalKrullDim W := by sorry

end AlgebraicGeometry.HilbertSamuel
