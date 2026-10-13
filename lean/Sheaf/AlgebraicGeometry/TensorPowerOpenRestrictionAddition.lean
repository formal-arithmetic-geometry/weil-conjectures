/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group U3
-/
module

public import Sheaf.AlgebraicGeometry.TensorPowerSectionOpenRestrictionN

/-! # Addition of tensor powers under open restriction

Source: Stacks Project, Modules, Tag 01CD, iterated tensor-pullback comparison.
-/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory MonoidalCategory

namespace AlgebraicGeometry.Scheme.Modules

/-- The recursive power comparison intertwines addition of exponents on pure tensors
of arbitrary sections of the two powers. No section of L is fixed.
Source: Stacks Project, Modules, Tag 01CD, tensor-pullback comparison.
(blueprint: lem-sc-tensor-power-open-restriction-addition).

Proof: First use the pure-tensor characterization of openRestrictionTensorIso and
uniqueness in the sheaf tensor universal property to establish naturality and
associator coherence. For unitor coherence, the unit comparison is the structure-ring
isomorphism, and the unitor multiplies a section by its scalar; restriction transports
this scalar through the same ring isomorphism. Induct on n in tensorPowAddIso.
For n = 0 its inverse is the left unitor followed by the exponent equality transport;
the just established unitor coherence gives the result for every scalar and section.
For n + 1 expand its inverse into the associator, tensor of the identity with the
previous addition inverse, and exponent equality transport. Associator coherence and
the inductive hypothesis identify the two composites as sheaf morphisms. Evaluate
that equality on tmulSection z w over V to obtain the displayed formula. The sheaf
universal property, rather than generation of global sections by pure tensors,
extends the checks to all sections of the powers. Equality transport commutes with
restriction by elimination of the exponent equality. This also covers zero modules,
the empty open, and either exponent zero. -/
theorem openRestrictionTensorPowIso_inv_add {X Y : Scheme.{u}} (j : Y ⟶ X)
    [IsOpenImmersion j] (L : X.Modules) (n b : ℕ) (V : Y.Opens)
    (z : Γ((L.restrict j).tensorPow n, V))
    (w : Γ((L.restrict j).tensorPow b, V)) :
    ((L.tensorPow (n + b)).restrictAppIso j V).hom
        ((openRestrictionTensorPowIso j L (n + b)).inv.app V
          (((L.restrict j).tensorPowAddIso n b).inv.app V (tmulSection z w))) =
      (L.tensorPowAddIso n b).inv.app (j ''ᵁ V)
        (tmulSection
          (((L.tensorPow n).restrictAppIso j V).hom
            ((openRestrictionTensorPowIso j L n).inv.app V z))
          (((L.tensorPow b).restrictAppIso j V).hom
            ((openRestrictionTensorPowIso j L b).inv.app V w))) := by
  sorry

end AlgebraicGeometry.Scheme.Modules
