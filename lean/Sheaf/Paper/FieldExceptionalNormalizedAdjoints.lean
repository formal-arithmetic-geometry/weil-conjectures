/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M9
-/
module

public import Sheaf.Paper.FieldExceptionalSystemLaws

/-! # Normalized tower adjunctions for exceptional coefficient comparison

The geometric domain and adjunction step, before comparison laws are asserted.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.integralOperationsCommHasDerivedCategory
attribute [-instance] WeilConjectures.integralOperationsSiteSmall
attribute [-instance] WeilConjectures.integralOperationsAbSheafify
attribute [-instance] WeilConjectures.integralOperationsAbLocallyBijective

universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme WeilConjectures

namespace AlgebraicGeometry.ProEtale.FieldExceptionalSystem

open FieldShriekSystem
variable (P : PurityFiniteSetting.{u})

/-- The actual tower adjunctions restrict to normalized constructible towers and
retain the counit-normalized finite evaluations and right-adjoint quotient formula.
This only supplies the adjunction data; it asserts no field-extension comparison law.

Source: latest blueprint, sk-lem-sp-field-extension-towers.proof.md (1)--(2),
using det-sp-tower-gluing (3) and det-sp-tower-gamma (3).
(blueprint: lem-sp-field-exceptional-normalized-adjoints).

Proof: For each coefficient field apply tower_gluing on the full uniform constructible
finite-Tor category. Transport the compact-support adjunction from its canonical
compactification to the fixed one by the counit-preserving proper/open comparison.
The section-preserving realizations in D.coordinates identify that category with the
recorded sequence-site category. tower_gamma proves that both adjoints preserve
normalization. Restrict the functors, unit and counit to the full normalized
subcategories: the triangle identities remain the same equations. Finite evaluation
of a normalized object is constructible with finite Tor amplitude by its defining
uniform bounds. Finite derived scalar extension preserves these properties for any
map of the finite quotient rings. field_scalar_normalized_systems gives the scalar
domain for each inclusion of fields, including ramified ones. These facts give a.
Use the finite right adjoints and their actual ordinary-etale realizations from
reductionExceptional_isIso. Uniqueness of representing pairs identifies them with the
finite adjoints of tower_gluing. Its counit-preserving left and right comparisons
supply A, including leftNormalized and AdjunctionEvaluationNormalized. Its quotient
transpose formula says that the reduction of the right adjoint equals the finite
quotient counit mate followed by the finite right adjoint of the input reduction;
substituting the finiteComponent definition gives rightReductionLaw. The chosen
section-identity quotient coordinates fix every reassociation. No arbitrary family
of derived arrows is lifted and no equality is detected by evaluation. -/
theorem field_exceptional_normalized_adjoints
    (X Y : Scheme.{u}) [X.Over (Spec (.of P.field.k))] [Y.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
    [QuasiCompact (X ↘ Spec (.of P.field.k))] [IsSeparated (X ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y ↘ Spec (.of P.field.k))] [IsSeparated (Y ↘ Spec (.of P.field.k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of P.field.k))]
    (d : ℕ) [SmoothOfRelativeDimension d f] [IsSeparated f] (c : Compactification f)
    (D : Models P) (b : FieldShriekSystem.Laws P D c) :
    ∃ (a : Domains P D c) (A : Adjoints P D c b a),
      rightReductionLaw P D c b a A := by sorry

end AlgebraicGeometry.ProEtale.FieldExceptionalSystem
