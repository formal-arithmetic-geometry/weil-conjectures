/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ConstructibleExceptionalCompositorData

/-! # Coherence of canonical compact-support left compositors -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped CategoryTheory.Functor
namespace WeilConjectures.ConstructibleExceptionalCompositor
open ConstructibleExceptionalCoefficients

/-- The normalized compact-support left compositors satisfy shift and refinement
coherence at every coefficient stage. Source: blueprint compact-support composition,
package clauses (2)--(3), and Verdier-exchange Step 1
(blueprint: lem-sf-constructible-left-compositor-coherence).

Proof:
1. Construct the three exceptional-adjunction coefficient systems by exists_system,
using the same canonical constant-ring realizations, normalized integral realizations,
and raw localization and common-field models as in its construction. At finite level
lift the specified support compositor through the fully faithful finite-Tor inclusion;
this is finiteAlpha. At integral level use constructibleIntegralSupport_eq and lift the
specified completed support compositor; this is integralAlpha.
2. The compactified-tower comparison theorem identifies the strict refinement and
composition maps at every positive quotient, with their Roos projection normalizations.
Its horizontal and vertical pasting laws give the displayed left refinement square.
Apply total derived limit to these strict maps and conjugate by the normalized word
realizations to obtain the integral square. This uses equality of strict tower maps,
not faithfulness of individual finite evaluations in the derived category.
3. Use finiteStructuralMaps_commShift for the finite maps. Apply integral realization
shift coherence to the finite list of intermediate finite-Tor objects in each word,
with a common cohomological and Tor interval. This gives the integral shift square
for the specified integral shifts, without replacing a shift by a new choice.
4. Extend the integral compositor and its square linearly to the raw rational Hom
modules. Naturality and the composition equation hold on pure tensors and hence on
all morphisms. The chosen rationalization comparisons give exactly the rational field
of LeftCompositors. Represent the finite collection of common-stage objects over a
common finite coefficient field, then use coherent-pair functor descent and its
compatibility with further field extension. This gives the common field and both
squares at the closed stage. Empty schemes have the zero operation, so all equations
are identities there. No exceptional mate property is part of this result. -/
theorem constructibleLeftCompositorCoherence
    {D : FiniteFieldDatum.{u}} (B : D.CoefficientDatum)
    (S : ∀ (E : FieldStage.{u} B.l) (n : ℕ+),
      SixFunctorOperationDatum D B E.carrier n n.pos)
    {X Y Z : SixFunctorSpace D}
    [IsSeparated X.obj.hom] [IsSeparated Y.obj.hom] [IsSeparated Z.obj.hom]
    (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsSeparated f.hom.left] [LocallyOfFiniteType f.hom.left] [QuasiCompact f.hom.left]
    [IsSeparated g.hom.left] [LocallyOfFiniteType g.hom.left] [QuasiCompact g.hom.left] :
    ∃ (P : System B.l B.Qbar D B.different (f := f.hom.left))
      (Q : System B.l B.Qbar D B.different (f := g.hom.left))
      (R : System B.l B.Qbar D B.different (f := (f ≫ g).hom.left))
      (A : LeftCompositors B f g P Q R S),
      (∀ (cf : Compactification f.hom.left) (cg : Compactification g.hom.left)
        (cx : Compactification (f ≫ g).hom.left) (s : Stage.{u} B.l),
        (A.alpha cf cg cx s).hom.CommShift ℤ) ∧
      (∀ (cf df : Compactification f.hom.left) (rf : cf.Refinement df)
        (cg dg : Compactification g.hom.left) (rg : cg.Refinement dg)
        (cx dx : Compactification (f ≫ g).hom.left) (rx : cx.Refinement dx)
        (s : Stage.{u} B.l),
        (A.alpha cf cg cx s).hom ≫ (R.refinements.refinement rx s).left.hom =
          Functor.whiskerLeft (P.ring.operation cf s).F
            (Q.refinements.refinement rg s).left.hom ≫
          Functor.whiskerRight (P.refinements.refinement rf s).left.hom
            (Q.ring.operation dg s).F ≫ (A.alpha df dg dx s).hom) := by
  sorry

end WeilConjectures.ConstructibleExceptionalCompositor
