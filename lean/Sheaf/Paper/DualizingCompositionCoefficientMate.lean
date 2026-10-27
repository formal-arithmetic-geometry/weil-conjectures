/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q129
-/
module

public import Sheaf.Paper.FiniteFieldFiber
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Sheaf.Paper.SixFunctorDatum
public import Sheaf.Paper.FiniteTorAmplitudeSites
public import Sheaf.Paper.SixFunctorDualNotation
import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.CategoryTheory.Adjunction.Mates

/-! # The constructible dualizing composition mate

Source: main-20261015, thm-sf-verdier-exchange.proof.md, Steps 1 and 3
(blueprint: lem-sf-dualizing-composition-coefficient-mate).

The restricted exceptional functors use the actual finite-Tor predicates and the
preservation fields of A1. The composition mate is the already recorded right-adjoint
composition, restricted to those full categories. Its Hom normalization determines it
uniquely. The coefficient equation uses precisely the adjunction comparisons of A5.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u v w v' w'

open CategoryTheory AlgebraicGeometry

namespace WeilConjectures

section Restricted

variable {D : FiniteFieldDatum.{u}}
  {B : SixFunctorSpace D → Type v} [∀ X, Category.{w} (B X)]
  {S : SixFunctorPushStage D B} {P : ∀ X, ObjectProperty (B X)}

/-- Restrict the supplied exceptional functor to its actual finite-Tor domain.
Source: A1, finite-Tor domain of def-sf-datum
(blueprint: lem-sf-dualizing-composition-coefficient-mate). -/
def dualizingCompositionExceptional (H : SixFunctorCoherentStage S P)
    {X Y : SixFunctorSpace D} (f : X ⟶ Y) (cf : Compactification f.hom.left) :
    (P Y).FullSubcategory ⥤ (P X).FullSubcategory :=
  (P X).lift ((P Y).ι ⋙ S.exceptional f cf)
    (fun K ↦ H.exceptionalDomain f cf K.obj K.property)

/-- The existing composition mate, restricted through the full finite-Tor inclusions.
Source: Step 1, conjugate of the supplied A4 compositor
(blueprint: lem-sf-dualizing-composition-coefficient-mate). -/
def dualizingCompositionMate (H : SixFunctorCoherentStage S P)
    {X Y Z : SixFunctorSpace D} (f : X ⟶ Y) (g : Y ⟶ Z)
    (cf : Compactification f.hom.left) (cg : Compactification g.hom.left)
    (cfg : Compactification (f ≫ g).hom.left) :
    dualizingCompositionExceptional H g cg ⋙ dualizingCompositionExceptional H f cf ≅
      dualizingCompositionExceptional H (f ≫ g) cfg :=
  NatIso.ofComponents
    (fun K ↦ ObjectProperty.isoMk (P X)
      ((sixFunctorExceptionalComposition S f g cf cg cfg).symm.app K.obj))
    (fun t ↦ ObjectProperty.hom_ext (P X)
      ((sixFunctorExceptionalComposition S f g cf cg cfg).inv.naturality t.hom))

/-- The full Hom chain, with precomposition by alpha rather than its inverse.
Source: Step 1, the displayed A1 Hom characterization
(blueprint: lem-sf-dualizing-composition-coefficient-mate). -/
def DualizingCompositionHomFormula (H : SixFunctorCoherentStage S P)
    {X Y Z : SixFunctorSpace D} (f : X ⟶ Y) (g : Y ⟶ Z)
    (cf : Compactification f.hom.left) (cg : Compactification g.hom.left)
    (cfg : Compactification (f ≫ g).hom.left)
    (c : dualizingCompositionExceptional H g cg ⋙
      dualizingCompositionExceptional H f cf ≅
        dualizingCompositionExceptional H (f ≫ g) cfg) : Prop :=
  ∀ (K : (P X).FullSubcategory) (L : (P Z).FullSubcategory)
    (t : K ⟶ (dualizingCompositionExceptional H g cg ⋙
      dualizingCompositionExceptional H f cf).obj L),
    (t ≫ c.hom.app L).hom =
      (S.exceptionalAdjunction (f ≫ g) cfg).homEquiv K.obj L.obj
        ((S.composition f g cf cg cfg).hom.app K.obj ≫
          ((S.exceptionalAdjunction g cg).homEquiv
            ((S.support f cf).obj K.obj) L.obj).symm
            (((S.exceptionalAdjunction f cf).homEquiv K.obj
              ((S.exceptional g cg).obj L.obj)).symm t.hom))

/-- The normalization and uniqueness clauses for one coefficient stage.
Source: Step 1, natural isomorphism and uniqueness
(blueprint: lem-sf-dualizing-composition-coefficient-mate). -/
def DualizingCompositionNormalized (H : SixFunctorCoherentStage S P) : Prop :=
  ∀ (X Y : SixFunctorSpace D) [IsSeparated X.obj.hom] [IsSeparated Y.obj.hom]
    (f : X ⟶ Y) [IsSeparated f.hom.left]
    [LocallyOfFiniteType f.hom.left] [QuasiCompact f.hom.left]
    (cf : Compactification f.hom.left)
    (cg : Compactification (sixFunctorStructure Y).hom.left)
    (cfg : Compactification (f ≫ sixFunctorStructure Y).hom.left),
    DualizingCompositionHomFormula H f (sixFunctorStructure Y) cf cg cfg
      (dualizingCompositionMate H f (sixFunctorStructure Y) cf cg cfg) ∧
    ∀ c, DualizingCompositionHomFormula H f (sixFunctorStructure Y) cf cg cfg c →
      c = dualizingCompositionMate H f (sixFunctorStructure Y) cf cg cfg

end Restricted

/-- The four coefficient stages have exactly the normalized unique composition mate.
Its value at the coefficient unit is the indicated dualizing isomorphism, since
`SixFunctorDualityData.dualizing` is exceptional inverse image of that unit.

Source: main-20261015, thm-sf-verdier-exchange.proof.md, Step 1
(blueprint: lem-sf-dualizing-composition-coefficient-mate).

Proof plan: (1) use def-weil-pbc-composite-adjunction for the pasted Hom bijection
and counit. (2) Conjugate alpha using def-weil-pbc-adjunction-conjugate; the inverse
is the conjugate of its inverse. (3) The transpose formula of
def-weil-pbc-adjunction-mate is eps_H H(c) = eps_G G(eps_F) alpha.
Naturality of alpha gives exactly the three inverse Hom bijections and the
precomposition in the definition above. (4) Test a competing map on the identity
of the composite right-adjoint object to prove uniqueness. Restrict through the
full finite-Tor inclusions using A1 preservation. No biduality is used. -/
theorem dualizingComposition_normalized
    (D : FiniteFieldDatum.{u}) (C : D.CoefficientDatum)
    (E : Type u) [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] (n : ℕ) (hn : 1 ≤ n)
    (S : SixFunctorDatum D C E n hn) :
    DualizingCompositionNormalized S.finiteCoherence ∧
    DualizingCompositionNormalized S.integralCoherence ∧
    DualizingCompositionNormalized S.rationalCoherence ∧
    DualizingCompositionNormalized S.commonCoherence := by
  sorry

section Coefficients

variable {D : FiniteFieldDatum.{u}}
  {B : SixFunctorSpace D → Type v} [∀ X, Category.{w} (B X)]
  {B' : SixFunctorSpace D → Type v'} [∀ X, Category.{w'} (B' X)]

/-- The composition mate evaluated at the coefficient unit, hence the dualizing iso.
Source: Step 1, the particular isomorphism f^! omega_Y = omega_X
(blueprint: lem-sf-dualizing-composition-coefficient-mate). -/
def dualizingCompositionUnitIso (S : SixFunctorPushStage D B)
    {X Y : SixFunctorSpace D} (f : X ⟶ Y)
    (cf : Compactification f.hom.left)
    (cg : Compactification (sixFunctorStructure Y).hom.left)
    (cfg : Compactification (f ≫ sixFunctorStructure Y).hom.left)
    (one : B (sixFunctorPoint D)) :
    (S.exceptional f cf).obj ((S.exceptional (sixFunctorStructure Y) cg).obj one) ≅
      (S.exceptional (f ≫ sixFunctorStructure Y) cfg).obj one :=
  (sixFunctorExceptionalComposition S f (sixFunctorStructure Y) cf cg cfg).symm.app one

/-- The A5 dualizing-object comparison: beta followed by exceptional image of u.
Here the chosen source structure map is literally `a_Y f`, as in the node.
Source: Step 3, definition of kappa
(blueprint: lem-sf-dualizing-composition-coefficient-mate). -/
def dualizingCompositionKappa
    {S : SixFunctorPushStage D B} {S' : SixFunctorPushStage D B'}
    {T : ∀ X, B X ⥤ B' X} (A : SixFunctorCoefficientComparison S S' T)
    {X Z : SixFunctorSpace D} (a : X ⟶ Z) (ca : Compactification a.hom.left)
    {one : B Z} {one' : B' Z} (unit : (T Z).obj one ≅ one') :
    (T X).obj ((S.exceptional a ca).obj one) ≅ (S'.exceptional a ca).obj one' :=
  ((A.supportAdjunction a ca).right.app one) ≪≫
    (S'.exceptional a ca).mapIso unit

/-- Coefficient equation for an allowed A5 comparison, with its supplied unit map.
This is stated in the faithful bounded-constructible presentation of the full
finite-Tor categories; all arrows and their order are unchanged by the inclusion.
`S,S'` are the stages of that comparison, not additional exceptional adjoints on
ambient derived categories. A comparison is supplied only where A5 defines it;
this theorem neither constructs nor assumes any field-to-finite reduction.

Source: main-20261015, thm-sf-verdier-exchange.proof.md, Step 3
(blueprint: lem-sf-dualizing-composition-coefficient-mate).

Proof plan: (1) A.supportAdjunction is exactly the A5 unit/counit square, so its
right comparison is the mate of the inverse left comparison by
def-weil-pbc-adjunction-mate. (2) A.composition is the A5 compositor square.
Rearrange that square and apply lem-weil-pbc-mate-pasting: clause 2 pastes the
f and a_Y comparisons, and clauses 3a and 3b change the two adjunctions via alpha
and alpha'. (3) The two equal left squares have equal mates, giving the equation
at arbitrary L. (4) Put L equal to the coefficient unit, postcompose by the
exceptional image of unit, and use naturality of the target composition mate.
This gives exactly kappa_X T_X(c_f) = c'_f f'^!(kappa_Y) beta_f. -/
theorem dualizingComposition_coefficient
    (S : SixFunctorPushStage D B) (S' : SixFunctorPushStage D B')
    (T : ∀ X, B X ⥤ B' X) (A : SixFunctorCoefficientComparison S S' T)
    (X Y : SixFunctorSpace D) [IsSeparated X.obj.hom] [IsSeparated Y.obj.hom]
    (f : X ⟶ Y) [IsSeparated f.hom.left]
    [LocallyOfFiniteType f.hom.left] [QuasiCompact f.hom.left]
    (cf : Compactification f.hom.left)
    (cg : Compactification (sixFunctorStructure Y).hom.left)
    (cfg : Compactification (f ≫ sixFunctorStructure Y).hom.left)
    (one : B (sixFunctorPoint D)) (one' : B' (sixFunctorPoint D))
    (unit : (T (sixFunctorPoint D)).obj one ≅ one') :
    (T X).map
        (dualizingCompositionUnitIso S f cf cg cfg one).hom ≫
      (dualizingCompositionKappa A (f ≫ sixFunctorStructure Y) cfg unit).hom =
    (A.supportAdjunction f cf).right.hom.app
        ((S.exceptional (sixFunctorStructure Y) cg).obj one) ≫
      (S'.exceptional f cf).map
        (dualizingCompositionKappa A (sixFunctorStructure Y) cg unit).hom ≫
      (dualizingCompositionUnitIso S' f cf cg cfg one').hom := by
  sorry

end Coefficients
end WeilConjectures
