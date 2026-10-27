/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group S8
-/
module

public import Sheaf.SixFunctors.IntegralOpenReductionDefinitions

/-! # The finite ordinary restriction mate

Source: Stacks Project, Modules on Sites, Tags 03DJ and 0E8I.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option backward.defeqAttrib.useBackward true
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [local irreducible] HasDerivedCategory.standard
universe t u a b c d av bv cv dv
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open WeilConjectures.IntegralOpenReduction
namespace WeilConjectures.CanonicalOpenRestriction

private theorem mate_word
    {A : Type a} {B : Type b} {C : Type c} {D : Type d}
    [Category.{av} A] [Category.{bv} B] [Category.{cv} C] [Category.{dv} D]
    {L : A ⥤ B} {R : B ⥤ A} {F : C ⥤ D} {G : D ⥤ C}
    (adj : L ⊣ R) (level : F ⊣ G) {S : A ⥤ C} {T : B ⥤ D}
    (α : TwoSquare S L F T) (N : B) :
    (mateEquiv adj level α).app N = level.unit.app (S.obj (R.obj N)) ≫
      G.map (α.app (R.obj N)) ≫ G.map (T.map (adj.counit.app N)) := by
  simp [mateEquiv]

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  {U X : Scheme.{t}} (j : U ⟶ X) [IsOpenImmersion j] (o : Operations l E j)

/-- The finite open adjunction, retaining both coefficient-equivalence transformations.
Source: Stacks 03DJ (blueprint: lem-sf-ordinary-open-finite-restriction-mate-invertible). -/
abbrev finiteOpenAdjunction (n : ℕ) := (o.finite n).toAdjunction.comp
  (SheafOfModules.localizedSystemAdjunction.{t+1, t, max u (t+1)}
    (rings l E X n) (openObject j))

/-- The actual mate of inverse extension tensor comparison.
Source: Stacks 0E8I (blueprint: lem-sf-ordinary-open-finite-restriction-mate-invertible). -/
def finiteRestrictionMate (tensor : TensorComparison l E j o) (n : ℕ) :
    restriction l E j o ⋙ scalarReductionExtension l E U n ⟶
      scalarReductionExtension l E X n ⋙ finiteRestriction l E j o n :=
  (mateEquiv (ordinaryAdjunction l E j o) (finiteOpenAdjunction l E j o n)
    (TwoSquare.mk _ _ _ _ (tensor.ordinary n).inv)).natTrans

/-- The mate has the prescribed unit, inverse-tensor, counit word.
Source: Stacks 0E8I (blueprint: lem-sf-ordinary-open-finite-restriction-mate-invertible). -/
theorem finiteRestrictionMate_app (tensor : TensorComparison l E j o) (n : ℕ)
    (N : scalarReductionSource l E X) :
    (finiteRestrictionMate l E j o tensor n).app N =
      (finiteOpenAdjunction l E j o n).unit.app _ ≫
        (finiteRestriction l E j o n).map
          ((tensor.ordinary n).inv.app ((restriction l E j o).obj N)) ≫
        (finiteRestriction l E j o n).map
          ((scalarReductionExtension l E X n).map
            ((ordinaryAdjunction l E j o).counit.app N)) := by
  exact mate_word (ordinaryAdjunction l E j o) (finiteOpenAdjunction l E j o n)
    (TwoSquare.mk _ _ _ _ (tensor.ordinary n).inv) N

/-- The generator-normalized finite restriction mate is invertible.
Source: Stacks Project, Modules on Sites, Tags 03DJ and 0E8I,
lemma-j-shriek-and-tensor; finite part of the ordinary quotient argument.
(blueprint: lem-sf-ordinary-open-finite-restriction-mate-invertible).

Proof: work on the actual open slice. Restrict the sheafified scalar-extension
presheaf. Slice restriction commutes with sheafification, and the two tensor
presheaves have the same sections and balancing relations. Sending a pure tensor
to the same two sections therefore defines inverse comparison maps. Transport
through o.integral and o.finite using their units and counits. The coefficient
projection square identifies their scalar actions. To identify the forward map
with the displayed mate, transpose it through the finite open adjunction. Its
extension on every summand generator is the inverse of tensor.ordinary followed
by scalar extension of the integral counit: this is precisely tensor.generators.
Linearity and uniqueness of maps from sheafification give equality everywhere.
The triangular identities identify its transpose with finiteRestrictionMate.
Thus every component is invertible, naturally in N. This is a single finite-level
assertion; no system assembly or transition compatibility is asserted here.
The argument applies at n = 0 and to zero modules and the empty open. -/
theorem finiteRestrictionMate_isIso (tensor : TensorComparison l E j o) (n : ℕ) :
    IsIso (finiteRestrictionMate l E j o tensor n) := by sorry

end WeilConjectures.CanonicalOpenRestriction
