/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NB
-/
module

public import Sheaf.Paper.CondensedCompositorRealizationData

/-! # A coherence step for the specified condensed compact-support compositor -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genCtorIdx false
attribute [-instance] WeilConjectures.IntegralHom.derivedCategory
attribute [local irreducible] HasDerivedCategory.standard
  DerivedCategory.monoidalClosed CategoryTheory.Mod.monoidalClosed
  CategoryTheory.Functor.leftDerivedFunctor CategoryTheory.Functor.rightDerivedFunctor
  CategoryTheory.Functor.mapDerivedCategory CategoryTheory.Mod.monoidalCategory
  CategoryTheory.Sheaf.monoidalCategory

universe u
open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.MonoidalCategory CategoryTheory.MonObj
open scoped CategoryTheory.Obj
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.ProEtale
open WeilConjectures.CompactSupportCondensedRealization

namespace WeilConjectures.CondensedCompositorRealization

attribute [local irreducible] _root_.instCategoryDerivedCategory
  constantSheaf presheafToSheaf Functor.leftAdjoint
attribute [local implicit_reducible] coefficientSequenceHasDerived
  SemilinearProperOpen.derived SemilinearSections.moduleAbelian SemilinearSections.hasDerived
  integralCoefficientSheaf integralCoefficientCommRingSheaf
  coefficientSequenceCommRingSheaf coefficientSequenceCommRingPresheaf
  coefficientSequenceCommRingSystem coefficientSequenceCommRingTransition
  integralCoefficientSheafTransition CategoryTheory.sheafCompose CommRingCat.hasForgetToRingCat
  SemilinearSections.systemRing SemilinearSections.ringPresheaf SemilinearSections.rings



variable (l : ℕ) [Fact l.Prime] (E : Type u) [NormedField E]
  [NormedAlgebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ l)]

/-- Independence of the whole-system word from the intervening tower and common
refinement, with fixed input and output compactifications.
Source: latest blueprint sk-prop-sp-composition, Towers; proper/open interchange
coherence and common-refinement argument, parent proof Step 7
(blueprint: lem-pur-condensed-compositor-system-independence).
Proof: dominate two intervening compactifications by a common proper refinement,
and dominate the two supplied final common refinements compatibly. Vertical and
horizontal mate pasting identify the tower/refinement words after this domination.
Proper and open compositor associativity and their identity normalizations identify
all inserted factors. The refinement homs are the intrinsic proper/open mates.
Their chosen inverse has the specified hom, so is the unique inverse. Cancel the
invertible common-refinement maps on the uniform reduction. This yields equality
of the original whole-system composites. All pasting occurs on the derived sequence
site; finite etale origins are used only to prove the maps invertible, never to
detect equality. The proof also applies to empty opens and identity refinements. -/
theorem condensedCompositorSystemIndependence (A : CoefficientData l E k)
    (X Y Z : CondensedERealization.Base k)
    (f : X.scheme ⟶ Y.scheme) (g : Y.scheme ⟶ Z.scheme)
    [f.IsOver (Spec (.of k))] [g.IsOver (Spec (.of k))]
    (cf : Compactification f) (cg : Compactification g)
    (ch : Compactification (f ≫ g)) (d : Compactification (cf.g ≫ cg.i))
    (c : Compactification (f ≫ g))
    (r : c.Refinement (composite k X Y Z f g cf cg d)) (s : c.Refinement ch)
    (d' : Compactification (cf.g ≫ cg.i)) (c' : Compactification (f ≫ g))
    (r' : c'.Refinement (composite k X Y Z f g cf cg d')) (s' : c'.Refinement ch)
    (K : CondensedERealization.Integral l E X.scheme) (hK : Uniform l E k X K) :
    systemCompositor l E k A X Y Z f g cf cg ch d c r s K hK =
      systemCompositor l E k A X Y Z f g cf cg ch d' c' r' s' K hK := by sorry

end WeilConjectures.CondensedCompositorRealization
