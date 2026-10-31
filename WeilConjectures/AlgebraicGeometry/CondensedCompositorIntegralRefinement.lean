/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CondensedCompositorRealizationData

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

/-- The integral compositor commutes with refinement of all three exterior
compactifications, using their specified integralRefinement maps.
Source: latest blueprint sk-prop-sp-composition, Towers; compact-support realization
refinement squares; parent proof Step 7
(blueprint: lem-pur-condensed-compositor-integral-refinement).
Proof: apply the faithful coefficient-model equivalence. Normalize each five-arrow
compositor by cancelling reduction of delta against the counit. The refinement
square for the actual limit presentation expresses integralRefinement in these
coordinates. Naturality of delta and beta transports the two input refinement maps
through the first two factors. Horizontal and vertical proper/open mate pasting
give the resulting whole-system refinement square for the two specified tower
words. The uniquely pinned refinement inverses cancel the common-refinement factors.
Apply the total-limit functor to this equality, paste the delta naturality squares,
and cancel the output delta isomorphism. Reflect equality back through the model
and full-subcategory inclusion. No total-limit faithfulness or equality detection by
finite evaluation is used. Identity refinements reduce to identity maps, and empty
opens reduce to the unique maps of zero objects. -/
theorem condensedCompositorIntegralRefinement (C : ComparisonFamily l k)
    (X Y Z : CondensedERealization.Base k)
    (f : X.scheme ⟶ Y.scheme) (g : Y.scheme ⟶ Z.scheme)
    [f.IsOver (Spec (.of k))] [g.IsOver (Spec (.of k))]
    (cf : Compactification f) (cg : Compactification g)
    (ch : Compactification (f ≫ g)) (d : Compactification (cf.g ≫ cg.i))
    (c : Compactification (f ≫ g))
    (r : c.Refinement (composite k X Y Z f g cf cg d)) (s : c.Refinement ch)
    (cf' : Compactification f) (cg' : Compactification g)
    (ch' : Compactification (f ≫ g))
    (rf : cf'.Refinement cf) (rg : cg'.Refinement cg) (rh : ch'.Refinement ch)
    (d' : Compactification (cf'.g ≫ cg'.i)) (c' : Compactification (f ≫ g))
    (r' : c'.Refinement (composite k X Y Z f g cf' cg' d')) (s' : c'.Refinement ch')
    (K : CondensedERealization.Integral l E X.scheme) (hK : Uniform l E k X K) :
    let A := C.coefficient E
    integralCompositor l E k A X Y Z f g cf cg ch d c r s K hK ≫
        (integralRefinement l E k A X Z (f ≫ g) rh).app K =
      (integralRefinement l E k A Y Z g rg).app ((P l E k A X Y f cf).obj K) ≫
        (P l E k A Y Z g cg').map ((integralRefinement l E k A X Y f rf).app K) ≫
        integralCompositor l E k A X Y Z f g cf' cg' ch' d' c' r' s' K hK := by sorry

end WeilConjectures.CondensedCompositorRealization
