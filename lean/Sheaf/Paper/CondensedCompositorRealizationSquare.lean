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

/-- The realization square for the specified five-arrow compositor.
Source: latest blueprint sk-prop-sp-composition, Towers and coefficient transport;
sk-thm-purity-transport, Steps 2--3; the parent node's proof Steps 2 and 4--6
(blueprint: lem-pur-condensed-compositor-realization-square).
Proof: form the ordinary completed proper/open word and its comparison b with the
whole coefficient-system word, using the proper counit transpose and inverse open
unit mate. Mate pasting gives its composition identity, before any finite evaluation.
Apply the actual reduction/limit adjunction to b. Its adjunct q satisfies beta R(q)=b
by the triangle identity. Substitute this equation in the five-arrow definition:
functoriality and the two triangles identify the integral compositor with the ordinary
completed compositor conjugated by q. IsFactorized identifies the rational comparison
with realization of q inverse followed by the proper counit mate and open unit mate.
Their coefficient squares identify the completed compositor with the condensed
compositor over E. Extend to Omega through the original condensedProjection. Its
proper/open mate-pasting square transports this identification to the archived
compositor, with its specified direction and compactification conjugations. Cancel
the invertible images of the two q maps. The remaining equality is the displayed
square. This argument uses equality of whole-system morphisms, not faithfulness of
finite evaluation. Identity arrows use the adjunction triangles; empty opens give
zero functors and hence the same unique maps. -/
theorem condensedCompositorRealizationSquare (C : ComparisonFamily l k)
    (hC : CompactSupportRealizationFactorization.IsFactorized l k C)
    (e : E ≃ₐ[ℚ_[l]] ℚ_[l])
    (X Y Z : CondensedERealization.Base k)
    (f : X.scheme ⟶ Y.scheme) (g : Y.scheme ⟶ Z.scheme)
    [f.IsOver (Spec (.of k))] [g.IsOver (Spec (.of k))]
    (cf : Compactification f) (cg : Compactification g)
    (ch : Compactification (f ≫ g)) (d : Compactification (cf.g ≫ cg.i))
    (c : Compactification (f ≫ g))
    (r : c.Refinement (composite k X Y Z f g cf cg d)) (s : c.Refinement ch)
    (K : CondensedERealization.Integral l E X.scheme) (hK : Uniform l E k X K) :
    let A := C.coefficient E
    let a := (Algebra.ofId ℚ_[l] (PadicAlgCl l)).comp e.toAlgHom
    (U l E k A a Z).map
        (integralCompositor l E k A X Y Z f g cf cg ch d c r s K hK) ≫
      comparison l E k A a X Z (f ≫ g) ch K =
    comparison l E k A a Y Z g cg ((P l E k A X Y f cf).obj K) ≫
      (CondensedRing.rightDerivedLowerShriekOfCompactification
        (Profinite.padicAlgClRingObj l) cg).map (comparison l E k A a X Y f cf K) ≫
      ((condensedCompositor l k X Y Z f g cf cg ch).hom.app
        ⟨(U l E k A a X).obj K, U_constructible l E k A a X K⟩).hom := by sorry

end WeilConjectures.CondensedCompositorRealization
