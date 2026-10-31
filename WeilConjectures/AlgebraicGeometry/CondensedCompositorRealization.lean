/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CondensedCompositorRealizationData
import all WeilConjectures.AlgebraicGeometry.CondensedCompositorRealizationData
import WeilConjectures.AlgebraicGeometry.CondensedCompositorRealizationSquare
import WeilConjectures.AlgebraicGeometry.CondensedCompositorSystemIndependence
import WeilConjectures.AlgebraicGeometry.CondensedCompositorIntegralRefinement
import WeilConjectures.AlgebraicGeometry.CondensedCompositorIntegralLaws

/-! # Condensed realization of the specified compact-support compositor

The comparison laws and triangle normalization are proved in the data module.
This theorem assembles them with four strictly smaller integral and geometric steps.
(blueprint: lem-pur-condensed-compositor-realization).
-/

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



attribute [local irreducible] integralCompositor systemCompositor refinementInverse delta
attribute [local implicit_reducible] integralReduction reconstructedSystem

variable (l : ℕ) [Fact l.Prime] (E : Type u) [NormedField E]
  [NormedAlgebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ l)]

/-- Condensed realization preserves the specified compact-support compositor.
The coefficient field E is a universe-sized presentation of Q_l, fixed by e.
IsFactorized fixes a to inverse reconstruction, the proper counit mate and the open
unit mate, rather than allowing an independently rescaled realization isomorphism.
Source: latest blueprint sk-prop-sp-composition, Towers; sk-thm-purity-transport,
Steps 2--3; the item's explicit comparison supplement
(blueprint: lem-pur-condensed-compositor-realization).
Proof:
1. Finite type over k gives noetherian finite dimension, and l is invertible.
Integral support preserves uniform constructibility and compatible etale origins.
2. Form the ordinary completed proper/open comparison b on the whole derived
sequence site. Its proper factor is the counit transpose and its open factor is
the inverse unit mate. The finite b composition identity is the etale/pro-etale
composition identity; transposition gives the finite c identity.
3. Apply the actual reduction/limit adjunction to b. Its adjunct q is L(b) after
the reconstruction unit, and beta R(q)=b by the triangle identity. The strict
proper/open word and its refinement factors are invertible on the uniform domain;
evaluations detect isomorphisms but are not used to detect equality of arrows.
4. Proper composition, open composition and the intrinsic interchange satisfy the
whole-system coefficient square by mate pasting. Take its total limit. Substitute
beta R(q)=b in the displayed five-arrow composite. Naturality and the two triangle
identities cancel its inserted counit and units, identifying it with the completed
proper/open compositor conjugated by q.
5. IsFactorized identifies a_E with J(q inverse), the actual proper scalar counit
mate and the open-unit scalar mate. Their coefficient squares identify the completed
compositor with the condensed compositor. Extending to Omega uses the original
proper/open coefficient projection; descent to a common finite field proves this
projection invertible for the finite-extension-valued coefficient ring.
6. Paste the scalar square with the conjugacy of Step 4, then cancel the invertible
image of the two q maps. The remaining equality is exactly square, with the inverse
archived compositor transported to cf,cg,ch by the canonical comparisons.
7. All these maps are natural in complexes and localized morphisms. Horizontal and
vertical mate pasting before evaluation gives refinement compatibility and tower
independence. For an open g, use (g,id); its proper counit mate becomes identity
under openTrivial, leaving the exact open extension and its specified unit.
This includes identity arrows, empty schemes and empty opens. -/
theorem condensedCompositorRealization (C : ComparisonFamily l k)
    (_hC : CompactSupportRealizationFactorization.IsFactorized l k C)
    (_e : E ≃ₐ[ℚ_[l]] ℚ_[l])
    (X Y Z : CondensedERealization.Base k)
    (f : X.scheme ⟶ Y.scheme) (g : Y.scheme ⟶ Z.scheme)
    [f.IsOver (Spec (.of k))] [g.IsOver (Spec (.of k))]
    (df dg : ℕ) [SmoothOfRelativeDimension df f] [SmoothOfRelativeDimension dg g]
    (cf : Compactification f) (cg : Compactification g)
    (ch : Compactification (f ≫ g)) (d : Compactification (cf.g ≫ cg.i))
    (c : Compactification (f ≫ g))
    (r : c.Refinement (composite k X Y Z f g cf cg d)) (s : c.Refinement ch) :
    Laws l E k (C.coefficient E) ((Algebra.ofId ℚ_[l] (PadicAlgCl l)).comp _e.toAlgHom)
      X Y Z f g cf cg ch d c r s := by
  have hIntegral := condensedCompositorIntegralLaws l E k (C.coefficient E)
    X Y Z f g cf cg ch d c r s
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact hIntegral.1
  · exact comparison_isIso l E k (C.coefficient E)
      ((Algebra.ofId ℚ_[l] (PadicAlgCl l)).comp _e.toAlgHom) X Y f cf
  · exact condensedCompositorRealizationSquare l E k C _hC _e X Y Z f g
      cf cg ch d c r s
  · exact ⟨fun cf' rf ↦ comparison_refines l E k C _ X Y f rf,
      fun cg' rg ↦ comparison_refines l E k C _ Y Z g rg,
      fun ch' rh ↦ comparison_refines l E k C _ X Z (f ≫ g) rh⟩
  · exact hIntegral.2
  · intro d' c' r' s' K hK
    apply ObjectProperty.hom_ext
    apply (purCoefficientModel l E Z.scheme).fullyFaithfulFunctor.map_injective
    rw [integralCompositor_model, integralCompositor_model,
      condensedCompositorSystemIndependence l E k (C.coefficient E)
        X Y Z f g cf cg ch d c r s d' c' r' s' K hK]
  · exact condensedCompositorIntegralRefinement l E k C
      X Y Z f g cf cg ch d c r s


end WeilConjectures.CondensedCompositorRealization
