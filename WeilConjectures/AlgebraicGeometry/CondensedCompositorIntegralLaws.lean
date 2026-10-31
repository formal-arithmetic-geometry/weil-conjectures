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

/-- Invertibility and naturality of the ordinary integral compositor on the uniform domain.
Source: latest blueprint sk-prop-sp-composition, Towers and passage by Rlim;
sk-thm-purity-transport, Steps 2--3; parent proof Steps 3--4 and 7
(blueprint: lem-pur-condensed-compositor-integral-laws).
Proof: uniform integral reductions have bounded finite etale origins in every
coefficient degree. Open extension preserves these origins. The finite proper/open
base-change theorem makes each intrinsic interchange component invertible there;
whole-system detection of isomorphisms then makes the tower word invertible.
Proper and open compositors are already isomorphisms. Each refinement component is
invertible by refinementIso_exists; its specified inverse is the unique inverse of
that component. Thus the three-factor system compositor is invertible.
Delta is the limit-presentation isomorphism by the adjunction triangle. In the
five-arrow integral composite, functoriality and the other triangle combine the
reduction of delta_f followed by the counit into beta_f. The remaining four factors
are delta_g, the limit of g_!(beta_f), the limit of the system compositor, and
inverse delta_h. They are all invertible. Reflect this through the coefficient
model equivalence and the full integral subcategory to prove the first assertion.
For the second, refinement naturality and uniqueness of inverse give naturality
of its inverse on uniform objects. Compose it with the natural tower and first
refinement maps to get naturality of the whole system word. The four-factor
normal form is natural: paste the squares for delta_g at P_f(v), g_!(beta_f),
the system word and inverse delta_h. Faithfulness gives the stated equality.
No equality is detected by evaluation. Identity arrows and empty opens satisfy the
same unit, counit and naturality identities; zero objects cause no exception. -/
theorem condensedCompositorIntegralLaws (A : CoefficientData l E k)
    (X Y Z : CondensedERealization.Base k)
    (f : X.scheme ⟶ Y.scheme) (g : Y.scheme ⟶ Z.scheme)
    [f.IsOver (Spec (.of k))] [g.IsOver (Spec (.of k))]
    (cf : Compactification f) (cg : Compactification g)
    (ch : Compactification (f ≫ g)) (d : Compactification (cf.g ≫ cg.i))
    (c : Compactification (f ≫ g))
    (r : c.Refinement (composite k X Y Z f g cf cg d)) (s : c.Refinement ch) :
    (∀ (K : CondensedERealization.Integral l E X.scheme) (hK : Uniform l E k X K),
      IsIso (integralCompositor l E k A X Y Z f g cf cg ch d c r s K hK)) ∧
    (∀ (K K' : CondensedERealization.Integral l E X.scheme)
      (hK : Uniform l E k X K) (hK' : Uniform l E k X K') (v : K ⟶ K'),
      (P l E k A Y Z g cg).map ((P l E k A X Y f cf).map v) ≫
          integralCompositor l E k A X Y Z f g cf cg ch d c r s K' hK' =
        integralCompositor l E k A X Y Z f g cf cg ch d c r s K hK ≫
          (P l E k A X Z (f ≫ g) ch).map v) := by sorry

end WeilConjectures.CondensedCompositorRealization
