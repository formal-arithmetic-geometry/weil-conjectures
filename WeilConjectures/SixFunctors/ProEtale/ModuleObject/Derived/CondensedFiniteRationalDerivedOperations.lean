/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedModuleDerivedPushpull
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixDefinitions
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ScalarSixTensorHom
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedProperOpenInterchange
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic

/-! # Ambient operations and finite reduction for condensed coefficients

Source: latest blueprint, sec-proetale-coefficients/sk-prop-sf-open-closed-triangle/
def-weil-derived-pullback-tensor-hom.md, the three operations and final paragraph;
sec-smooth-purity/sk-lem-sp-reduction/thm-pur-finite-reduction-of-purity.proof.md, Step 2.
(blueprint: def-sf-finite-rational-derived-operations).

The datum packages the native total pullback, K-flat tensor and closed internal Hom.
Scalar comparisons retain their mate and evaluation normalizations. Finite reduction
is ordinary derived scalar extension along the actual quotient map.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- The normalized scalar-adjunction mate, conjugated through the canonical exact/total
pullback comparisons. Its components are the forward components of the published j.
Only the morphism is used here; no invertibility assertion is needed in this definition.
Source: latest blueprint def-weil-derived-pullback-tensor-hom, scalar compatibility;
def-sfb-scalar-six-coefficient-interfaces, canonical pullback mate
(blueprint: def-sf-finite-rational-derived-operations). -/
def condensedOperationPullbackComparison {Λ Λ' : ScalarSixRing.{u}} (a : Λ ⟶ Λ')
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    moduleObjectDerivedPullback Λ.X f ⋙ scalarSixChange a X ⟶
      scalarSixChange a Y ⋙ moduleObjectDerivedPullback Λ'.X f :=
  Functor.whiskerRight (leftDerivedUpperStarIsoMapDerivedCategory Λ.X f).hom _ ≫
    scalarSixPullHom a f ≫
      Functor.whiskerLeft _ (leftDerivedUpperStarIsoMapDerivedCategory Λ'.X f).inv

/-- The actual quotient coefficient map, induced by identity on O_E and postcomposition
on continuous sections. The discrete topologies make the quotient map continuous.
Source: latest blueprint thm-pur-finite-reduction-of-purity.proof, Step 2
(blueprint: def-sf-finite-rational-derived-operations). -/
def condensedFiniteReductionCoefficient (ℓ : ℕ) [Fact ℓ.Prime] (E : Type u) [Field E]
    [Algebra (Padic ℓ) E] [FiniteDimensional (Padic ℓ) E]
    (n m : ℕ) (_hm : 1 ≤ m) (hmn : m ≤ n) :
    (⟨properOpenFiniteCoefficient ℓ E n⟩ : ScalarSixRing.{u}) ⟶
      (⟨properOpenFiniteCoefficient ℓ E m⟩ : ScalarSixRing.{u}) :=
  letI : TopologicalSpace (Padic.coefficientExtensionRing ℓ E n) := ⊥
  letI : DiscreteTopology (Padic.coefficientExtensionRing ℓ E n) := ⟨rfl⟩
  letI : TopologicalSpace (Padic.coefficientExtensionRing ℓ E m) := ⊥
  letI : DiscreteTopology (Padic.coefficientExtensionRing ℓ E m) := ⟨rfl⟩
  let q : Padic.coefficientExtensionRing ℓ E n →+* Padic.coefficientExtensionRing ℓ E m :=
    Ideal.Quotient.factor (Ideal.pow_le_pow_right hmn)
  let g : Profinite.continuousCoefficientRingSheaf (Padic.coefficientExtensionRing ℓ E n) ⟶
      Profinite.continuousCoefficientRingSheaf (Padic.coefficientExtensionRing ℓ E m) :=
    ⟨{ app := fun _ ↦ RingCat.ofHom
         (ULift.ringEquiv.symm.toRingHom.comp
           ((q.compLeftContinuous _ continuous_of_discreteTopology).comp
             ULift.ringEquiv.toRingHom))
       naturality := fun _ _ _ ↦ rfl }⟩
  CommMon.homMk (Mon.ofHom
    ((sheafCompose (coherentTopology Profinite.{u})
      (forget₂ RingCat.{u + 1} Ab.{u + 1})).map g))

/-- Finite reduction red_(n,m,W) is derived extension along the quotient, with no
flatness hypothesis. Applied to K it gives the object denoted K_m.
Source: latest blueprint thm-pur-finite-reduction-of-purity.proof, Step 2
(blueprint: def-sf-finite-rational-derived-operations). -/
def condensedFiniteReduction (ℓ : ℕ) [Fact ℓ.Prime] (E : Type u) [Field E]
    [Algebra (Padic ℓ) E] [FiniteDimensional (Padic ℓ) E]
    (n m : ℕ) (hm : 1 ≤ m) (hmn : m ≤ n) (W : Scheme.{u}) :=
  scalarSixChange (condensedFiniteReductionCoefficient ℓ E n m hm hmn) W

end AlgebraicGeometry.ProEtale.CondensedRing
