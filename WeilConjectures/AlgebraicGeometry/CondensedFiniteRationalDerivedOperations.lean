/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CondensedModuleDerivedPushpull
public import WeilConjectures.SixFunctors.ScalarSixDefinitions
public import WeilConjectures.SixFunctors.ScalarSixTensorHom
public import WeilConjectures.AlgebraicGeometry.CondensedProperOpenInterchange
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

/-- The five functors in the three-operation datum, with Hom contravariant in its
first argument. The canonical value is `condensedThreeOperations` below.
Source: latest blueprint def-weil-derived-pullback-tensor-hom, displayed operations
(blueprint: def-sf-finite-rational-derived-operations). -/
structure CondensedThreeOperationDatum (Λ : ScalarSixRing.{u}) (X Y : Scheme.{u}) where
  P : DerivedCategory (ModuleRingedComparison.internalModules Λ.X Y) ⥤
    DerivedCategory (ModuleRingedComparison.internalModules Λ.X X)
  TX : DerivedCategory (ModuleRingedComparison.internalModules Λ.X X) ⥤
    DerivedCategory (ModuleRingedComparison.internalModules Λ.X X) ⥤
      DerivedCategory (ModuleRingedComparison.internalModules Λ.X X)
  TY : DerivedCategory (ModuleRingedComparison.internalModules Λ.X Y) ⥤
    DerivedCategory (ModuleRingedComparison.internalModules Λ.X Y) ⥤
      DerivedCategory (ModuleRingedComparison.internalModules Λ.X Y)
  HX : (DerivedCategory (ModuleRingedComparison.internalModules Λ.X X))ᵒᵖ ⥤
    DerivedCategory (ModuleRingedComparison.internalModules Λ.X X) ⥤
      DerivedCategory (ModuleRingedComparison.internalModules Λ.X X)
  HY : (DerivedCategory (ModuleRingedComparison.internalModules Λ.X Y))ᵒᵖ ⥤
    DerivedCategory (ModuleRingedComparison.internalModules Λ.X Y) ⥤
      DerivedCategory (ModuleRingedComparison.internalModules Λ.X Y)

/-- The specified datum: total derived module pullback and the existing K-flat tensor
and closed Hom at each endpoint. It is defined independently at every coefficient.
Source: latest blueprint def-weil-derived-pullback-tensor-hom, constructions of Lf*,
tensor and RHom (blueprint: def-sf-finite-rational-derived-operations). -/
def condensedThreeOperations (Λ : ScalarSixRing.{u}) {X Y : Scheme.{u}} (f : X ⟶ Y) :
    CondensedThreeOperationDatum Λ X Y where
  P := moduleObjectDerivedPullback Λ.X f
  TX := derivedTensor Λ.X X
  TY := derivedTensor Λ.X Y
  HX := derivedHom Λ.X X
  HY := derivedHom Λ.X Y

/-- The canonical exact termwise interpretation of the datum's total pullback.
Source: latest blueprint def-weil-derived-pullback-tensor-hom, exactness paragraph
(blueprint: def-sf-finite-rational-derived-operations). -/
def condensedThreeOperationsTermwise (Λ : ScalarSixRing.{u}) {X Y : Scheme.{u}}
    (f : X ⟶ Y) :
    (condensedThreeOperations Λ f).P ≅ (upperStar Λ.X f).mapDerivedCategory :=
  leftDerivedUpperStarIsoMapDerivedCategory Λ.X f

/-- Ordinary derived scalar extension along the pulled-back coefficient map.
Source: latest blueprint det-def-sfb-coefficient-change, T^X
(blueprint: def-sf-finite-rational-derived-operations). -/
abbrev condensedOperationScalarChange {Λ Λ' : ScalarSixRing.{u}} (a : Λ ⟶ Λ')
    (W : Scheme.{u}) := scalarSixChange a W

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

/-- Scalar composition is the adjunction conjugate of restriction transitivity.
Source: latest blueprint def-sfb-scalar-six-coefficient-interfaces, tower comparison
(blueprint: def-sf-finite-rational-derived-operations). -/
abbrev condensedOperationScalarComposition {Λ Λ' Λ'' : ScalarSixRing.{u}}
    (a : Λ ⟶ Λ') (b : Λ' ⟶ Λ'') (W : Scheme.{u}) := scalarSixTower a b W

/-- The tensor comparison is the inverse tensorator of derived scalar extension.
Source: latest blueprint det-prop-scalar-six-tensor-hom, clause (1)
(blueprint: def-sf-finite-rational-derived-operations). -/
abbrev condensedOperationTensorComparison {Λ Λ' : ScalarSixRing.{u}} (a : Λ ⟶ Λ')
    (W : Scheme.{u}) (M N : DerivedCategory (ModuleRingedComparison.internalModules Λ.X W)) :=
  scalarSixTensorIso a W M N

/-- The internal-Hom comparison is the evaluation transpose: inverse tensor comparison
followed by scalar extension of evaluation. It is an arrow on arbitrary unbounded inputs.
Source: latest blueprint det-prop-scalar-six-tensor-hom, clause (2)
(blueprint: def-sf-finite-rational-derived-operations). -/
abbrev condensedOperationHomComparison {Λ Λ' : ScalarSixRing.{u}} (a : Λ ⟶ Λ')
    (W : Scheme.{u}) (M N : DerivedCategory (ModuleRingedComparison.internalModules Λ.X W)) :=
  scalarSixHomComparison a W M N

/-- The same operation datum at the discrete finite quotient A_(E,n).
Source: latest blueprint def-weil-derived-pullback-tensor-hom, finite coefficients
(blueprint: def-sf-finite-rational-derived-operations). -/
def condensedFiniteOperations (ℓ : ℕ) [Fact ℓ.Prime] (E : Type u) [Field E]
    [Algebra (Padic ℓ) E] [FiniteDimensional (Padic ℓ) E] (n : ℕ)
    {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  condensedThreeOperations (⟨properOpenFiniteCoefficient ℓ E n⟩ : ScalarSixRing.{u}) f

/-- The same operation datum at the continuous integral coefficient O_E.
Source: latest blueprint def-weil-derived-pullback-tensor-hom, uniform definition
(blueprint: def-sf-finite-rational-derived-operations). -/
def condensedIntegralOperations (ℓ : ℕ) [Fact ℓ.Prime] (E : Type u) [Field E]
    [Algebra (Padic ℓ) E] [FiniteDimensional (Padic ℓ) E]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  condensedThreeOperations (⟨properOpenIntegralCoefficient ℓ E⟩ : ScalarSixRing.{u}) f

/-- The same operation datum at the continuous finite-extension coefficient E.
Source: latest blueprint def-weil-derived-pullback-tensor-hom, uniform definition
(blueprint: def-sf-finite-rational-derived-operations). -/
def condensedFieldOperations (ℓ : ℕ) [Fact ℓ.Prime] (E : Type u) [Field E]
    [Algebra (Padic ℓ) E] [FiniteDimensional (Padic ℓ) E]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  condensedThreeOperations (⟨properOpenFieldCoefficient ℓ E⟩ : ScalarSixRing.{u}) f

/-- The same datum at Qbar_l with finite-subextension-valued continuous sections.
Source: latest blueprint sk-def-sfb-qlbar-condensed and uniform operation definition
(blueprint: def-sf-finite-rational-derived-operations). -/
def condensedAlgebraicClosureOperations (ℓ : ℕ) [Fact ℓ.Prime]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  condensedThreeOperations (⟨Profinite.padicAlgClRingObj ℓ⟩ : ScalarSixRing.{u}) f

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

/-- Reduction/pullback comparison with the inherited scalar-adjunction normalization.
Source: latest blueprint thm-pur-finite-reduction-of-purity.proof, Step 2
(blueprint: def-sf-finite-rational-derived-operations). -/
def condensedFiniteReductionPullback (ℓ : ℕ) [Fact ℓ.Prime] (E : Type u) [Field E]
    [Algebra (Padic ℓ) E] [FiniteDimensional (Padic ℓ) E]
    (n m : ℕ) (hm : 1 ≤ m) (hmn : m ≤ n) {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  condensedOperationPullbackComparison (condensedFiniteReductionCoefficient ℓ E n m hm hmn) f

/-- Reduction/tensor comparison with the inherited inverse tensorator normalization.
Source: latest blueprint thm-pur-finite-reduction-of-purity.proof, Step 2
(blueprint: def-sf-finite-rational-derived-operations). -/
def condensedFiniteReductionTensor (ℓ : ℕ) [Fact ℓ.Prime] (E : Type u) [Field E]
    [Algebra (Padic ℓ) E] [FiniteDimensional (Padic ℓ) E]
    (n m : ℕ) (hm : 1 ≤ m) (hmn : m ≤ n) (W : Scheme.{u})
    (M N : DerivedCategory (ModuleRingedComparison.internalModules
      (properOpenFiniteCoefficient ℓ E n) W)) :=
  scalarSixTensorIso (condensedFiniteReductionCoefficient ℓ E n m hm hmn) W M N

/-- Reduction/internal-Hom arrow with the inherited evaluation-transpose normalization.
Source: latest blueprint thm-pur-finite-reduction-of-purity.proof, Step 2
(blueprint: def-sf-finite-rational-derived-operations). -/
def condensedFiniteReductionHom (ℓ : ℕ) [Fact ℓ.Prime] (E : Type u) [Field E]
    [Algebra (Padic ℓ) E] [FiniteDimensional (Padic ℓ) E]
    (n m : ℕ) (hm : 1 ≤ m) (hmn : m ≤ n) (W : Scheme.{u})
    (M N : DerivedCategory (ModuleRingedComparison.internalModules
      (properOpenFiniteCoefficient ℓ E n) W)) :=
  scalarSixHomComparison (condensedFiniteReductionCoefficient ℓ E n m hm hmn) W M N

end AlgebraicGeometry.ProEtale.CondensedRing
