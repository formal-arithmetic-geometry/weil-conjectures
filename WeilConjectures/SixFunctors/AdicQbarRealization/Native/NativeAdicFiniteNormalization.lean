/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.AdicQbarRealization.Native.NativeAdicRealizationData

/-! # Canonical comparison data
Source: BS 6.8.14--6.8.15; HRS 7.9 (blueprint: def-sf-native-adic-finite-normalization). -/
@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option cleanup.letToHave false
set_option linter.all false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genCtorIdx false

attribute [local irreducible] HasDerivedCategory.standard

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme

namespace WeilConjectures.AdicQbarRealization

variable (l : ℕ) [Fact l.Prime] (X : Scheme.{u})

/-- The normalized continuous integral structural map, with its stored commutativity
instance supplied explicitly.
Source: BS 6.8.2 (blueprint: def-sf-native-adic-finite-normalization). -/
def coefficientMap (R : LocallyFiniteAdicRealization.Realization l X)
    (E : AlgebraicallyClosedCoefficients.Index l (PadicAlgCl l)) :
    completedIntegralCommRingSheafUnrestricted l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) X ⟶ ring l X R := by
  letI := R.commutative
  exact (R.coefficient E).integralMap l X

/-- Termwise ordinary scalar extension along the actual continuous integral inclusion.
Source: BS 6.8.14 (blueprint: def-sf-native-adic-finite-normalization). -/
def integralComplex (R : LocallyFiniteAdicRealization.Realization l X)
    (E : AlgebraicallyClosedCoefficients.Index l (PadicAlgCl l)) :=
  (pbcExtend (coefficientMap l X R E)).mapHomologicalComplex (.up ℤ)

/-- Agreement with the finite integral tensor, expressed separately to keep the
literal dependent object transports out of the comparison record's recursor.
Source: BS 6.8.14--6.8.15
(blueprint: def-sf-native-adic-finite-normalization). -/
def finiteTensorAgreement (R : LocallyFiniteAdicRealization.Realization l X)
    [∀ x : X, Invertible (l : X.residueField x)] (A : At l X R)
    (E : AlgebraicallyClosedCoefficients.Index l (PadicAlgCl l))
    (completion : ConstructibleTensorCompletionPresentation l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) X)
    (comparison : completion.tensor ⋙ pbcDerivedExtend (coefficientMap l X R E) ≅
      ((pbcDerivedExtend (coefficientMap l X R E)).prod
        (pbcDerivedExtend (coefficientMap l X R E))) ⋙ A.closed.tensor) : Prop :=
  ∀ K L : sfIntegralConstructibleCategory l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) X,
    let Q₀ := sfRationalConstructibleLocalization l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) X
    let I := GeneralAlgebraicallyClosedCoefficients.inclusion
      (l := l) (Ω := PadicAlgCl l) (Y := X) E
    let e : (rationalDerivedTensor l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) X).obj
        (Q₀.obj K, Q₀.obj L) ≅
      Q₀.obj ((constructibleIntegralTensor l
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) X).obj (K, L)) :=
      eqToIso ((rationalDerivedTensor_existsUnique l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) X).exists.choose_spec.1
        (Q₀.obj K, Q₀.obj L))
    let c := @asIso _ _ _ _ (completion.comparison.app (K.obj, L.obj))
      (completion.normalized.2.2.2 K.obj L.obj K.property L.property).2
    HEq (A.tensor.hom.app (I.obj (Q₀.obj K), I.obj (Q₀.obj L)))
    (A.closed.tensor.map (Prod.mkHom ((R.integral E).hom.app K) ((R.integral E).hom.app L)) ≫
      comparison.inv.app (K.obj, L.obj) ≫
      (pbcDerivedExtend (coefficientMap l X R E)).map c.hom ≫
      (R.integral E).inv.app ((constructibleIntegralTensor l
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) X).obj (K, L)) ≫
      (AdicQbarRealization.ordinary l X R).map (I.map e.inv) ≫
      (AdicQbarRealization.ordinary l X R).map
        (stageTensor l X (PadicAlgCl l) E (Q₀.obj K) (Q₀.obj L)).hom)

/-- The balanced section equation for native integral scalar extension.
Source: BS 6.8.14--6.8.15 (blueprint: def-sf-native-adic-finite-normalization). -/
def finiteBalanceSections (R : LocallyFiniteAdicRealization.Realization l X)
    [∀ x : X, Invertible (l : X.residueField x)] (A : At l X R)
    (E : AlgebraicallyClosedCoefficients.Index l (PadicAlgCl l))
    (balance : constructibleTensorTotal l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) X ⋙
        integralComplex l X R E ≅
    ((integralComplex l X R E).prod (integralComplex l X R E)) ⋙
      coefficientTotalTensor.{u + 1, u + 1, u} (ProEt.topology X) (ring l X R)) : Prop :=
  ∀ (P Q : CochainComplex (integralTowerModules l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) X) ℤ)
      (p q : ℤ) (U : X.ProEtᵒᵖ) (s : (ring l X R).obj.obj U)
      (x : (P.X p).val.obj U) (y : (Q.X q).val.obj U),
    ((balance.hom.app (P, Q)).f (p + q)).val.app U
      (pbcTensorSection (coefficientMap l X R E)
        (((constructibleTensorTotal l
          (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) X).obj
            (P, Q)).X (p + q)) U s
        (constructibleTensorTotalSection l
          (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) X P Q p q U x y)) =
      coefficientTensorGenerator.{u + 1, u + 1, u} (ProEt.topology X) (ring l X R)
        ((integralComplex l X R E).obj P) ((integralComplex l X R E).obj Q)
        p q (p + q) rfl U
        (pbcTensorSection (coefficientMap l X R E) (P.X p) U s x)
        (pbcTensorSection (coefficientMap l X R E) (Q.X q) U 1 y)

/-- The derived normalization equation on actual K-flat representatives.
Source: BS 6.8.14--6.8.15 (blueprint: def-sf-native-adic-finite-normalization). -/
def finiteRepresentative (R : LocallyFiniteAdicRealization.Realization l X)
    [∀ x : X, Invertible (l : X.residueField x)] (A : At l X R)
    (E : AlgebraicallyClosedCoefficients.Index l (PadicAlgCl l))
    (completion : ConstructibleTensorCompletionPresentation l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) X)
    (balance : constructibleTensorTotal l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) X ⋙
        integralComplex l X R E ≅
    ((integralComplex l X R E).prod (integralComplex l X R E)) ⋙
      coefficientTotalTensor.{u + 1, u + 1, u} (ProEt.topology X) (ring l X R))
    (kflat : ∀ P : (integralOperationsGoodComplex l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) X).FullSubcategory,
    CochainComplex.IsKFlatIndependentCoefficients (J := ProEt.topology X) (R := ring l X R)
      ((integralComplex l X R E).obj P.obj))
    (ordinary : completion.tensor ⋙ pbcDerivedExtend (coefficientMap l X R E) ≅
    ((pbcDerivedExtend (coefficientMap l X R E)).prod
      (pbcDerivedExtend (coefficientMap l X R E))) ⋙ A.closed.tensor) : Prop :=
  ∀ P Q : (integralOperationsGoodComplex l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) X).FullSubcategory,
    (pbcDerivedExtend (coefficientMap l X R E)).map
        (completion.model.hom.app (P, Q)) ≫
      ordinary.hom.app (DerivedCategory.Q.obj P.obj, DerivedCategory.Q.obj Q.obj) ≫
      A.closed.tensor.map (Prod.mkHom
        (pbcComplexCounit (coefficientMap l X R E) P.obj)
        (pbcComplexCounit (coefficientMap l X R E) Q.obj)) =
    pbcComplexCounit (coefficientMap l X R E)
        ((constructibleTensorTotal l
          (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) X).obj
            (P.obj, Q.obj)) ≫
      DerivedCategory.Q.map (balance.hom.app (P.obj, Q.obj)) ≫
      (A.models.iso _ _ _ _ _ (kflat P) (kflat Q)).hom

/-- The tensorator is the quotient-completion tensorator, followed by balanced
multiplication. Its chain normalization fixes it on every homogeneous pure section;
the representative equation descends it to the actual derived tensor. The final
identity transports precisely this map through raw localization and stage inclusion.
Source: BS 3.4.10, 6.8.14 and 6.8.15; HRS 7.9
(blueprint: def-sf-native-adic-finite-normalization). -/
structure FiniteNormalization (R : LocallyFiniteAdicRealization.Realization l X)
    [∀ x : X, Invertible (l : X.residueField x)] (A : At l X R)
    (E : AlgebraicallyClosedCoefficients.Index l (PadicAlgCl l)) where
  completion : ConstructibleTensorCompletionPresentation l
    (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) X
  balance : constructibleTensorTotal l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) X ⋙
        integralComplex l X R E ≅
    ((integralComplex l X R E).prod (integralComplex l X R E)) ⋙
      coefficientTotalTensor.{u + 1, u + 1, u} (ProEt.topology X) (ring l X R)
  balance_sections : finiteBalanceSections l X R A E balance
  kflat : ∀ P : (integralOperationsGoodComplex l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) X).FullSubcategory,
    CochainComplex.IsKFlatIndependentCoefficients (J := ProEt.topology X) (R := ring l X R)
      ((integralComplex l X R E).obj P.obj)
  ordinary : completion.tensor ⋙ pbcDerivedExtend (coefficientMap l X R E) ≅
    ((pbcDerivedExtend (coefficientMap l X R E)).prod
      (pbcDerivedExtend (coefficientMap l X R E))) ⋙ A.closed.tensor
  representative : finiteRepresentative l X R A E completion balance kflat ordinary
  integral_tensor : finiteTensorAgreement l X R A E completion ordinary

end WeilConjectures.AdicQbarRealization
