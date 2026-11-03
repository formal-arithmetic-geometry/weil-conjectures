/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.ProEtaleCoefficients.SixFunctorOperationDatum.SixFunctorOperationDatum
public import WeilConjectures.DeligneLaumon.SfWeilSheafComplex
public import WeilConjectures.SmoothPurity.Derived.DerivedPullbackTensorHom
public import WeilConjectures.SixFunctors.Coef.CoefQbarVerdier
public import WeilConjectures.SixFunctors.FrobeniusExchange.FrobeniusGeometricExchange
public import WeilConjectures.SixFunctors.Rational.RationalVerdier
public import WeilConjectures.SixFunctors.RationalOperations.RationalOperationsData
public import WeilConjectures.SixFunctors.RationalOperations.RationalHomIdentifications
public import WeilConjectures.SixFunctors.RationalOperations.RationalExceptionalIdentifications
public import WeilConjectures.SixFunctors.RationalOperations.RationalDualizingIdentification
public import WeilConjectures.SmoothPurity.Derived.DerivedPullbackTensorIso

/-! # Weil equivariance of completed coefficient duality

Source: Weil blueprint main-20261015, sec-six-functors/sk-thm-sf-package,
cor-coef-verdier-weil-equivariance, statement and proof paragraphs 1--3
(blueprint: cor-coef-verdier-weil-equivariance).
The extracted record interface is (blueprint: def-coef-verdier-weil-data).

The records package conclusions about the actual coefficient-passage operations.
All structure isomorphisms act on rational objects themselves.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option synthInstance.maxSize 4096
set_option genSizeOf false
set_option genInjectivity false
set_option genSizeOfSpec false
set_option genCtorIdx false
set_option maxRecDepth 10000
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v a b a' b' i w
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open CategoryTheory.Endofunctor (IsoAlgebra)

namespace WeilConjectures.CoefVerdierWeil

/-- Exceptional Frobenius comparison and equivariance of the specified adjunction.
The right comparison is the mate of the inverse left comparison. Thus the unit
and counit are those of the original constructible adjunction.
Source: blueprint proof paragraph 1, explicit mate in DAG step 3
(blueprint: cor-coef-verdier-weil-equivariance). -/
structure Exceptional {C : Type a} {C' : Type a'}
    [Category.{b} C] [Category.{b'} C'] (P : C ⥤ C) (Q : C' ⥤ C')
    {F : C ⥤ C'} {G : C' ⥤ C} (adj : F ⊣ G) where
  left : F ⋙ Q ≅ P ⋙ F
  right : G ⋙ P ≅ Q ⋙ G
  mate : right.hom = (mateEquiv adj adj (TwoSquare.mk _ _ _ _ left.inv)).natTrans
  unit (K : IsoAlgebra P) :
    K.str.hom ≫ adj.unit.app K.carrier =
      P.map (adj.unit.app K.carrier) ≫ right.hom.app (F.obj K.carrier) ≫
        G.map (left.hom.app K.carrier) ≫ G.map (F.map K.str.hom)
  counit (M : IsoAlgebra Q) :
    left.hom.app (G.obj M.carrier) ≫ F.map (right.hom.app M.carrier) ≫
      F.map (G.map M.str.hom) ≫ adj.counit.app M.carrier =
        Q.map (adj.counit.app M.carrier) ≫ M.str.hom

/-- The structure morphism of the geometric fiber inherits local finite type.
Source: blueprint geometric-fiber convention, Stacks 01T0
(blueprint: cor-coef-verdier-weil-equivariance). -/
abbrev fiberStructureLocallyFiniteType (D : FiniteFieldDatum.{u})
    (X₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] :
    LocallyOfFiniteType ((D.geometricFiber X₀).left ↘ Spec (.of D.k)) :=
  (FrobeniusExchange.fiber_finiteType D X₀).1

/-- The structure morphism of the geometric fiber inherits quasi-compactness.
Source: blueprint geometric-fiber convention, Stacks 01T0
(blueprint: cor-coef-verdier-weil-equivariance). -/
abbrev fiberStructureQuasiCompact (D : FiniteFieldDatum.{u})
    (X₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] :
    QuasiCompact ((D.geometricFiber X₀).left ↘ Spec (.of D.k)) :=
  (FrobeniusExchange.fiber_finiteType D X₀).2

/-- Separatedness is inherited by the actual geometric fiber structure morphism.
Source: blueprint separated finite-type convention, Stacks 01KH
(blueprint: cor-coef-verdier-weil-equivariance). -/
abbrev fiberStructureSeparated (D : FiniteFieldDatum.{u})
    (X₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType X₀.hom]
    [QuasiCompact X₀.hom] [IsSeparated X₀.hom] :
    IsSeparated ((D.geometricFiber X₀).left ↘ Spec (.of D.k)) :=
  MorphismProperty.baseChange_obj (P := @IsSeparated) _ X₀ inferInstance

/-- The geometric map inherits separatedness from the descended morphism.
Source: blueprint exceptional clause, Stacks 01KH
(blueprint: cor-coef-verdier-weil-equivariance). -/
abbrev fiberMapSeparated (D : FiniteFieldDatum.{u})
    {X₀ Y₀ : Over (Spec (.of D.k₀))} (f₀ : X₀ ⟶ Y₀) [IsSeparated f₀.left] :
    IsSeparated (FrobeniusExchange.fiberMap D f₀) :=
  MorphismProperty.overPullbackMap (P := @IsSeparated) _ f₀ inferInstance

/-- The geometric map inherits local finite type from the descended morphism.
Source: blueprint exceptional clause, Stacks 01T0
(blueprint: cor-coef-verdier-weil-equivariance). -/
abbrev fiberMapLocallyFiniteType (D : FiniteFieldDatum.{u})
    {X₀ Y₀ : Over (Spec (.of D.k₀))} (f₀ : X₀ ⟶ Y₀) [LocallyOfFiniteType f₀.left] :
    LocallyOfFiniteType (FrobeniusExchange.fiberMap D f₀) :=
  MorphismProperty.overPullbackMap (P := @LocallyOfFiniteType) _ f₀ inferInstance

/-- The geometric map inherits quasi-compactness from the descended morphism.
Source: blueprint exceptional clause, Stacks 01T0
(blueprint: cor-coef-verdier-weil-equivariance). -/
abbrev fiberMapQuasiCompact (D : FiniteFieldDatum.{u})
    {X₀ Y₀ : Over (Spec (.of D.k₀))} (f₀ : X₀ ⟶ Y₀) [QuasiCompact f₀.left] :
    QuasiCompact (FrobeniusExchange.fiberMap D f₀) :=
  MorphismProperty.overPullbackMap (P := @QuasiCompact) _ f₀ inferInstance

section Geometric
open AlgebraicallyClosedCoefficients (Index Coefficient coefficientInclusion)
open GeneralAlgebraicallyClosedCoefficients (Stage inclusion transition)

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
  (X₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType X₀.hom]
  [QuasiCompact X₀.hom] [IsSeparated X₀.hom]

/-- The actual common-stage Frobenius pullback-tensor comparison.
Source: blueprint proof steps 2 and 8
(blueprint: cor-coef-verdier-weil-equivariance). -/
def commonMu
    (K M : generalAlgebraicallyClosedConstructibleCategory l Ω (D.geometricFiber X₀).left) :
    (sfCommonStageWeilFrobeniusPullback D l hl X₀ Ω).obj
      ((CoefQbarTensor D l hl Ω (D.geometricFiber X₀).left).obj (K, M)) ≅
    (CoefQbarTensor D l hl Ω (D.geometricFiber X₀).left).obj
      ((sfCommonStageWeilFrobeniusPullback D l hl X₀ Ω).obj K,
       (sfCommonStageWeilFrobeniusPullback D l hl X₀ Ω).obj M) :=
  @canonicalCommonStagePullbackTensor l _ Ω _ _ _ _ _
    (D.geometricFrobenius X₀).hom
    (fun x ↦ sfWeilPrimeInvertible D l hl X₀ x)
    (fun x ↦ sfWeilPrimeInvertible D l hl X₀ x) K M


set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

section ExceptionalGeometry
variable {Y₀ : Over (Spec (.of D.k₀))} [LocallyOfFiniteType Y₀.hom]
  [QuasiCompact Y₀.hom] [IsSeparated Y₀.hom]
  (f₀ : X₀ ⟶ Y₀) [IsSeparated f₀.left] [LocallyOfFiniteType f₀.left]
  [QuasiCompact f₀.left] (c : Compactification (FrobeniusExchange.fiberMap D f₀))


/-- The actual exceptional record, with inherited fiber instances.
Source: blueprint exceptional clause (blueprint: cor-coef-verdier-weil-equivariance). -/
def FiberExceptional :=
  letI := fiberStructureLocallyFiniteType D X₀
  letI := fiberStructureQuasiCompact D X₀
  letI := fiberStructureSeparated D X₀
  letI := fiberStructureLocallyFiniteType D Y₀
  letI := fiberStructureQuasiCompact D Y₀
  letI := fiberStructureSeparated D Y₀
  letI := fiberMapSeparated D f₀
  letI := fiberMapLocallyFiniteType D f₀
  letI := fiberMapQuasiCompact D f₀
  CoefQbarVerdier.Exceptional (Y := (D.geometricFiber Y₀).left)
    D l hl Ω (D.geometricFiber X₀).left
    (FrobeniusExchange.fiberMap D f₀) c


end ExceptionalGeometry


set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

section PinnedGeometry
variable {Y₀ : Over (Spec (.of D.k₀))} [LocallyOfFiniteType Y₀.hom]
    [QuasiCompact Y₀.hom] [IsSeparated Y₀.hom]
    (f₀ : X₀ ⟶ Y₀) [IsSeparated f₀.left] [LocallyOfFiniteType f₀.left]
    [QuasiCompact f₀.left] (c₀ : Compactification f₀.left)
    (A : FiberExceptional D l hl Ω X₀ f₀
      (FrobeniusExchange.geometricCompactification D f₀ c₀))

end PinnedGeometry

/-- The finite-field point in the retained model category.
Source: blueprint proof step 3 (blueprint: cor-coef-verdier-weil-equivariance). -/
abbrev pointModel (D : FiniteFieldDatum.{u}) : Over (Spec (.of D.k₀)) :=
  Over.mk (𝟙 (Spec (.of D.k₀)))

/-- The same constant coefficient object in the common-stage category.
Source: blueprint proof steps 3 and 8 (blueprint: cor-coef-verdier-weil-equivariance). -/
def commonUnit :=
  @pullbackTensorCommonUnit l _ Ω _ _ _ (D.geometricFiber X₀).left
    (fun x ↦ sfWeilPrimeInvertible D l hl X₀ x)

/-- The specified common-stage left unitor for that coefficient object.
Source: blueprint proof steps 3 and 8 (blueprint: cor-coef-verdier-weil-equivariance). -/
def commonUnitor :
    ∀ M : generalAlgebraicallyClosedConstructibleCategory l Ω (D.geometricFiber X₀).left,
      (@commonStageDerivedTensor l _ Ω _ _ _ (D.geometricFiber X₀).left
        (fun x ↦ sfWeilPrimeInvertible D l hl X₀ x)).obj
          (commonUnit D l hl Ω X₀, M) ≅ M :=
  @pullbackTensorCommonLeftUnitor l _ Ω _ _ _ (D.geometricFiber X₀).left
    (fun x ↦ sfWeilPrimeInvertible D l hl X₀ x)

end Geometric
end WeilConjectures.CoefVerdierWeil
