/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q34
-/
module

public import Sheaf.Paper.SystemTensorMateArrows
public import Sheaf.Paper.SemilinearDerivedSections
public import Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Sheaf.SixFunctors.OpenTensorNormalization
public import Sheaf.SixFunctors.ProperOpenProjectionMate
public import Sheaf.Paper.ExchangeProjectionSuppliedDomains

/-! # Interfaces for strict quotient-system tensor presentations

Source: Stacks Project, sites-cohomology, Tag 0B56,
`equation-projection-formula-map`; sites-modules, Tag 0E8I,
`lemma-j-shriek-and-tensor` (blueprint: lem-pur-system-tensor-presentation-identification).

The published `Systems` model already uses modules on the vertical sequence site.
Its index `a` represents positive coefficient exponent `a+1`. Thus reindexing is
literally the identity in this shared model. The actual geometric and localization
operations of the semilinear datum are compared with the diagram presentation.
The separate proper/open realization interface stays in the importing item module.

## Main declarations

- `SemilinearPresentationComparison`: actual geometric and localization operations.
- `TensorPresentationCore`: comparison data preceding the mate consequences.
- `TensorPresentationComparison`: the full normalized comparison.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genInjectivity false
set_option genSizeOfSpec false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

attribute [local irreducible] CategoryTheory.Functor.mapDerivedCategory
  CategoryTheory.Functor.rightDerivedFunctor CategoryTheory.Functor.leftAdjoint
  WeilConjectures.pullbackTensorCalculus HasDerivedCategory.standard
  CategoryTheory.Functor.mapDerivedCategoryFactors

attribute [local irreducible] WeilConjectures.CoefficientClosedStructure.tensor
  WeilConjectures.SystemTensorMate.Operations.derivedAdj
  WeilConjectures.SystemTensorMate.Operations.derivedOpenAdj
  WeilConjectures.SystemTensorMate.TensorOperations.projection
  WeilConjectures.SystemTensorMate.TensorOperations.deltaInv
  WeilConjectures.SystemTensorMate.TensorOperations.delta
  WeilConjectures.SystemTensorMate.Operations.pComp

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open WeilConjectures.SemilinearSections

namespace WeilConjectures.SystemTensorMate

variable (l : ℕ) [Fact l.Prime] (E : Type (u + 1)) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- Reindex positive coefficient levels by `a = n-1`, leaving sections and
transitions unchanged. Both sides use the dependency's single vertical-site model.
Source: the explicit presentation comparison, Step 1; Stacks 0941
(blueprint: lem-pur-system-tensor-presentation-identification). -/
abbrev presentationReindexing (W : Scheme.{u}) :
    DS.{u + 1, u, u + 1} (Scheme.ProEt.topology W)
        (integralCoefficientCommRingSheaf l E W)
        (coefficientSequenceCommRingTransition l E W) ≌ D l E W :=
  CategoryTheory.Equivalence.refl

/-- The canonical direct-image comparison for reindexing. Sectionwise direct
image is unchanged, and the same total right derived functor is used on both sides.
Source: the explicit presentation comparison, Steps 4--5; Stacks 07A4
(blueprint: lem-pur-system-tensor-presentation-identification). -/
def presentationDirectComparison {X Y : Scheme.{u}} (f : X ⟶ Y) :
    pushDerived l E f ⋙ (presentationReindexing l E Y).functor ≅
      (presentationReindexing l E X).functor ⋙ pushDerived l E f :=
  Functor.rightUnitor _ ≪≫ (Functor.leftUnitor _).symm

variable {l E}

/-- The comparison data through pullback tensor normalization, before the mate
consequences are formed. This records Steps 1--7 of the presentation argument.
Source: Stacks 03EL, 07A4, 0B56; presentation comparison Steps 1--7
(blueprint: def-pur-system-tensor-presentation-core). -/
structure TensorPresentationCore (o d : TensorOperations l E) where
  /-- Comparison of exact pullbacks. -/
  pull : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y),
    o.P f ≅ d.P f
  /-- Comparison of exact open extensions. -/
  extension : ∀ {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j],
    o.J j ≅ d.J j
  /-- Natural derived tensor comparison. -/
  tensor : ∀ W : Scheme.{u},
    o.T W ≅ d.T W
  /-- Identity on the ordinary signed total tensor, after localization. -/
  tensor_model : ∀ (W : Scheme.{u}) (P Q : CochainComplex (S l E W) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients
      (J := coefficientSequenceTopology (Scheme.ProEt.topology W)) (R := R l E W) P)
    (hQ : CochainComplex.IsKFlatIndependentCoefficients
      (J := coefficientSequenceTopology (Scheme.ProEt.topology W)) (R := R l E W) Q),
    (tensor W).hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) =
      (tensorModelIso.{u + 1, u, u + 1}
        (coefficientSequenceTopology (Scheme.ProEt.topology W)) (R l E W)
        (o.systems W).closed (o.systems W).tensorModels P Q hP hQ).inv ≫
      (tensorModelIso.{u + 1, u, u + 1}
        (coefficientSequenceTopology (Scheme.ProEt.topology W)) (R l E W)
        (d.systems W).closed (d.systems W).tensorModels P Q hP hQ).hom
  /-- The specified proper-adjunction units agree. -/
  unit : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) (M : D l E Y),
    (o.derivedAdj f).unit.app M ≫ (pushDerived l E f).map ((pull f).hom.app M) =
      (d.derivedAdj f).unit.app M
  /-- The specified proper-adjunction counits agree. -/
  counit : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) (H : D l E X),
    (pull f).hom.app ((pushDerived l E f).obj H) ≫ (d.derivedAdj f).counit.app H =
      (o.derivedAdj f).counit.app H
  /-- The section-normalized open units agree. -/
  open_unit : ∀ {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] (H : D l E U),
    (o.derivedOpenAdj j).unit.app H ≫
      (o.P j).map ((extension j).hom.app H) ≫
        (pull j).hom.app ((d.J j).obj H) = (d.derivedOpenAdj j).unit.app H
  /-- The open counits agree as well. -/
  open_counit : ∀ {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] (Q : D l E X),
    (extension j).hom.app ((o.P j).obj Q) ≫
      (d.J j).map ((pull j).hom.app Q) ≫ (d.derivedOpenAdj j).counit.app Q =
        (o.derivedOpenAdj j).counit.app Q
  /-- Canonical pullback composition, including identity maps. -/
  composition : ∀ {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (Q : D l E Z),
    (o.pComp f g).hom.app Q ≫ (pull (f ≫ g)).hom.app Q =
      (o.P f).map ((pull g).hom.app Q) ≫
        (pull f).hom.app ((d.P g).obj Q) ≫ (d.pComp f g).hom.app Q
  /-- The actual representative-normalized tensor-pullback isomorphism agrees. -/
  mu : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) (M N : D l E Y),
    (o.P f).map ((tensor Y).hom.app (M, N)) ≫
      (pull f).hom.app ((d.T Y).obj (M, N)) ≫ (d.mu f).hom.app (M, N) =
    (o.mu f).hom.app (M, N) ≫
      (tensor X).hom.app ((o.P f).obj M, (o.P f).obj N) ≫
        (d.T X).map (Prod.mkHom ((pull f).hom.app M) ((pull f).hom.app N))

/-- The full comparison of independently chosen, normalized strict-system
operations in the common published model. Direct image is the same specified
sectionwise functor and its same right derived functor, so its comparison is
identity. Every displayed equality is in the unbounded system category.
Source: Stacks 0B56, 0E8I; the explicit presentation comparison, Steps 1--9
(blueprint: lem-pur-system-tensor-presentation-identification). -/
structure TensorPresentationComparison (o d : TensorOperations l E)
    extends TensorPresentationCore o d where
  /-- The counit-defined projection arrows agree, without inverting them. -/
  projection : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) (H : D l E X) (Q : D l E Y),
    (tensor Y).hom.app ((pushDerived l E f).obj H, Q) ≫ d.projection f H Q =
      o.projection f H Q ≫ (pushDerived l E f).map
        ((tensor X).hom.app (H, (o.P f).obj Q) ≫
          (d.T X).map (Prod.mkHom (𝟙 H) ((pull f).hom.app Q)))
  /-- The canonical open tensor isomorphisms agree. -/
  delta : ∀ {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (H : D l E U) (Q : D l E X),
    (tensor X).hom.app ((o.J j).obj H, Q) ≫
      (d.T X).map (Prod.mkHom ((extension j).hom.app H) (𝟙 Q)) ≫
        (d.delta j H Q).hom =
    (o.delta j H Q).hom ≫
      (extension j).hom.app ((o.T U).obj (H, (o.P j).obj Q)) ≫
        (d.J j).map ((tensor U).hom.app (H, (o.P j).obj Q) ≫
          (d.T U).map (Prod.mkHom (𝟙 H) ((pull j).hom.app Q)))
  /-- The inverse open arrow is the same specified open-unit transpose. -/
  delta_inverse : ∀ {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (H : D l E U) (Q : D l E X),
    (extension j).hom.app ((o.T U).obj (H, (o.P j).obj Q)) ≫
      (d.J j).map ((tensor U).hom.app (H, (o.P j).obj Q) ≫
        (d.T U).map (Prod.mkHom (𝟙 H) ((pull j).hom.app Q))) ≫ d.deltaInv j H Q =
    o.deltaInv j H Q ≫ (tensor X).hom.app ((o.J j).obj H, Q) ≫
      (d.T X).map (Prod.mkHom ((extension j).hom.app H) (𝟙 Q))

/-- The actual semilinear calculus specialized to the coefficient tower of a scheme.
Source: Zheng 4.1, 4.10; Stacks 0941
(blueprint: lem-pur-system-tensor-presentation-identification). -/
abbrev PresentationSections (W : Scheme.{u}) :=
  SemilinearDerivedSectionsData.{u + 1, u, u + 1} (Scheme.ProEt.topology W)
    (integralCoefficientCommRingSheaf l E W)
    (coefficientSequenceCommRingTransition l E W)

/-- Compare the actual geometric calculus, including its inverse-image coefficient
ring, with the diagram operations. The coefficient comparison is fixed by the
original set-sheaf adjunction unit and the constant-section structural map.
Source: Stacks 03D2, 07A4, 0B56; comparison Steps 4--8
(blueprint: lem-pur-system-tensor-presentation-identification). -/
structure GeometricPresentationComparison {X Y : Scheme.{u}} (f : X ⟶ Y)
    (a : PresentationSections (l := l) (E := E) Y) (o : TensorOperations l E)
    (G : Geometry.{u + 1, u, u + 1} (Scheme.ProEt.topology Y)
      (integralCoefficientCommRingSheaf l E Y)
      (coefficientSequenceCommRingTransition l E Y) a.systems
      (Scheme.ProEt.topology X)
      (Scheme.proEtaleSheafInverseImage f (Type (u + 1)))
      (Scheme.proEtaleSheafDirectImage f (Type (u + 1)))
      (Scheme.proEtaleSheafAdjunction f (Type (u + 1)))) where
  /-- The inverse-image coefficients are canonically the constant coefficients on X. -/
  coefficients : ∀ n : ℕ, G.coefficients n ≅ integralCoefficientCommRingSheaf l E X n
  /-- Normalization by the underlying topos unit, on every section. -/
  coefficient_unit : ∀ (n : ℕ) (V : Y.ProEtᵒᵖ),
    ((Scheme.proEtaleSheafAdjunction f (Type (u + 1))).unit.app
      ((sheafCompose (Scheme.ProEt.topology Y) (forget CommRingCat.{u + 1})).obj
        (integralCoefficientCommRingSheaf l E Y n))).hom.app V ≫
      (G.inverseImage n).ringUnderlying.hom.hom.app
        (op ((Scheme.proEtaleBaseChange f).obj V.unop)) ≫
      (forget CommRingCat.{u + 1}).map ((coefficients n).hom.hom.app
        (op ((Scheme.proEtaleBaseChange f).obj V.unop))) =
      (forget CommRingCat.{u + 1}).map
        ((coefficient l E f).hom.app (op (n, V.unop)))
  /-- Compatibility includes the actual non-flat quotient transitions. -/
  coefficient_transition : ∀ n : ℕ,
    (coefficients (n + 1)).hom ≫ coefficientSequenceCommRingTransition l E X n =
      G.coefficientTransition n ≫ (coefficients n).hom
  /-- The assembled coefficient-ring isomorphism, with no alternative sections. -/
  ringIso : systemRing.{u + 1, u, u + 1} (Scheme.ProEt.topology X)
    G.coefficients G.coefficientTransition ≅ R l E X
  /-- Its components are the preceding canonical ring maps. -/
  ringIso_sections : ∀ (n : ℕ) (V : X.ProEtᵒᵖ),
    ringIso.hom.hom.app (op (n, V.unop)) = (coefficients n).hom.hom.app V
  /-- Exact coefficient transport is restriction along the inverse ring isomorphism. -/
  pull : G.pull.mapDerivedCategory ⋙ resD ringIso.inv ≅ o.P f
  /-- The comparison of the specified total right-derived direct images. -/
  push : G.push.rightDerivedFunctor ≅ resD ringIso.inv ⋙ pushDerived l E f
  /-- Tensor on the source, fixed on K-flat representatives below. -/
  sourceTensor : a.systems.closed.tensor ≅ o.T Y
  /-- Tensor after transport of the inverse-image coefficients. -/
  targetTensor : G.target.closed.tensor ⋙ resD ringIso.inv ≅
    ((resD ringIso.inv).prod (resD ringIso.inv)) ⋙ o.T X
  /-- The transported target tensor is normalized on actual K-flat total models. -/
  targetModel : TensorComparisonModel.{u + 1, u, u + 1}
    (coefficientSequenceTopology (Scheme.ProEt.topology X))
    (coefficientSequenceTopology (Scheme.ProEt.topology X))
    (systemRing.{u + 1, u, u + 1} (Scheme.ProEt.topology X)
      G.coefficients G.coefficientTransition) (R l E X) (res ringIso.inv)
    G.target.closed (o.systems X).closed G.target.tensorModels (o.systems X).tensorModels
    targetTensor
  /-- On ordinary pure tensors, scalar transport leaves the two sections unchanged. -/
  target_pure : ∀ (M N : Systems.{u + 1, u, u + 1} (Scheme.ProEt.topology X)
      G.coefficients G.coefficientTransition) (V : (ℕ × X.ProEt)ᵒᵖ)
      (x : M.val.obj V) (y : N.val.obj V),
    ((targetModel.ordinary M N).hom.val.app V)
      (tensorSection.{u + 1, u, u + 1}
        (coefficientSequenceTopology (Scheme.ProEt.topology X))
        (systemRing.{u + 1, u, u + 1} (Scheme.ProEt.topology X)
          G.coefficients G.coefficientTransition) M N V x y) =
      tensorSection.{u + 1, u, u + 1}
        (coefficientSequenceTopology (Scheme.ProEt.topology X)) (R l E X)
        ((res ringIso.inv).obj M) ((res ringIso.inv).obj N) V x y
  /-- The source tensor comparison has the identity total-model normalization. -/
  source_model : ∀ (P Q : CochainComplex (S l E Y) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients
      (J := coefficientSequenceTopology (Scheme.ProEt.topology Y)) (R := R l E Y) P)
    (hQ : CochainComplex.IsKFlatIndependentCoefficients
      (J := coefficientSequenceTopology (Scheme.ProEt.topology Y)) (R := R l E Y) Q),
    sourceTensor.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) =
      (tensorModelIso.{u + 1, u, u + 1}
        (coefficientSequenceTopology (Scheme.ProEt.topology Y)) (R l E Y)
        a.systems.closed a.systems.tensorModels P Q hP hQ).inv ≫
      (tensorModelIso.{u + 1, u, u + 1}
        (coefficientSequenceTopology (Scheme.ProEt.topology Y)) (R l E Y)
        (o.systems Y).closed (o.systems Y).tensorModels P Q hP hQ).hom
  /-- The actual geometric unit, before finite evaluation. -/
  unit : ∀ M : D l E Y,
    G.adjunction.unit.app M ≫ push.hom.app (G.pull.mapDerivedCategory.obj M) ≫
      (pushDerived l E f).map (pull.hom.app M) = (o.derivedAdj f).unit.app M
  /-- The actual geometric counit. -/
  counit : ∀ H : DS.{u + 1, u, u + 1} (Scheme.ProEt.topology X)
      G.coefficients G.coefficientTransition,
    (o.P f).map (push.inv.app H) ≫ pull.inv.app (G.push.rightDerivedFunctor.obj H) ≫
      (resD ringIso.inv).map (G.adjunction.counit.app H) =
        (o.derivedAdj f).counit.app ((resD ringIso.inv).obj H)
  /-- Identification of Geometry.tensorPullback itself, on all unbounded inputs. -/
  mu : ∀ M N : D l E Y,
    (resD ringIso.inv).map (G.tensorPullback.hom.app (M, N)) ≫
      targetTensor.hom.app (G.pull.mapDerivedCategory.obj M, G.pull.mapDerivedCategory.obj N) ≫
      (o.T X).map (Prod.mkHom (pull.hom.app M) (pull.hom.app N)) =
    pull.hom.app (a.systems.closed.tensor.obj (M, N)) ≫
      (o.P f).map (sourceTensor.hom.app (M, N)) ≫ (o.mu f).hom.app (M, N)
  /-- Identification of the recorded semilinear counit-defined projection. -/
  projection : ∀ (H : DS.{u + 1, u, u + 1} (Scheme.ProEt.topology X)
      G.coefficients G.coefficientTransition) (Q : D l E Y),
    G.tensorProjection (Scheme.ProEt.topology Y) (integralCoefficientCommRingSheaf l E Y)
        (coefficientSequenceCommRingTransition l E Y) a.systems (Scheme.ProEt.topology X)
        (Scheme.proEtaleSheafInverseImage f (Type (u + 1)))
        (Scheme.proEtaleSheafDirectImage f (Type (u + 1)))
        (Scheme.proEtaleSheafAdjunction f (Type (u + 1))) H Q ≫
      push.hom.app (G.target.closed.tensor.obj (H, G.pull.mapDerivedCategory.obj Q)) ≫
      (pushDerived l E f).map (targetTensor.hom.app (H, G.pull.mapDerivedCategory.obj Q) ≫
        (o.T X).map (Prod.mkHom (𝟙 _) (pull.hom.app Q))) =
    sourceTensor.hom.app (G.push.rightDerivedFunctor.obj H, Q) ≫
      (o.T Y).map (Prod.mkHom (push.hom.app H) (𝟙 Q)) ≫
        o.projection f ((resD ringIso.inv).obj H) Q

/-- Comparison with the actual localization OpenSystems, using the canonical
slice equivalence on every section and transition. The unit equation fixes the
open-extension comparison, rather than choosing an unrelated tensor arrow.
Source: Stacks 03DI, 0E8I; comparison Steps 4--5 and 9
(blueprint: lem-pur-system-tensor-presentation-identification). -/
structure OpenPresentationComparison {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (a : PresentationSections (l := l) (E := E) X) (o : TensorOperations l E) where
  /-- Localization at the pro-etale object defined by j. -/
  slice : S l E U ≌ Systems.{u + 1, u, u + 1}
    ((Scheme.ProEt.topology X).over (Scheme.ProEt.mk j))
    (openRings.{u + 1, u, u + 1} (Scheme.ProEt.topology X) (integralCoefficientCommRingSheaf l E X)
      (Scheme.ProEt.mk j))
    (openTransitions.{u + 1, u, u + 1} (Scheme.ProEt.topology X)
      (integralCoefficientCommRingSheaf l E X)
      (coefficientSequenceCommRingTransition l E X) (Scheme.ProEt.mk j))
  /-- The slice functor keeps all underlying section groups. -/
  sections : ∀ (M : S l E U) (n : ℕ) (V : Over (Scheme.ProEt.mk j)),
    HEq (((slice.functor.obj M).val.obj (op (n, V))) : Type (u + 1))
      ((M.val.obj (op (n, (Scheme.ProEt.sliceTo X (Scheme.ProEt.mk j)).obj V))) : Type (u + 1))
  /-- Reindexing also keeps every section map of a system morphism. -/
  maps : ∀ {M N : S l E U} (f : M ⟶ N) (n : ℕ)
    (V : Over (Scheme.ProEt.mk j)),
    HEq (fun x ↦ ((slice.functor.map f).val.app (op (n, V))) x)
      (fun x ↦ (f.val.app
        (op (n, (Scheme.ProEt.sliceTo X (Scheme.ProEt.mk j)).obj V))) x)
  /-- Quotient-semilinear transitions are preserved before deriving. -/
  transitions : ∀ (M : S l E U) (n : ℕ) (V : Over (Scheme.ProEt.mk j)),
    HEq (fun x ↦ (slice.functor.obj M).val.map
      (Prod.mkHom (homOfLE (Nat.le_succ n)) (𝟙 V)).op x)
      (fun x ↦ M.val.map (Prod.mkHom (homOfLE (Nat.le_succ n))
        (𝟙 ((Scheme.ProEt.sliceTo X (Scheme.ProEt.mk j)).obj V))).op x)
  /-- The inverse-image comparison with actual slice restriction. -/
  restriction : o.pull j ⋙ slice.functor ≅
    openRestriction.{u + 1, u, u + 1} (Scheme.ProEt.topology X)
      (integralCoefficientCommRingSheaf l E X)
      (coefficientSequenceCommRingTransition l E X) (Scheme.ProEt.mk j)
  /-- The localization supplied by the semilinear derived-sections datum. -/
  extension : slice.functor ⋙ (a.localization (Scheme.ProEt.mk j)).extension ≅ o.extension j
  /-- Its comparison preserves the actual ordinary open unit. -/
  unit : ∀ M : S l E U,
    slice.functor.map ((o.openAdj j).unit.app M) ≫
      restriction.hom.app ((o.extension j).obj M) =
    (a.localization (Scheme.ProEt.mk j)).ordinaryAdjunction.unit.app
        (slice.functor.obj M) ≫
      (openRestriction.{u + 1, u, u + 1} (Scheme.ProEt.topology X)
        (integralCoefficientCommRingSheaf l E X)
        (coefficientSequenceCommRingTransition l E X) (Scheme.ProEt.mk j)).map
          (extension.hom.app M)

/-- The source side is the specified semilinear calculus, not a second arbitrary
TensorOperations package. Both geometric and localization operations are retained.
Source: Zheng 4.1, 4.10; Stacks 03DI, 07A4, 0B56
(blueprint: lem-pur-system-tensor-presentation-identification). -/
structure SemilinearPresentationComparison
    (a : ∀ W : Scheme.{u}, PresentationSections (l := l) (E := E) W)
    (o : TensorOperations l E) where
  /-- The tensor calculus on each scheme is the one supplied by a. -/
  systems : ∀ W : Scheme.{u}, o.systems W = (a W).systems
  /-- The actual geometric operation for the pro-etale morphism of topoi. -/
  geometric : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y)
    (h : PreservesFiniteLimits (Scheme.proEtaleSheafInverseImage f (Type (u + 1)))),
    Nonempty (GeometricPresentationComparison f (a Y) o
      (@SemilinearDerivedSectionsData.geometric.{u + 1, u, u + 1}
        _ _ _ _ _ _ (a Y) _ _ _
        (Scheme.ProEt.topology X) (Scheme.proEtaleSheafInverseImage f (Type (u + 1)))
        (Scheme.proEtaleSheafDirectImage f (Type (u + 1)))
        (Scheme.proEtaleSheafAdjunction f (Type (u + 1))) h).val)
  /-- Open operations are the published localization OpenSystems. -/
  localization : ∀ {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j],
    Nonempty (OpenPresentationComparison j (a X) o)

end WeilConjectures.SystemTensorMate

