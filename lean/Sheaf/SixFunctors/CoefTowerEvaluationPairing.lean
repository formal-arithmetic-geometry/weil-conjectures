/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q04
-/
module

public import Sheaf.SixFunctors.CoefTowerTraceRectification
public import Sheaf.Paper.CoefDerivedSystemEvaluationCalculus
public import Sheaf.Paper.FiniteTorAmplitude
public import Sheaf.AlgebraicGeometry.ProEtaleTorAmplitude
public import Sheaf.Paper.IntrinsicFiniteTorsionConstructibility
public import Sheaf.Paper.SfIntegralConstructible
public import Sheaf.AlgebraicGeometry.ProEtaleCohomologicalSupport
public import Sheaf.Paper.SfDerivedComplete
public import Sheaf.Paper.CompactSupportReductionTower
public import Sheaf.AlgebraicGeometry.SfIntrinsicCompactSupport
public import WeilConjectures.CategoryTheory.DerivedCategory.HasMonoidalDerivedCategory
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution
public import Mathlib.CategoryTheory.Monoidal.Closed.FunctorCategory.Basic
public import Mathlib.CategoryTheory.Monoidal.FunctorCategory
public import WeilConjectures.CategoryTheory.Adjunction.ProjectionMap

import Mathlib.CategoryTheory.Generator.Presheaf
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.FunctorCategory
import Sheaf.Paper.CoefficientRingedSequenceSite
import Sheaf.Paper.CoefficientRingedTensorHomModel
import Sheaf.Paper.CoefficientHomRepresentativeEvaluation
import Sheaf.Paper.ExchangeProjectionSuppliedDomains
import Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses
import Sheaf.Paper.FiniteCoefficientPoint
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.CategoryTheory.PreDerivedAdjointFunctorsGeneral
import Sheaf.Algebra.Homology.KInjectiveHomComplex
import Sheaf.Algebra.Homology.RingedDerivedClosedSymmetricMonoidal
import Sheaf.Algebra.Homology.ScalarInternalHomAdjunction
import Sheaf.SixFunctors.RingedDerivedMonoidalComparisons
import Sheaf.Paper.DerivedScalarExtensionRestrictionAdjunction
import Sheaf.Paper.ProjectionMateExact
import Sheaf.CategoryTheory.RingedSliceExtensionExactness
import Sheaf.CategoryTheory.RingedSliceExtensionTensor
import Sheaf.Paper.RingedTopoiDerivedPullback
import Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition
import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
import Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
import Sheaf.CategoryTheory.RingedTowerPushforwardLimitComparison
import Sheaf.CategoryTheory.RingedToposMorphism
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import WeilConjectures.Algebra.Homology.TowerEvaluationKInjective
import Sheaf.Paper.SemilinearDerivedSections

/-! # Evaluation and compact support before taking inverse limits

Source: blueprint `prop-coef-integral-dualizing`, proof paragraph 2
(blueprint: lem-coef-tower-evaluation-pairing).
The index n denotes positive exponent n+1. The target is the already fixed
compact-support tower, before its trace. All constructions retain the tower index.

## Main definitions

- `coefPairingHom`, `coefPairingSupport`: the contravariant and covariant towers.
- `CoefPairingSystem.beta`: the adjunction-mate/evaluation composite before trace.
- `coefPairingFiniteBeta`: its ambient finite-level formula, including scalar balancing.

## Main statements

- `coefTowerEvaluationPairing`: representative computation, finite evaluation and dinaturality.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u a v
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped MonoidalClosed.FunctorCategory
open SheafOfModules
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- The strict module-tower category used by the fixed trace target.
Source: blueprint proof paragraph 2 (blueprint: lem-coef-tower-evaluation-pairing). -/
abbrev coefPairingModules := ℕᵒᵖ ⥤ ModuleCat.{u + 1} (coefTraceRing l E)

/-- Module towers are Grothendieck abelian, without transition-surjectivity hypotheses.
Source: Stacks 0941 (blueprint: lem-coef-tower-evaluation-pairing).
Proof: use module-valued presheaves on the small poset of natural numbers.
Filtered colimits and exactness are levelwise; coproducts of the free representables
form a generator. This is also the trivial-topology sheaf presentation. -/
@[instance] theorem coefPairingModules_grothendieck :
    IsGrothendieckAbelian.{u + 1} (coefPairingModules l E) := by
  exact { ab5OfSize := ⟨fun _ _ _ ↦ inferInstance⟩ }

/-- Functorial flat resolutions for the pointwise tensor of strict module towers.
Source: Stacks 06YY, 0941 (blueprint: lem-coef-tower-evaluation-pairing).
Proof: take the coproduct of free module-valued representables. Each value is free,
so tensor with it preserves finite limits levelwise. The free representables form
a flat separator. Apply the functorial-flat-resolution theorem for flat separators. -/
@[instance] theorem coefPairingModules_flat :
    Abelian.HasFunctorialFlatResolution (coefPairingModules l E) := by
  obtain ⟨G, hG, hflat⟩ :=
    Abelian.exists_flat_separator_of_hasFunctorialFlatResolution
      (ModuleCat.{u + 1} (coefTraceRing l E))
  apply Abelian.hasFunctorialFlatResolution_of_flat_separator _
    (Presheaf.isSeparator ℕ (S := fun _ : ULift.{u + 1} Unit ↦ G) (by
      intro X Y f g h
      exact hG.def f g (fun k ↦ h G ⟨ULift.up ()⟩ k)))
  apply ObjectProperty.flat_coproduct
  rintro ⟨n, _⟩
  rw [ObjectProperty.flat_iff_preservesFiniteLimits]
  have (m : ℕᵒᵖ) :
      PreservesFiniteLimits (tensorLeft ((Presheaf.freeYoneda n G).obj m)) :=
    (ObjectProperty.flat_iff_preservesFiniteLimits _).1
      (ObjectProperty.prop_of_iso ObjectProperty.flat
        (Sigma.reindex (Equiv.ulift : ULift.{u + 1} _ ≃ _) _)
        (ObjectProperty.flat_coproduct _ fun _ ↦ hflat))
  exact preservesFiniteLimits_of_evaluation _ fun m ↦
    inferInstanceAs (PreservesFiniteLimits
      ((evaluation ℕᵒᵖ (ModuleCat.{u + 1} (coefTraceRing l E))).obj m ⋙
        tensorLeft ((Presheaf.freeYoneda n G).obj m)))

/-- The ordinary unbounded derived category of strict R-module towers.
Source: Stacks 0941 (blueprint: lem-coef-tower-evaluation-pairing). -/
abbrev coefPairingDerived := DerivedCategory (coefPairingModules l E)

/-- The derived tensor of towers, constructed by the existing K-flat localization.
Source: Stacks 06YY, 0941 (blueprint: lem-coef-tower-evaluation-pairing). -/
def coefPairingTensor : coefPairingDerived l E × coefPairingDerived l E ⥤
    coefPairingDerived l E := MonoidalCategory.tensor _

/-- Sections after actual quotient-scalar restriction, retaining the strict tower.
Source: blueprint proof paragraph 2 (blueprint: lem-coef-tower-evaluation-pairing). -/
def coefPairingSections (W : Scheme.{u}) :
    coefficientSequenceDerived.{u, u} l E W ⥤ coefPairingDerived l E :=
  (coefTraceSystemRestriction l E W).mapDerivedCategory ⋙
    (coefTraceSections l E W).rightDerivedFunctor

/-- The contravariant Hom tower. Scalar adjunction identifies this with termwise
Hom from K into a simultaneous K-injective resolution of Res Q.
Source: blueprint proof paragraph 2 (blueprint: lem-coef-tower-evaluation-pairing). -/
def coefPairingHom (X : Scheme.{u}) (S : CoefficientDerivedSystemCalculus l E X)
    (Q : CochainComplex (coefficientSequenceModules.{u, u} l E X) ℤ) :
    (DerivedCategory (scalarReductionSource.{u, u} l E X))ᵒᵖ ⥤ coefPairingDerived l E :=
  S.reduction.op ⋙ Prod.sectL _ (coefTraceInput l E X Q) ⋙
    coefficientSequenceInternalHom l E X ⋙ coefPairingSections l E X

/-- The covariant compact-support reduction tower with separately derived proper
image and point sections, using the same compactification as B_omega.
Source: blueprint proof paragraph 2 (blueprint: lem-coef-tower-evaluation-pairing). -/
def coefPairingSupport (D : FiniteFieldDatum.{u}) (X : Scheme.{u})
    [X.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
    [QuasiCompact (X ↘ Spec (.of D.k))] [IsSeparated (X ↘ Spec (.of D.k))]
    (S : CoefficientDerivedSystemCalculus l E X) :
    DerivedCategory (scalarReductionSource.{u, u} l E X) ⥤ coefPairingDerived l E :=
  S.reduction ⋙ coefTraceCompactSections l E (finiteDualizingCompactification D X)


end WeilConjectures

namespace CategoryTheory

universe b c d v₁ v₂ v₃ v₄

/-- The adjoint-evaluation construction used on both the sequence site and its finite
slices. The functors J, P, R and RX are supplied independently: exact open extension,
separately derived proper image, point sections and source sections, respectively.
No invertibility of a proper or sections projection mate is included.
Source: blueprint proof steps 5--8 (blueprint: lem-coef-tower-evaluation-pairing). -/
structure CoefPairingFrame
    {A : Type a} {B : Type b} {C : Type c} {D : Type d}
    [Category.{v₁} A] [Category.{v₂} B] [Category.{v₃} C] [Category.{v₄} D]
    (TA : A × A ⥤ A) (TB : B × B ⥤ B) (TC : C × C ⥤ C) (TD : D × D ⥤ D)
    (J : A ⥤ B) (P : B ⥤ C) (R : C ⥤ D) (RX : A ⥤ D) where
  /-- Derived restriction to the open subsite. -/
  jstar : B ⥤ A
  /-- Exact open extension is left adjoint to open restriction. -/
  openAdjunction : J ⊣ jstar
  /-- Derived pullback along the proper part. -/
  pstar : C ⥤ B
  /-- The ringed derived pullback/direct-image adjunction. -/
  properAdjunction : pstar ⊣ P
  /-- Derived extension of the constant base scalars after point pullback. -/
  sstar : D ⥤ C
  /-- Point sections, including scalar restriction, are its right adjoint. -/
  sectionsAdjunction : sstar ⊣ R
  /-- Pullback composition identifies source sections with this right adjoint. -/
  sourceAdjunction : sstar ⋙ pstar ⋙ jstar ⊣ RX
  /-- Canonical tensor pullback comparison along p. -/
  properTensor : TC ⋙ pstar ≅ pstar.prod pstar ⋙ TB
  /-- Canonical tensor pullback comparison along point sections and scalar extension. -/
  sectionsTensor : TD ⋙ sstar ≅ sstar.prod sstar ⋙ TC
  /-- Canonical tensor pullback along open restriction. -/
  restrictionTensor : TB ⋙ jstar ≅ jstar.prod jstar ⋙ TA
  /-- The inverse-open-projection arrow is the actual counit mate. -/
  openTensor : ∀ (L : B) (M : A), J.obj (TA.obj (jstar.obj L, M)) ≅ TB.obj (L, J.obj M)
  /-- Its adjunct is insertion into j* j!, following inverse tensor comparison. -/
  openTensor_adjunct : ∀ (L : B) (M : A),
    openAdjunction.homEquiv _ _ (openTensor L M).hom =
      TA.map (Prod.mkHom (𝟙 (jstar.obj L)) (openAdjunction.unit.app M)) ≫
        restrictionTensor.inv.app (L, J.obj M)

namespace CoefPairingFrame

variable {A : Type a} {B : Type b} {C : Type c} {D : Type d}
  [Category.{v₁} A] [Category.{v₂} B] [Category.{v₃} C] [Category.{v₄} D]
  {TA : A × A ⥤ A} {TB : B × B ⥤ B} {TC : C × C ⥤ C} {TD : D × D ⥤ D}
  {J : A ⥤ B} {P : B ⥤ C} {R : C ⥤ D} {RX : A ⥤ D}
  (F : CoefPairingFrame TA TB TC TD J P R RX)

/-- The left-oriented projection mate, obtained by transposing tensor of the counit.
It is the usual projection mate conjugated by the canonical graded symmetries.
Source: blueprint steps 7--8 (blueprint: lem-coef-tower-evaluation-pairing). -/
def leftMate {V : Type a} {W : Type b} [Category.{v₁} V] [Category.{v₂} W]
    (TV : V × V ⥤ V) (TW : W × W ⥤ W) (L : V ⥤ W) (G : W ⥤ V)
    (adj : L ⊣ G) (mu : TV ⋙ L ≅ L.prod L ⋙ TW) (H : V) (M : W) :
    TV.obj (H, G.obj M) ⟶ G.obj (TW.obj (L.obj H, M)) :=
  let flip := (Functor.flipping (C := V) (D := V) (E := W)).functor
  ((adj.rightAdjointProjectionMap
    (T_C := (Functor.curryObj TW).flip) (T_D := (Functor.curryObj TV).flip)
    (flip.map (Functor.curry.map mu.hom) ≫
      (flip.mapIso (Functor.curryObjProdComp L L TW)).hom)).app M).app H

/-- The composite of the point-sections mate, proper mate and open tensor inverse.
All three arrows live in the derived system categories before finite evaluation.
Source: blueprint steps 5--8 (blueprint: lem-coef-tower-evaluation-pairing). -/
def projection (H : D) (M : A) :
    TD.obj (H, R.obj (P.obj (J.obj M))) ⟶
      R.obj (P.obj (J.obj (TA.obj (F.jstar.obj (F.pstar.obj (F.sstar.obj H)), M)))) :=
  leftMate TD TC F.sstar R F.sectionsAdjunction F.sectionsTensor H (P.obj (J.obj M)) ≫
    R.map (leftMate TC TB F.pstar P F.properAdjunction F.properTensor
      (F.sstar.obj H) (J.obj M)) ≫
    R.map (P.map (F.openTensor (F.pstar.obj (F.sstar.obj H)) M).inv)

/-- Evaluation after the source-sections counit, followed by compact support.
This formula includes the scalar-balancing map through sstar. It ends at F(Q);
no exceptional counit or trace is composed into it.
Source: blueprint steps 6--8 (blueprint: lem-coef-tower-evaluation-pairing). -/
def pairing {HA : Aᵒᵖ × A ⥤ A} (S : WeilConjectures.CoefficientClosedStructure HA)
    (tensor_eq : S.tensor = TA) (M Q : A) :
    TD.obj (RX.obj (HA.obj (op M, Q)), R.obj (P.obj (J.obj M))) ⟶
      R.obj (P.obj (J.obj Q)) :=
  F.projection (RX.obj (HA.obj (op M, Q))) M ≫
    R.map (P.map (J.map
      (TA.map (Prod.mkHom (F.sourceAdjunction.counit.app (HA.obj (op M, Q))) (𝟙 M)) ≫
        eqToHom (congrArg (fun T ↦ T.obj (HA.obj (op M, Q), M)) tensor_eq.symm) ≫
          S.evaluation M Q)))

end CoefPairingFrame
end CategoryTheory

namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- Ordinary final-object sections are additive with the fixed integral scalar action.
Source: Stacks 0941 (blueprint: lem-coef-tower-evaluation-pairing).
Proof: sections add pointwise and restriction of scalars changes no addition of maps. -/
@[instance] theorem coefPairingOrdinarySections_additive (W : Scheme.{u}) :
    ((sheafSections (ProEt.topology W) (ModuleCat.{u + 1} (coefTraceRing l E))).obj
      (op (ProEt.mk (𝟙 W)))).Additive where
  map_add := rfl

/-- Ordinary sections with the fixed constant integral action, prior to deriving.
Source: blueprint step 2 (blueprint: lem-coef-tower-evaluation-pairing). -/
def coefPairingOrdinaryIntegralSections (W : Scheme.{u}) :
    scalarReductionSource.{u, u} l E W ⥤ ModuleCat.{u + 1} (coefTraceRing l E) :=
  coefTraceConstantScalars l E W ⋙
    (sheafSections (ProEt.topology W) (ModuleCat.{u + 1} (coefTraceRing l E))).obj
      (op (ProEt.mk (𝟙 W)))

/-- Additivity of ordinary integral sections follows from its two factors.
Source: blueprint step 2 (blueprint: lem-coef-tower-evaluation-pairing). -/
instance coefPairingOrdinaryIntegralSections_additive (W : Scheme.{u}) :
    (coefPairingOrdinaryIntegralSections l E W).Additive :=
  inferInstanceAs (_ ⋙ _).Additive

/-- The component differential vanishes outside the cochain shape.
Source: Stacks 0941 (blueprint: lem-coef-tower-evaluation-pairing).
Proof: evaluate the natural transformation at each tower index. Its component is
(F.obj n).d i j, which is zero by the shape axiom of that complex. Natural
transformations are equal when all their components are equal. -/
theorem coefPairingComplexTower_shape {A : Type a} [Category.{v} A]
    [HasZeroMorphisms A] (F : ℕᵒᵖ ⥤ CochainComplex A ℤ) (i j : ℤ)
    (_h : ¬ (ComplexShape.up ℤ).Rel i j) :
    Functor.whiskerLeft F (HomologicalComplex.dNatTrans A (.up ℤ) i j) = 0 := by
  ext n
  dsimp
  change (F.obj n).d i j = 0
  exact F.obj n |>.shape i j _h

/-- The reassembled differential squares to zero.
Source: Stacks 0941 (blueprint: lem-coef-tower-evaluation-pairing).
Proof: evaluate at n. The composite becomes (F.obj n).d i j followed by
(F.obj n).d j k, which is zero by d_comp_d of the component complex.
Extensionality of natural transformations proves the displayed identity. -/
theorem coefPairingComplexTower_d_comp_d {A : Type a} [Category.{v} A]
    [HasZeroMorphisms A] (F : ℕᵒᵖ ⥤ CochainComplex A ℤ) (i j k : ℤ) :
    Functor.whiskerLeft F (HomologicalComplex.dNatTrans A (.up ℤ) i j) ≫
      Functor.whiskerLeft F (HomologicalComplex.dNatTrans A (.up ℤ) j k) = 0 := by
  ext n
  dsimp
  change (F.obj n).d i j ≫ (F.obj n).d j k = 0
  exact F.obj n |>.d_comp_d i j k

/-- Reassemble a strict functor to complexes as a complex of strict towers.
Source: Stacks 0941 (blueprint: lem-coef-tower-evaluation-pairing). -/
def coefPairingComplexTower {A : Type a} [Category.{v} A]
    [HasZeroMorphisms A] (F : ℕᵒᵖ ⥤ CochainComplex A ℤ) :
    CochainComplex (ℕᵒᵖ ⥤ A) ℤ where
  X i := F ⋙ HomologicalComplex.eval A (.up ℤ) i
  d i j := Functor.whiskerLeft F (HomologicalComplex.dNatTrans A (.up ℤ) i j)
  shape i j h := coefPairingComplexTower_shape F i j h
  d_comp_d' i j k _ _ := coefPairingComplexTower_d_comp_d F i j k

/-- The termwise global Hom complex from P to a simultaneous completed-module tower I.
Its arrows are postcomposition by the actual transitions of I, with the usual Hom
complex differential. It retains the integral scalar action before localization.
Source: blueprint step 2 (blueprint: lem-coef-tower-evaluation-pairing). -/
def coefPairingHomComplex (X : Scheme.{u})
    (P : CochainComplex (scalarReductionSource.{u, u} l E X) ℤ)
    (I : CochainComplex (ℕᵒᵖ ⥤ scalarReductionSource.{u, u} l E X) ℤ) :
    CochainComplex (coefPairingModules l E) ℤ :=
  coefPairingComplexTower
    (I.asFunctor ⋙
      (homComplexFunctor.{u + 1, u, u + 1, u + 1}
        (R := completedIntegralCommRingSheafUnrestricted l E X)).obj (op P) ⋙
      (coefPairingOrdinaryIntegralSections l E X).mapHomologicalComplex (.up ℤ))

/-- R-linear derived sections of completed-module sheaves.
Source: blueprint step 2 (blueprint: lem-coef-tower-evaluation-pairing). -/
def coefPairingIntegralSections (W : Scheme.{u}) :
    DerivedCategory (scalarReductionSource.{u, u} l E W) ⥤
      DerivedCategory (ModuleCat.{u + 1} (coefTraceRing l E)) :=
  (coefTraceConstantScalars l E W).mapDerivedCategory ⋙
    ((sheafSections (ProEt.topology W) (ModuleCat.{u + 1} (coefTraceRing l E))).obj
      (op (ProEt.mk (𝟙 W)))).rightDerivedFunctor

/-- Finite sections with the actual quotient-induced R action.
Source: blueprint step 9 (blueprint: lem-coef-tower-evaluation-pairing). -/
def coefPairingFiniteSections (W : Scheme.{u}) (n : ℕ) :
    normalizedDVRDerived.{u, u} l E W n ⥤
      DerivedCategory (ModuleCat.{u + 1} (coefTraceRing l E)) :=
  scalarReductionDerivedRestriction l E W n ⋙ coefPairingIntegralSections l E W

/-- Finite Hom before forgetting its quotient scalar action.
Source: blueprint step 2 (blueprint: lem-coef-tower-evaluation-pairing). -/
def coefPairingFiniteHom (X : Scheme.{u}) (n : ℕ) (N : normalizedDVRDerived.{u, u} l E X n) :
    (DerivedCategory (scalarReductionSource.{u, u} l E X))ᵒᵖ ⥤
      DerivedCategory (ModuleCat.{u + 1} (coefTraceRing l E)) :=
  (scalarReductionDerivedExtension l E X n).op ⋙ Prod.sectL _ N ⋙
    coefficientFiniteInternalHom l E X n ⋙ coefPairingFiniteSections l E X n


/-- The first finite Hom description, over the completed coefficient ring R_X.
Source: blueprint step 2 (blueprint: lem-coef-tower-evaluation-pairing). -/
def coefPairingIntegralHom (X : Scheme.{u}) (n : ℕ)
    (N : normalizedDVRDerived.{u, u} l E X n) :
    (DerivedCategory (scalarReductionSource.{u, u} l E X))ᵒᵖ ⥤
      DerivedCategory (ModuleCat.{u + 1} (coefTraceRing l E)) :=
  Prod.sectL _ ((scalarReductionDerivedRestriction l E X n).obj N) ⋙
    coefficientIntegralInternalHom l E X ⋙ coefPairingIntegralSections l E X

/-- The existing Grothendieck instance on the actual quotient sequence site.
Source: Stacks 079P (blueprint: lem-coef-tower-evaluation-pairing). -/
instance coefPairingSequenceGrothendieck (W : Scheme.{u}) :
    IsGrothendieckAbelian.{u + 1} (coefficientSequenceModules.{u, u} l E W) :=
  (grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses.{u + 1, u, u + 1}
    (coefficientSequenceTopology (ProEt.topology W))
    (coefficientSequenceCommRingSheaf l E W)).1

/-- Ordinary quotient-ring open extension and proper image, together with the actual
scalar-restriction comparisons. These are witnesses of the fixed ringed construction,
not hypotheses on K. The proper image is derived after open extension.
Source: blueprint steps 1 and 4--8 (blueprint: lem-coef-tower-evaluation-pairing). -/
structure CoefPairingSystem {X Y : Scheme.{u}} {a : X ⟶ Y}
    (c : Compactification a) (S : CoefficientDerivedSystemCalculus l E X) where
  /-- The existing K-flat tensor-Hom data on the compactification. -/
  compactTensors : CoefficientDerivedSystemTensors l E c.Z
  /-- The existing K-flat tensor-Hom data on the base. -/
  baseTensors : CoefficientDerivedSystemTensors l E Y
  /-- Exact module-sheaf extension by zero on the quotient sequence site. -/
  openModules : coefficientSequenceModules.{u, u} l E X ⥤
    coefficientSequenceModules.{u, u} l E c.Z
  /-- The separately derived ordinary module-sheaf direct image. -/
  properModules : coefficientSequenceModules.{u, u} l E c.Z ⥤
    coefficientSequenceModules.{u, u} l E Y
  [openAdditive : openModules.Additive]
  [openLimits : PreservesFiniteLimits openModules]
  [openColimits : PreservesFiniteColimits openModules]
  [properAdditive : properModules.Additive]
  /-- The underlying open operation is the recorded actual extension by zero. -/
  openRestriction : openModules ⋙ coefTraceSystemRestriction l E c.Z ≅
    coefTraceSystemRestriction l E X ⋙ coefTraceOpen l E c.i
  /-- The underlying proper operation is the recorded actual direct image. -/
  properRestriction : properModules ⋙ coefTraceSystemRestriction l E Y ≅
    coefTraceSystemRestriction l E c.Z ⋙ coefTracePush l E c.g
  /-- Ambient adjunctions, canonical pullback tensor comparisons and open tensor mate. -/
  frame : CoefPairingFrame S.systemClosed.tensor compactTensors.systemClosed.tensor
    baseTensors.systemClosed.tensor (coefPairingTensor l E)
    openModules.mapDerivedCategory properModules.rightDerivedFunctor
    (coefPairingSections l E Y) (coefPairingSections l E X)
  /-- The direct-image composition comparison after exact scalar restriction. -/
  compactSections : openModules.mapDerivedCategory ⋙ properModules.rightDerivedFunctor ⋙
    coefPairingSections l E Y ≅ coefTraceCompactSections l E c

attribute [instance] CoefPairingSystem.openAdditive CoefPairingSystem.openLimits
  CoefPairingSystem.openColimits CoefPairingSystem.properAdditive

/-- The actual system pairing: two projection mates and evaluation, transported by the
scalar-restriction/direct-image comparison to the already fixed compact-support tower.
Source: blueprint steps 6--8 (blueprint: lem-coef-tower-evaluation-pairing). -/
def CoefPairingSystem.beta {X Y : Scheme.{u}} {a : X ⟶ Y} {c : Compactification a}
    {S : CoefficientDerivedSystemCalculus l E X} (G : CoefPairingSystem l E c S)
    (M Q : coefficientSequenceDerived.{u, u} l E X) :
    (coefPairingTensor l E).obj
        ((coefPairingSections l E X).obj ((coefficientSequenceInternalHom l E X).obj (op M, Q)),
          (coefTraceCompactSections l E c).obj M) ⟶
      (coefTraceCompactSections l E c).obj Q :=
  (coefPairingTensor l E).map (Prod.mkHom (𝟙 _) (G.compactSections.inv.app M)) ≫
    G.frame.pairing S.systemClosed rfl M Q ≫ G.compactSections.hom.app Q

/-- The finite compact-support/sections functor, with quotient restriction to R.
Source: blueprint step 9 (blueprint: lem-coef-tower-evaluation-pairing). -/
def coefPairingFiniteSupport {X Y : Scheme.{u}} {a : X ⟶ Y}
    (c : Compactification a) (n : ℕ) :
    normalizedDVRDerived.{u, u} l E X n ⥤
      DerivedCategory (ModuleCat.{u + 1} (coefTraceRing l E)) :=
  sfIntrinsicCompactSupport c (Padic.coefficientExtensionRing l E (n + 1)) ⋙
    coefPairingFiniteSections l E Y n

/-- The ambient finite projection/evaluation frame, using the recorded intrinsic open
extension, proper direct image and quotient-linear point sections. Its section mate
includes balancing from R to A_n; neither projection mate is assumed invertible.
Source: blueprint step 9 (blueprint: lem-coef-tower-evaluation-pairing). -/
abbrev CoefPairingFiniteFrame {X Y : Scheme.{u}} {a : X ⟶ Y}
    (c : Compactification a) (S : CoefficientDerivedSystemCalculus l E X)
    (G : CoefPairingSystem l E c S) (n : ℕ) :=
  CoefPairingFrame (S.finiteClosed n).tensor (G.compactTensors.finiteClosed n).tensor
    (G.baseTensors.finiteClosed n).tensor
    (MonoidalCategory.tensor (DerivedCategory (ModuleCat.{u + 1} (coefTraceRing l E))))
    (sfIntrinsicExtensionByZero c.i (Padic.coefficientExtensionRing l E (n + 1))).mapDerivedCategory
    (proEtaleConstantDerivedDirectImage c.g (Padic.coefficientExtensionRing l E (n + 1)))
    (coefPairingFiniteSections l E Y n) (coefPairingFiniteSections l E X n)

/-- The finite ambient projection followed by evaluation, before trace.
Source: blueprint step 9 (blueprint: lem-coef-tower-evaluation-pairing). -/
def coefPairingFiniteBeta {X Y : Scheme.{u}} {a : X ⟶ Y}
    (c : Compactification a) (S : CoefficientDerivedSystemCalculus l E X)
    (G : CoefPairingSystem l E c S) (n : ℕ) (F : CoefPairingFiniteFrame l E c S G n)
    (M Q : normalizedDVRDerived.{u, u} l E X n) :
    (coefPairingFiniteSections l E X n).obj
        ((coefficientFiniteInternalHom l E X n).obj (op M, Q)) ⊗
          (coefPairingFiniteSupport l E c n).obj M ⟶
      (coefPairingFiniteSupport l E c n).obj Q :=
  F.pairing (S.finiteClosed n) rfl M Q

variable (D : FiniteFieldDatum.{u}) (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
  [QuasiCompact (X ↘ Spec (.of D.k))] [IsSeparated (X ↘ Spec (.of D.k))]

/-- The finite compact-support functor on integral inputs, with its actual reductions.
Source: blueprint statement C_n (blueprint: lem-coef-tower-evaluation-pairing). -/
def coefPairingFiniteC (n : ℕ) :
    DerivedCategory (scalarReductionSource.{u, u} l E X) ⥤
      DerivedCategory (ModuleCat.{u + 1} (coefTraceRing l E)) :=
  scalarReductionDerivedExtension l E X n ⋙
    coefPairingFiniteSupport l E (finiteDualizingCompactification D X) n

/-- Simultaneous existence, finite evaluation and dinaturality of the tower evaluation
pairing. All implementation witnesses are conclusions, not additional assumptions.

Source: blueprint prop-coef-integral-dualizing, proof paragraph 2, expanded node proof
steps 1--10 (blueprint: lem-coef-tower-evaluation-pairing).

Proof:
1. Use the quotient sequence sites and the same separately derived compact-support
composite as coefTowerTraceRectification. Restriction is exact on underlying sheaves.
2. Resolve K by a flat-term K-flat P, and Res Q by a simultaneous K-injective tower I.
Hom(const P,I) is K-injective; its slices are Hom(P,I_n). Evaluation preserves
K-injectives for constant-ring towers. Scalar adjunction therefore identifies the
resulting R-linear Hom tower with coefPairingHom, including its contravariant maps.
3. Closed tensor transposition and the scalar adjunction identify the full system
Hom, not merely its evaluated objects. The comparison carries evaluation counits.
4. The strict quotient system P tensor A_n computes S.reduction. Exact open extension,
separately derived proper image and sections identify its compact support with the
specified reduction tower, naturally for all quotient maps.
5. Construct the open tensor comparison on module complexes, by the local formula
m tensor l maps to m tensor l restricted to X. The same formula commutes with every
quotient restriction. A K-flat replacement of l gives the derived open comparison.
6. Use pullback composition and the source-sections counit, followed by the recorded
closed evaluation, to obtain the system evaluation morphism.
7. Apply the counit-defined proper projection mate and the open tensor comparison.
8. Apply the sections projection mate with the scalar restriction included in its
left adjoint. This is exactly scalar balancing followed by the system pairing.
This yields G.beta in the derived category of strict R-module towers, with target
coefTraceDualizingTower. No invertibility of a projection mate has been used.
9. Evaluate normalized resolution models. Direct-image composition, coefficient
restriction and evaluation tensor comparisons carry units, counits and the open
chain map to their finite counterparts. Hence the evaluated map is precisely
coefPairingFiniteBeta: balancing, ambient compact-support projection, evaluation.
The same comparisons give eH, eB and eQcompact; the supplied eQ identifies Q_n with
omega_n, with its actual counit-defined transitions. No inverse limit or trace is used.
10. For f:K to K', naturality of closed evaluation and the source counit gives the
identity before compact support. Naturality of both projection mates and of the
open tensor comparison carries it to the displayed dinaturality in the derived
tower category. This does not invoke fullness of finite evaluation. -/
theorem coefTowerEvaluationPairing (hl : l ≠ D.p)
    (Q : CochainComplex (coefficientSequenceModules.{u, u} l E X) ℤ)
    (eQ : ∀ n : ℕ,
      (coefficientSequenceDerivedEvaluation.{u, u} l E X n).obj (coefTraceInput l E X Q) ≅
        integralDualizingFiniteTerm l E D X n)
    (_hQ : ∀ {m n : ℕ} (h : n ≤ m),
      (coefficientSequenceDerivedTransition.{u, u} l E X h).app (coefTraceInput l E X Q) ≫
          (normalizedDVRRes.{u, u} l E X h).map (eQ n).hom =
        (eQ m).hom ≫ integralDualizingExceptionalTransition l E D X hl h) :
    ∃ (S : CoefficientDerivedSystemCalculus l E X)
      (G : CoefPairingSystem l E (finiteDualizingCompactification D X) S)
      (F : ∀ n : ℕ,
        CoefPairingFiniteFrame l E (finiteDualizingCompactification D X) S G n)
      (evaluationTensor : ∀ n : ℕ,
        coefPairingTensor l E ⋙ coefTraceEvaluation l E n ≅
          (coefTraceEvaluation l E n).prod (coefTraceEvaluation l E n) ⋙
            MonoidalCategory.tensor
              (DerivedCategory (ModuleCat.{u + 1} (coefTraceRing l E))))
      (eIntegralHom : ∀ n : ℕ,
        coefPairingHom l E X S Q ⋙ coefTraceEvaluation l E n ≅
          coefPairingIntegralHom l E X n (integralDualizingFiniteTerm l E D X n))
      (eH : ∀ n : ℕ,
        coefPairingHom l E X S Q ⋙ coefTraceEvaluation l E n ≅
          coefPairingFiniteHom l E X n (integralDualizingFiniteTerm l E D X n))
      (eB : ∀ n : ℕ,
        coefPairingSupport l E D X S ⋙ coefTraceEvaluation l E n ≅
          coefPairingFiniteC l E D X n)
      (eQcompact : ∀ n : ℕ,
        (coefTraceEvaluation l E n).obj (coefTraceDualizingTower l E D X Q) ≅
          (coefPairingFiniteSupport l E (finiteDualizingCompactification D X) n).obj
            (integralDualizingFiniteTerm l E D X n)),
      (∀ (K : DerivedCategory (scalarReductionSource.{u, u} l E X))
        (P : CochainComplex (scalarReductionSource.{u, u} l E X) ℤ)
        (_eP : DerivedCategory.Q.obj P ≅ K)
        (I : CochainComplex (ℕᵒᵖ ⥤ scalarReductionSource.{u, u} l E X) ℤ)
        (_hI : I.IsKInjective)
        (_eI : DerivedCategory.Q.obj I ≅
          (coefficientSequenceDerivedRestriction.{u, u} l E X).obj (coefTraceInput l E X Q)),
        Nonempty ((coefPairingHom l E X S Q).obj (op K) ≅
          DerivedCategory.Q.obj (coefPairingHomComplex l E X P I))) ∧
      (∀ n : ℕ, ∃ scalarIso :
        coefPairingIntegralHom l E X n (integralDualizingFiniteTerm l E D X n) ≅
          coefPairingFiniteHom l E X n (integralDualizingFiniteTerm l E D X n),
        (eIntegralHom n).hom ≫ scalarIso.hom = (eH n).hom) ∧
      (∀ (K : DerivedCategory (scalarReductionSource.{u, u} l E X))
        {m n : ℕ} (h : n ≤ m),
        (coefTraceTransition l E h).app ((coefPairingSupport l E D X S).obj K) ≫
          (eB n).hom.app K =
        (eB m).hom.app K ≫
          (coefPairingIntegralSections l E (Spec (.of D.k))).map
            (compactSupportRestrictedTransition l E (finiteDualizingCompactification D X)
              m n h K)) ∧
      (∀ (K : DerivedCategory (scalarReductionSource.{u, u} l E X)),
        finiteTorConstructibleIntegral l E X K → ∀ n : ℕ,
        (coefTraceEvaluation l E n).map
            (G.beta l E (S.reduction.obj K) (coefTraceInput l E X Q)) ≫
          (eQcompact n).hom =
        (evaluationTensor n).hom.app
            ((coefPairingHom l E X S Q).obj (op K), (coefPairingSupport l E D X S).obj K) ≫
          ((eH n).hom.app (op K) ⊗ₘ (eB n).hom.app K) ≫
            coefPairingFiniteBeta l E (finiteDualizingCompactification D X) S G n (F n)
              ((scalarReductionDerivedExtension l E X n).obj K)
              (integralDualizingFiniteTerm l E D X n)) ∧
      (∀ (K K' : DerivedCategory (scalarReductionSource.{u, u} l E X)),
        finiteTorConstructibleIntegral l E X K → finiteTorConstructibleIntegral l E X K' →
          ∀ f : K ⟶ K',
          (coefPairingTensor l E).map
              (Prod.mkHom ((coefPairingHom l E X S Q).map f.op) (𝟙 _)) ≫
            G.beta l E (S.reduction.obj K) (coefTraceInput l E X Q) =
          (coefPairingTensor l E).map
              (Prod.mkHom (𝟙 _) ((coefPairingSupport l E D X S).map f)) ≫
            G.beta l E (S.reduction.obj K') (coefTraceInput l E X Q)) := by
  sorry

end WeilConjectures
