/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NA
-/
module

public import Sheaf.CategoryTheory.SiteCoveringAxioms
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel
public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import Sheaf.CategoryTheory.SystemOrdinarySingleExtension
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.HomologicalComplex
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Sheaf.CategoryTheory.SystemRingedSequenceSite
public import Sheaf.CategoryTheory.SystemEvaluationTopos
public import Sheaf.CategoryTheory.SystemLevelLeftExtension
public import Sheaf.CategoryTheory.SystemSingleDerivedExtension
public import Sheaf.CategoryTheory.SystemSingleDerivedEvaluation
public import Sheaf.CategoryTheory.RingedToposMorphism
public import Sheaf.CategoryTheory.AlgebraicInverseImage
public import Sheaf.CategoryTheory.Sites.GeometricMorphism
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import Mathlib.Algebra.Homology.BifunctorShift
import all Sheaf.Paper.KFlatRingedToposPullback
import Sheaf.CategoryTheory.SystemSingletonScalarExtension
import Sheaf.CategoryTheory.SystemScalarCoherence

import Sheaf.CategoryTheory.SystemGeometricDerivedLift

/-! # Geometric inverse image and derived singleton extension

Source: Zheng, Six Operations and Lefschetz--Verdier, Construction 4.1, printed p. 21,
and the base-change sentence before Lemma 4.10, printed p. 23
(blueprint: lem-pur-system-singleton-geometric-pullback).

The comparison includes its common flat-term K-flat model, transported tensor generators,
actual strict transitions, multiplication normalization and lower-singleton square.
The index `n : ℕ` represents positive level `n + 1`.
-/

set_option Elab.async false

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe uC vC uD vD w
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite
namespace SheafOfModules
open MonoidalCategory
open scoped TensorProduct ChangeOfRings

variable {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  [EssentiallySmall.{w} C] [EssentiallySmall.{w} D]
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [K.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify J AddCommGrpCat.{w}]
  [K.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify K AddCommGrpCat.{w}]
  (BY : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w}) (BX : ℕᵒᵖ ⥤ Sheaf K CommRingCat.{w})
  (u : GeometricMorphism (Sheaf K (Type w)) (Sheaf J (Type w)))
  (I : ∀ n : ℕ, AlgebraicInverseImage u.inverse (BY.obj (op n)) (BX.obj (op n)))

/-- The ordinary underlying-set functor at a coefficient level, used only to express
transport of the actual semilinear transition. Source: Zheng, Construction 4.1, p. 21;
Stacks 03D2 (blueprint: lem-pur-system-singleton-geometric-pullback). -/
abbrev systemGeometricUnderlying (n : ℕ) :=
  toSheaf (derivedChangeRingIndependentCoefficients J (BY.obj (op n))) ⋙
    sheafCompose J (CategoryTheory.forget AddCommGrpCat.{w})

set_option genInjectivity false in
set_option genSizeOfSpec false in
/-- An exact termwise inverse image with its specified underlying transition maps.
The transition equation fixes the functor on systems, rather than merely specifying
unrelated level objects. All exactness fields are conclusions of the existence theorem.
Source: Zheng, Construction 4.1 and the sentence before Lemma 4.10; Stacks 03D2
(blueprint: lem-pur-system-singleton-geometric-pullback). -/
structure SystemGeometricInverseImageData where
  functor : StrictRingSystem BY ⥤ StrictRingSystem BX
  [additive : functor.Additive]
  [limits : PreservesFiniteLimits functor]
  [colimits : PreservesFiniteColimits functor]
  [levelAdditive : ∀ n : ℕ, (I n).modules.Additive]
  [levelLimits : ∀ n : ℕ, PreservesFiniteLimits (I n).modules]
  [levelColimits : ∀ n : ℕ, PreservesFiniteColimits (I n).modules]
  evaluation : ∀ n : ℕ,
    functor ⋙ systemEvaluation BX n ≅ systemEvaluation BY n ⋙ (I n).modules
  transition : ∀ (M : StrictRingSystem BY) {m n : ℕ} (h : m ≤ n),
    (systemGeometricUnderlying BX n).map ((evaluation n).hom.app M) ≫
        (I n).moduleUnderlying.hom.app (M.level n) ≫
        u.inverse.map ((systemGeometricUnderlying BY n).map (M.transition h)) ≫
        (I m).moduleUnderlying.inv.app (M.level m) =
      (systemGeometricUnderlying BX n).map ((functor.obj M).transition h) ≫
        (systemGeometricUnderlying BX m).map ((evaluation m).hom.app M)

attribute [instance] SystemGeometricInverseImageData.additive
  SystemGeometricInverseImageData.limits SystemGeometricInverseImageData.colimits

variable {BY BX u I}

/-- The specified level inverse image, retaining the exactness witness in its interface.
Source: Stacks 03D2 (blueprint: lem-pur-system-singleton-geometric-pullback). -/
def SystemGeometricInverseImageData.levelFunctor
    (_F : SystemGeometricInverseImageData BY BX u I) (n : ℕ) := (I n).modules

/-- Additivity of the level inverse image. Source: Stacks 03D2
(blueprint: lem-pur-system-singleton-geometric-pullback). -/
instance SystemGeometricInverseImageData.levelFunctorAdditive
    (F : SystemGeometricInverseImageData BY BX u I) (n : ℕ) :
    (F.levelFunctor n).Additive := F.levelAdditive n

/-- Left exactness of the level inverse image. Source: Stacks 03DA
(blueprint: lem-pur-system-singleton-geometric-pullback). -/
instance SystemGeometricInverseImageData.levelFunctorLimits
    (F : SystemGeometricInverseImageData BY BX u I) (n : ℕ) :
    PreservesFiniteLimits (F.levelFunctor n) := F.levelLimits n

/-- Right exactness of the level inverse image. Source: Stacks 03DB
(blueprint: lem-pur-system-singleton-geometric-pullback). -/
instance SystemGeometricInverseImageData.levelFunctorColimits
    (F : SystemGeometricInverseImageData BY BX u I) (n : ℕ) :
    PreservesFiniteColimits (F.levelFunctor n) := F.levelColimits n

/-- The canonical localization of the termwise evaluation square.
Source: Zheng, Construction 4.1; Stacks 015F
(blueprint: lem-pur-system-singleton-geometric-pullback). -/
def SystemGeometricInverseImageData.derivedEvaluation
    (F : SystemGeometricInverseImageData BY BX u I) (n : ℕ) :
    F.functor.mapDerivedCategory ⋙ derivedSystemEvaluation BX n ≅
      derivedSystemEvaluation BY n ⋙ (F.levelFunctor n).mapDerivedCategory :=
  (Functor.mapDerivedCategoryCompIso F.functor (systemEvaluation BX n)).symm ≪≫
    Functor.mapDerivedCategoryNatIso
      (G := systemEvaluation BY n ⋙ F.levelFunctor n)
      (F.evaluation n : F.functor ⋙ systemEvaluation BX n ≅
        systemEvaluation BY n ⋙ F.levelFunctor n) ≪≫
    Functor.mapDerivedCategoryCompIso (systemEvaluation BY n) (F.levelFunctor n)

variable (SY : SystemScalarAssignment (J := J)) (TY : SystemTensorCoherence SY)
  (SX : SystemScalarAssignment (J := K)) (TX : SystemTensorCoherence SX)

/-- Multiplication at the selected level of ordinary singleton extension.
Source: Zheng, Construction 4.1, p. 21
(blueprint: lem-pur-system-singleton-geometric-pullback). -/
def systemSingletonOrdinaryMultiplication (n : ℕ) :
    systemSingleFunctor SY TY BY n ⋙ systemEvaluation BY n ≅ 𝟭 (systemLevel BY n) :=
  systemSingleBelow SY TY BY n (Nat.le_refl n) ≪≫ TY.ordinaryUnit BY n

/-- Multiplication at the selected level of derived singleton extension.
Source: Zheng, Construction 4.1, p. 21
(blueprint: lem-pur-system-singleton-geometric-pullback). -/
def systemSingletonDerivedMultiplication (n : ℕ) :
    (systemSingleDerivedExtension BY n SY TY).derived ⋙ derivedSystemEvaluation BY n ≅
      𝟭 (DerivedCategory (systemLevel BY n)) :=
  systemSingleDerivedBelow BY (Nat.le_refl n) SY TY ≪≫ TY.derivedUnit BY n

/-- The canonical lower-singleton arrow is the transpose of the inverse below-level
comparison. Its components are the tensor associators below `n`, and zero above `n`.
Source: Zheng, Construction 4.1, p. 21
(blueprint: lem-pur-system-singleton-geometric-pullback). -/
def systemSingletonLowerMap {n m : ℕ} (h : n ≤ m)
    (P : DerivedCategory (systemLevel BY m)) :
    (systemSingleDerivedExtension BY n SY TY).derived.obj
        ((systemDerivedTensor SY BY h).obj P) ⟶
      (systemSingleDerivedExtension BY m SY TY).derived.obj P :=
  ((systemSingleDerivedExtension BY n SY TY).adjunction.homEquiv _ _).symm
    ((systemSingleDerivedBelow BY h SY TY).inv.app P)

set_option linter.unusedVariables false in
/-- The geometric singleton comparison, together with all its specified normalizations.
This is the full conclusion of the node, including the ordinary representatives and the
canonical scalar comparison used in the lower-singleton square. It is not an unnormalized
existence assertion about an arbitrary isomorphism.
Source: Zheng, Construction 4.1 and the sentence before Lemma 4.10, pp. 21 and 23;
Stacks 03EL and 0G7E (blueprint: lem-pur-system-singleton-geometric-pullback). -/
def SystemSingletonGeometricComparisons
    (F : SystemGeometricInverseImageData BY BX u I) : Prop :=
  ∃ (ordinary : ∀ n : ℕ,
    systemSingleFunctor SY TY BY n ⋙ F.functor ≅
      F.levelFunctor n ⋙ systemSingleFunctor SX TX BX n)
    (tensor : ∀ {j n : ℕ} (h : j ≤ n),
    systemTensor SY BY h ⋙ F.levelFunctor j ≅ F.levelFunctor n ⋙ systemTensor SX BX h)
    (comparison : ∀ n : ℕ,
    (systemSingleDerivedExtension BY n SY TY).derived ⋙ F.functor.mapDerivedCategory ≅
      (F.levelFunctor n).mapDerivedCategory ⋙ (systemSingleDerivedExtension BX n SX TX).derived)
    (scalar : ∀ {n m : ℕ} (h : n ≤ m),
    systemDerivedTensor SY BY h ⋙ (F.levelFunctor n).mapDerivedCategory ≅
      (F.levelFunctor m).mapDerivedCategory ⋙ systemDerivedTensor SX BX h),
    -- tensor_evaluation
    (∀ {j n : ℕ} (h : j ≤ n) (P : systemLevel BY n),
    (F.evaluation j).hom.app ((systemSingleFunctor SY TY BY n).obj P) ≫
        (F.levelFunctor j).map ((systemSingleBelow SY TY BY n h).hom.app P) ≫
        (tensor h).hom.app P =
      ((ordinary n).hom.app P).app j ≫
        (systemSingleBelow SX TX BX n h).hom.app ((F.levelFunctor n).obj P)) ∧
    -- tensor_generators
    (∀ {j n : ℕ} (h : j ≤ n) (P : systemLevel BY n)
    (Z : Sheaf J (Type w))
    (b : Z ⟶ (sheafCompose J (CategoryTheory.forget CommRingCat.{w})).obj (BY.obj (op j)))
    (x : Z ⟶ (systemGeometricUnderlying BY n).obj P)
    (z : Z ⟶ (systemGeometricUnderlying BY j).obj ((systemTensor SY BY h).obj P)),
    (∀ U t, z.hom.app U t =
      systemModelTmul (SY (BY.map (homOfLE h).op)).model P U
        (b.hom.app U t) (x.hom.app U t)) →
    ∀ (W : Dᵒᵖ) (t : (u.inverse.obj Z).obj.obj W),
      ((tensor h).hom.app P).val.app W
          (((u.inverse.map z) ≫
            (I j).moduleUnderlying.inv.app ((systemTensor SY BY h).obj P)).hom.app W t) =
        systemModelTmul (SX (BX.map (homOfLE h).op)).model
          ((F.levelFunctor n).obj P) W
          (((u.inverse.map b) ≫ (I j).ringUnderlying.hom).hom.app W t)
          (((u.inverse.map x) ≫ (I n).moduleUnderlying.inv.app P).hom.app W t)) ∧
    -- above
    (∀ (n j : ℕ) (h : n < j) (P : systemLevel BY n),
    ((ordinary n).hom.app P).app j = 0) ∧
    -- multiplication
    (∀ (n : ℕ) (P : systemLevel BY n),
    ((ordinary n).hom.app P).app n ≫
        (systemSingletonOrdinaryMultiplication (BY := BX) SX TX n).hom.app
          ((F.levelFunctor n).obj P) =
      (F.evaluation n).hom.app ((systemSingleFunctor SY TY BY n).obj P) ≫
        (F.levelFunctor n).map
          ((systemSingletonOrdinaryMultiplication (BY := BY) SY TY n).hom.app P)) ∧
    -- flat_models
    (∀ (n : ℕ) (Q : CochainComplex (systemLevel BY n) ℤ),
    systemLevelKFlat BY n Q →
    systemLevelKFlat BX n (((F.levelFunctor n).mapHomologicalComplex (.up ℤ)).obj Q) ∧
    (CochainComplex.IsKFlatIndependentCoefficients (R := systemSequenceRing BY)
      (((strictSystemToSequenceFunctor BY).mapHomologicalComplex (.up ℤ)).obj
        (((systemSingleFunctor SY TY BY n).mapHomologicalComplex (.up ℤ)).obj Q)) ∧
      ∀ r : ℤ, IsFlatOnSite (R := systemSequenceRing BY)
        ((((strictSystemToSequenceFunctor BY).mapHomologicalComplex (.up ℤ)).obj
          (((systemSingleFunctor SY TY BY n).mapHomologicalComplex (.up ℤ)).obj Q)).X r)) ∧
    (CochainComplex.IsKFlatIndependentCoefficients (R := systemSequenceRing BX)
      (((strictSystemToSequenceFunctor BX).mapHomologicalComplex (.up ℤ)).obj
        (((systemSingleFunctor SX TX BX n).mapHomologicalComplex (.up ℤ)).obj
          (((F.levelFunctor n).mapHomologicalComplex (.up ℤ)).obj Q))) ∧
      ∀ r : ℤ, IsFlatOnSite (R := systemSequenceRing BX)
        ((((strictSystemToSequenceFunctor BX).mapHomologicalComplex (.up ℤ)).obj
          (((systemSingleFunctor SX TX BX n).mapHomologicalComplex (.up ℤ)).obj
            (((F.levelFunctor n).mapHomologicalComplex (.up ℤ)).obj Q))).X r))) ∧
    -- representative
    (∀ (n : ℕ) (Q : CochainComplex (systemLevel BY n) ℤ),
    systemLevelKFlat BY n Q →
    (comparison n).hom.app (DerivedCategory.Q.obj Q) ≫
        (systemSingleDerivedExtension BX n SX TX).derived.map
          ((F.levelFunctor n).mapDerivedCategoryFactors.hom.app Q) ≫
        (systemSingleDerivedExtension BX n SX TX).comparison.app
          (((F.levelFunctor n).mapHomologicalComplex (.up ℤ)).obj Q) =
      F.functor.mapDerivedCategory.map
          ((systemSingleDerivedExtension BY n SY TY).comparison.app Q) ≫
        F.functor.mapDerivedCategoryFactors.hom.app
          (((systemSingleFunctor SY TY BY n).mapHomologicalComplex (.up ℤ)).obj Q) ≫
        DerivedCategory.Q.map ((NatIso.mapHomologicalComplex (ordinary n) (.up ℤ)).hom.app Q)) ∧
    -- derived_multiplication
    (∀ (n : ℕ) (P : DerivedCategory (systemLevel BY n)),
    (derivedSystemEvaluation BX n).map ((comparison n).hom.app P) ≫
        (systemSingletonDerivedMultiplication (BY := BX) SX TX n).hom.app
          ((F.levelFunctor n).mapDerivedCategory.obj P) =
      (F.derivedEvaluation n).hom.app ((systemSingleDerivedExtension BY n SY TY).derived.obj P) ≫
        (F.levelFunctor n).mapDerivedCategory.map
          ((systemSingletonDerivedMultiplication (BY := BY) SY TY n).hom.app P)) ∧
    -- scalar_representative
    (∀ {n m : ℕ} (h : n ≤ m)
    (Q : CochainComplex (systemLevel BY m) ℤ), systemLevelKFlat BY m Q →
    (scalar h).hom.app (DerivedCategory.Q.obj Q) ≫
        (systemDerivedTensor SX BX h).map
          ((F.levelFunctor m).mapDerivedCategoryFactors.hom.app Q) ≫
        (SX (BX.map (homOfLE h).op)).model.ε.app
          (((F.levelFunctor m).mapHomologicalComplex (.up ℤ)).obj Q) =
      (F.levelFunctor n).mapDerivedCategory.map
          ((SY (BY.map (homOfLE h).op)).model.ε.app Q) ≫
        (F.levelFunctor n).mapDerivedCategoryFactors.hom.app
          (((systemTensor SY BY h).mapHomologicalComplex (.up ℤ)).obj Q) ≫
        DerivedCategory.Q.map ((NatIso.mapHomologicalComplex (tensor h) (.up ℤ)).hom.app Q)) ∧
    -- lower_singleton
    (∀ {n m : ℕ} (h : n ≤ m)
    (P : DerivedCategory (systemLevel BY m)),
    F.functor.mapDerivedCategory.map (systemSingletonLowerMap SY TY h P) ≫
        (comparison m).hom.app P =
      (comparison n).hom.app ((systemDerivedTensor SY BY h).obj P) ≫
        (systemSingleDerivedExtension BX n SX TX).derived.map ((scalar h).hom.app P) ≫
        systemSingletonLowerMap SX TX h ((F.levelFunctor m).mapDerivedCategory.obj P))


set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

include SX in
private theorem geometricLevelKFlat (n : ℕ)
    [H : ∀ n : ℕ, (I n).modules.Additive]
    (Q : CochainComplex (systemLevel BY n) ℤ) (hQ : systemLevelKFlat BY n Q) :
    systemLevelKFlat BX n (((I n).modules.mapHomologicalComplex (.up ℤ)).obj Q) := by
  let A := SX (𝟙 (BX.obj (op n)))
  let F := (I n).modules
  have : F.Additive := H n
  have : PreservesFiniteLimits u.inverse := u.leftExact
  have ht := isKFlat_ringedToposPullback u.inverse u.direct u.adj (I n)
    (𝟙 (BX.obj (op n))) (F ⋙ A.model.E)
    (fun P ↦ A.model.obj_eq (F.obj P))
    (fun f ↦ A.model.map_eq (F.map f)) Q hQ.1 hQ.2
  let e : F ⋙ A.model.E ≅ F :=
    isoWhiskerLeft F (systemScalarModelUnit rfl A) ≪≫ F.rightUnitor
  let ec := (NatIso.mapHomologicalComplex e (.up ℤ)).app Q
  exact ⟨kFlat_iso_independent (BX.obj (op n)) ec ht.1,
    fun i ↦ flatOnSite_of_iso (BX.obj (op n))
      ((HomologicalComplex.eval _ (.up ℤ) i).mapIso ec) (ht.2 i)⟩

private theorem singletonFlatModelsFromScalar
    (S : SystemScalarAssignment (J := J)) (T : SystemTensorCoherence S)
    (B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w}) (n : ℕ)
    (Q : CochainComplex (systemLevel B n) ℤ) (hQ : systemLevelKFlat B n Q)
    (A : SystemScalarModel (singletonSequenceRingMap (𝟙 B))) :
    CochainComplex.IsKFlatIndependentCoefficients (R := systemSequenceRing B)
      (((strictSystemToSequenceFunctor B).mapHomologicalComplex (.up ℤ)).obj
        (((systemSingleFunctor S T B n).mapHomologicalComplex (.up ℤ)).obj Q)) ∧
    ∀ r : ℤ, IsFlatOnSite (R := systemSequenceRing B)
      ((((strictSystemToSequenceFunctor B).mapHomologicalComplex (.up ℤ)).obj
        (((systemSingleFunctor S T B n).mapHomologicalComplex (.up ℤ)).obj Q)).X r) := by
  have h := (singletonScalarExtension (B := B) (D := B) S T (𝟙 B) A).2.1 n Q hQ
  exact ⟨h.1, h.2.1⟩


private theorem singletonFlatModels
    (S : SystemScalarAssignment (J := J)) (T : SystemTensorCoherence S)
    (B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w}) (n : ℕ)
    (Q : CochainComplex (systemLevel B n) ℤ) (hQ : systemLevelKFlat B n Q) :
    CochainComplex.IsKFlatIndependentCoefficients (R := systemSequenceRing B)
      (((strictSystemToSequenceFunctor B).mapHomologicalComplex (.up ℤ)).obj
        (((systemSingleFunctor S T B n).mapHomologicalComplex (.up ℤ)).obj Q)) ∧
    ∀ r : ℤ, IsFlatOnSite (R := systemSequenceRing B)
      ((((strictSystemToSequenceFunctor B).mapHomologicalComplex (.up ℤ)).obj
        (((systemSingleFunctor S T B n).mapHomologicalComplex (.up ℤ)).obj Q)).X r) :=
  singletonFlatModelsFromScalar S T B n Q hQ
    (Classical.choice (nonempty_systemScalarModel (singletonSequenceRingMap (𝟙 B))))


set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Geometric inverse image commutes with singleton left extension on the ordinary
unbounded derived categories, with the common model and all normalization clauses.
The ring equation says exactly that the target transitions are the pulled-back source
transitions. The source and target sites are small relative to the module universe;
coefficient transitions may be nonflat and the complexes may be unbounded.

Source: Zheng, Construction 4.1, printed p. 21, and the base-change sentence before
Lemma 4.10, printed p. 23 (blueprint: lem-pur-system-singleton-geometric-pullback).

Proof:
1. On the ringed sequence site covers are vertical. Tensor, exactness and coproducts
therefore evaluate componentwise. A system complex with K-flat levels is K-flat:
tensor with an acyclic system, evaluate the total tensor, and use exact evaluations
to detect acyclicity. The analogous argument gives flatness of each term.
2. The ordinary singleton has scalar-extension levels below n and zero above.
Apply ringed-topos K-flat preservation (Stacks 0G7E) to the identity geometric
morphism with coefficient map B_n to B_j. Apply it again to the geometric inverse
image with identity structural map. This gives the two flat-term K-flat singleton
models on the same Q, without a flatness hypothesis on the coefficients.
3. The inverse-image tensor comparison of Stacks 03EL sends the transported
b tensor q to the tensor of the transported b and q. Its naturality gives a
cochain isomorphism. Above n use the unique isomorphism between zero objects.
4. Check the actual transitions on balanced generators: both composites send
b tensor q to the transported transition of b tensor the transported q. At the
boundary the source is zero. At level n multiplication gives the identity.
The inverse ordinary comparison satisfies the singleton-adjunction unit-mate equation.
5. Geometric inverse image is exact. Localize its termwise evaluation square and
apply lem-pur-extension-evaluation-comparison to the two normalized singleton derived
extensions. Flat-term K-flat resolutions exist and Step 2 preserves the resolving
class. The normalized mate representative is the ordinary comparison of Steps 3-4;
it gives the representative equation and the derived multiplication normalization.
6. For m at least n, scalar extension of a good B_m-complex is again good by 0G7E.
The canonical lower-singleton map is adjoint to the inverse below-level comparison;
its components below n are the scalar tensor associators, and above n are zero.
Both paths send b tensor (a tensor q) to the transported product of b with the
transition of a, tensor the transported q. Thus the square commutes as a whole
system cochain square. Scalar-coherence identifies its localized associators and
the universal comparison formulas descend this equality to every derived input.
No assertion that derived evaluation detects equality of morphisms is used. -/
theorem systemSingletonGeometricPullback
    (BY : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w}) (BX : ℕᵒᵖ ⥤ Sheaf K CommRingCat.{w})
    (u : GeometricMorphism (Sheaf K (Type w)) (Sheaf J (Type w)))
    (I : ∀ n : ℕ, AlgebraicInverseImage u.inverse (BY.obj (op n)) (BX.obj (op n)))
    (htransition : ∀ {m n : ℕ} (h : m ≤ n),
      u.inverse.map ((sheafCompose J (CategoryTheory.forget CommRingCat.{w})).map
          (BY.map (homOfLE h).op)) ≫ (I m).ringUnderlying.hom =
        (I n).ringUnderlying.hom ≫
          (sheafCompose K (CategoryTheory.forget CommRingCat.{w})).map
            (BX.map (homOfLE h).op))
    (SY : SystemScalarAssignment (J := J)) (TY : SystemTensorCoherence SY)
    (SX : SystemScalarAssignment (J := K)) (TX : SystemTensorCoherence SX) :
    ∃ F : SystemGeometricInverseImageData BY BX u I,
      SystemSingletonGeometricComparisons SY TY SX TX F := by
  obtain ⟨G, ordinary, tensor, heval, hgen, habove, hmul⟩ :=
    geometricSystemOrdinaryComparison BY BX u I htransition SY TY SX TX
  obtain ⟨comparison, scalar, hrep, hdmul, hsrep, hlower⟩ :=
    geometricSystemDerivedLift SY TY SX TX G ordinary tensor heval hgen habove hmul
  let F : SystemGeometricInverseImageData BY BX u I :=
    { functor := G.functor
      additive := G.additive
      limits := G.limits
      colimits := G.colimits
      levelAdditive := G.levelAdditive
      levelLimits := G.levelLimits
      levelColimits := G.levelColimits
      evaluation := G.evaluation
      transition := G.transition }
  refine ⟨F, ordinary, tensor, comparison, scalar, heval, hgen, habove, hmul,
    ?_, hrep, hdmul, hsrep, hlower⟩
  intro n Q hQ
  let := G.levelAdditive
  have hX := geometricLevelKFlat (I := I) SX n Q hQ
  exact ⟨hX, singletonFlatModels SY TY BY n Q hQ,
    singletonFlatModels SX TX BX n _ hX⟩

end SheafOfModules
