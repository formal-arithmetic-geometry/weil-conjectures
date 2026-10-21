/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N8
-/
module

public import Sheaf.Paper.InternalScalarTensorComparison
public import Sheaf.Algebra.Homology.FlatInternalHomEvaluationRoof
public import Sheaf.CategoryTheory.InternalSectionScalarAdjunction
public import Sheaf.Paper.ModuleObjectRingedSiteDerivedComparison
public import Sheaf.Paper.DerivedInternalHomFilteredColimit
public import Sheaf.AlgebraicGeometry.CondensedCoefficientComplexDiagram
public import Sheaf.Topology.ProfiniteCondensedRing
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.CategoryTheory.Limits.Final
import Sheaf.Paper.FiniteSubextensionsDirected
import Sheaf.Paper.CartesianCoefficients
public import Sheaf.Paper.CompletedCondensedCoefficients
public import Sheaf.Paper.QlbarTailModuleColimit
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Sheaf.CategoryTheory.InternalSectionTensorComparison

/-! # Algebraic-closure coefficient comparison for internal Hom

Source: Bhatt--Scholze, Lemma 6.8.2, Proposition 6.8.14 and Remark 6.8.15;
the explicit-continuity specialization in the DAG
(blueprint: lem-sfb-qlbar-internal-hom-coefficient-comparison).

## Main definitions and statements

* `evaluationComparison`: the actual scalar-extended evaluation transpose.
* `Continuous`: the explicit continuity hypothesis on strict filtered diagrams.
* `fields`, `coefficients`, `coefficientCocone`: the prescribed finite-field tail.
* `StrictColimitFormula`, `ColimitFormula`: the termwise colimit roof and its squares.
* `evaluationComparison_naturality`, `evaluationComparison_restriction`:
  naturality and scalar-adjunction normalization.
* `fieldDiagram`, `coefficientModules`, `coefficientRingColimit`:
  smallness, cofinality, finite freeness and the specified coefficient colimits.
* `coefficient_colimit_formula`: the three evaluation-normalized colimit arrows.
* `qlbar_internalHom_coefficient_comparison`: invertibility on the stated inputs.
-/

@[expose] public noncomputable section
set_option autoImplicit false
attribute [local irreducible] WeilConjectures.SfbHomFilteredColimit.comparison
  WeilConjectures.SfbHomFilteredColimit.homFixed
  WeilConjectures.SfbHomFilteredColimit.tensorFixed
  WeilConjectures.SfbHomFilteredColimit.roofDenominator
  WeilConjectures.coefficientHomResolution
  CategoryTheory.Functor.leftDerivedFunctor CategoryTheory.Functor.mapDerivedCategory
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.QlbarInternalHom

open ModuleObjectRingedComparison

variable (X : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime]

/-- The actual evaluation transpose for any flat condensed coefficient inclusion.
Source: DAG displayed comparison; Bhatt--Scholze 6.8.14--6.8.15
(blueprint: lem-sfb-qlbar-internal-hom-coefficient-comparison). -/
def evaluationComparison
    {R S : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj R] [IsCommMonObj R] [MonObj S] [IsCommMonObj S]
    (a : R ⟶ S) [IsMonHom a]
    [∀ Z : Scheme.{u}, PreservesFiniteLimits (Mod.extendScalars (coefficientMap a Z))]
    (K L : DerivedCategory (Internal R X)) :
    (CondensedRing.internalScalarExtension a X).obj
        (((CondensedRing.derivedHom R X).obj (op K)).obj L) ⟶
      ((CondensedRing.derivedHom S X).obj
        (op ((CondensedRing.internalScalarExtension a X).obj K))).obj
          ((CondensedRing.internalScalarExtension a X).obj L) :=
  (CondensedRing.derivedTensorHomAdjunction S
    ((CondensedRing.internalScalarExtension a X).obj K)).homEquiv _ _
      (((CondensedRing.internalScalarTensorIso a X).inv.app K).app
          (((CondensedRing.derivedHom R X).obj (op K)).obj L) ≫
        (CondensedRing.internalScalarExtension a X).map
          ((CondensedRing.derivedTensorHomAdjunction R K).counit.app L))

/-- Naturality for every flat condensed coefficient map and all derived morphisms.
Source: DAG naturality clause, Stacks 08J9
(blueprint: lem-sfb-qlbar-internal-hom-coefficient-comparison).
Proof: naturality of the scalar tensorator and both evaluation counits identifies
both evaluation transposes. Injectivity of the tensor-Hom adjunction gives equality. -/
theorem evaluationComparison_naturality
    {R S : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj R] [IsCommMonObj R] [MonObj S] [IsCommMonObj S]
    (a : R ⟶ S) [IsMonHom a]
    [∀ Z : Scheme.{u}, PreservesFiniteLimits (Mod.extendScalars (coefficientMap a Z))]
    (K K' L L' : DerivedCategory (Internal R X)) (f : K' ⟶ K) (g : L ⟶ L') :
    (CondensedRing.internalScalarExtension a X).map
        (((CondensedRing.derivedHom R X).map f.op).app L ≫
          ((CondensedRing.derivedHom R X).obj (op K')).map g) ≫
        evaluationComparison X a K' L' =
      evaluationComparison X a K L ≫
        ((CondensedRing.derivedHom S X).map
          ((CondensedRing.internalScalarExtension a X).map f).op).app
            ((CondensedRing.internalScalarExtension a X).obj L) ≫
        ((CondensedRing.derivedHom S X).obj
          (op ((CondensedRing.internalScalarExtension a X).obj K'))).map
            ((CondensedRing.internalScalarExtension a X).map g) := by
  sorry

/-- The scalar internal-Hom adjunction is the unique isomorphism of right adjoints.
Its left-adjoint isomorphism is the unit-normalized tensor comparison above.
Source: DAG restriction formula, Stacks 08J9 and 07A4
(blueprint: lem-sfb-qlbar-internal-hom-coefficient-comparison). -/
def scalarHomIso
    {R S : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj R] [IsCommMonObj R] [MonObj S] [IsCommMonObj S]
    (a : R ⟶ S) [IsMonHom a]
    [∀ Z : Scheme.{u}, PreservesFiniteLimits (Mod.extendScalars (coefficientMap a Z))]
    (K : DerivedCategory (Internal R X)) :
    ((CondensedRing.derivedHom S X).obj
        (op ((CondensedRing.internalScalarExtension a X).obj K))) ⋙
        (Mod.comap (coefficientMap a X)).mapDerivedCategory ≅
      (Mod.comap (coefficientMap a X)).mapDerivedCategory ⋙
        (CondensedRing.derivedHom R X).obj (op K) :=
  ((Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap a X)).comp
      (CondensedRing.derivedTensorHomAdjunction S
        ((CondensedRing.internalScalarExtension a X).obj K))).rightAdjointUniq
    (((CondensedRing.derivedTensorHomAdjunction R K).comp
        (Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap a X))).ofNatIsoLeft
      ((CondensedRing.internalScalarTensorIso a X).app K))

/-- The restricted comparison is characterized by the scalar unit and evaluation.
Source: DAG restriction formula, Stacks 08J9 and 07A4
(blueprint: lem-sfb-qlbar-internal-hom-coefficient-comparison).
Proof: transpose through the scalar adjunction and both tensor-Hom adjunctions.
The defining mate of scalarHomIso cancels the strong tensorator. Both transposes
are evaluation followed by the scalar unit of L, giving the equality. -/
theorem evaluationComparison_restriction
    {R S : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj R] [IsCommMonObj R] [MonObj S] [IsCommMonObj S]
    (a : R ⟶ S) [IsMonHom a]
    [∀ Z : Scheme.{u}, PreservesFiniteLimits (Mod.extendScalars (coefficientMap a Z))]
    (K L : DerivedCategory (Internal R X)) :
    (Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap a X)).unit.app
        (((CondensedRing.derivedHom R X).obj (op K)).obj L) ≫
      (Mod.comap (coefficientMap a X)).mapDerivedCategory.map
        (evaluationComparison X a K L) ≫
      (scalarHomIso X a K).hom.app ((CondensedRing.internalScalarExtension a X).obj L) =
    ((CondensedRing.derivedHom R X).obj (op K)).map
      ((Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap a X)).unit.app L) := by
  sorry

/-- Continuity on every coefficient-small filtered index and every representative of K.
The existing exact section equivalence and evaluation-normalized Hom comparison identify
this with internal-sheaf continuity in the node, with functorial K-injective models.
Source: DAG continuity hypothesis, proof step 5; Stacks 08J9
(blueprint: lem-sfb-qlbar-internal-hom-coefficient-comparison). -/
def Continuous (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (K : DerivedCategory (Internal (Profinite.continuousMapRingObj E) X)) : Prop :=
  ∀ (P : CochainComplex (Modules (Profinite.continuousMapRingObj E) X) ℤ),
    Nonempty (DerivedCategory.Q.obj P ≅
      (forward (Profinite.continuousMapRingObj E) X).obj K) →
    ∀ (I : Type (u + 1)) [SmallCategory I] [IsFiltered I],
      WeilConjectures.SfbHomFilteredColimit.Continuous.{u + 1, u, u}
        (Scheme.ProEt.topology X) (ring (Profinite.continuousMapRingObj E) X) (I := I) P

/-- The small tail index, including E itself. Its projection is the actual inclusion.
Source: DAG proof step 1, Bhatt--Scholze 6.8.2(2)
(blueprint: lem-sfb-qlbar-internal-hom-coefficient-comparison). -/
def fields (E : PadicAlgCl.FiniteIntermediateField ℓ) :
    AsSmall.{u + 1} (Under E) ⥤ PadicAlgCl.FiniteIntermediateField ℓ :=
  (AsSmall.equiv (C := Under E)).inverse ⋙ Under.forget E

/-- The finite-free coefficient diagram, using the actual scalar-inclusion chain maps.
The degree-zero extension of the regular E-module is canonically the regular F-module.
Source: DAG proof steps 2--3; Bhatt--Scholze 6.8.2(2)
(blueprint: lem-sfb-qlbar-internal-hom-coefficient-comparison). -/
def coefficients (E : PadicAlgCl.FiniteIntermediateField ℓ) :
    AsSmall.{u + 1} (Under E) ⥤ Modules (Profinite.continuousMapRingObj E) X :=
  coefficientComplexDiagram X ℓ
      ((HomologicalComplex.single (Internal (Profinite.continuousMapRingObj E) X)
          (ComplexShape.up ℤ) 0).obj
        (Mod.regular (padicSubfieldRingObj X ℓ E))) (fields ℓ E)
      (fun i ↦ leOfHom (((AsSmall.equiv (C := Under E)).inverse.obj i).hom))
      (fun i ↦ leOfHom (((AsSmall.equiv (C := Under E)).inverse.obj i).hom)) ⋙
    complexForward (Profinite.continuousMapRingObj E) X ⋙ HomologicalComplex.eval _ _ 0

/-- The cocone with the prescribed inclusions into the closure, in module sheaves.
Source: DAG proof step 3; Bhatt--Scholze 6.8.2(2)
(blueprint: lem-sfb-qlbar-internal-hom-coefficient-comparison). -/
def coefficientCocone (E : PadicAlgCl.FiniteIntermediateField ℓ) :
    Cocone (coefficients X ℓ E) :=
  (HomologicalComplex.eval _ _ 0).mapCocone
    ((complexForward (Profinite.continuousMapRingObj E) X).mapCocone
      (coefficientComplexCocone X ℓ
        ((HomologicalComplex.single (Internal (Profinite.continuousMapRingObj E) X)
          (ComplexShape.up ℤ) 0).obj
          (Mod.regular (padicSubfieldRingObj X ℓ E))) (fields ℓ E)
        (fun i ↦ leOfHom (((AsSmall.equiv (C := Under E)).inverse.obj i).hom))
        (fun i ↦ leOfHom (((AsSmall.equiv (C := Under E)).inverse.obj i).hom))))

/-- The strict three-arrow colimit formula, for an actual coefficient-module cocone.
Source: DAG displayed formula, proof step 6; Bhatt--Scholze 6.8.14--6.8.15
(blueprint: lem-sfb-qlbar-internal-hom-coefficient-comparison). -/
def StrictColimitFormula
    {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{u + 1}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u + 1}]
    (R : Sheaf J CommRingCat.{u + 1})
    {I : Type (u + 1)} [SmallCategory I]
    (T : I ⥤ WeilConjectures.SfbHomFilteredColimit.Modules.{u + 1, u, u} J R)
    [HasColimit T] (c : Cocone T)
    (P L : CochainComplex
      (WeilConjectures.SfbHomFilteredColimit.Modules.{u + 1, u, u} J R) ℤ) : Prop :=
  Nonempty (IsColimit c) ∧
  QuasiIso (colimMap (Functor.whiskerLeft T
    (WeilConjectures.SfbHomFilteredColimit.comparison.{u + 1, u, u} J R P L))) ∧
  WeilConjectures.SfbHomFilteredColimit.Normalized.{u + 1, u, u} J R P L
    (WeilConjectures.SfbHomFilteredColimit.comparison.{u + 1, u, u} J R P L) ∧
  QuasiIso (colimit.post
    (T ⋙ WeilConjectures.SfbHomFilteredColimit.tensorFixed.{u + 1, u, u} J R
      ((WeilConjectures.coefficientHomResolution.{u, u + 1, u} J R).obj L))
    (WeilConjectures.SfbHomFilteredColimit.homFixed.{u + 1, u, u} J R P)) ∧
  IsIso (colimit.post T
    (WeilConjectures.SfbHomFilteredColimit.tensorFixed.{u + 1, u, u} J R
      ((WeilConjectures.SfbHomFilteredColimit.homFixed.{u + 1, u, u} J R P).obj L))) ∧
  (∀ i, QuasiIso
    ((WeilConjectures.SfbHomFilteredColimit.comparison.{u + 1, u, u} J R P L).app
      (T.obj i))) ∧
  (∀ i, QuasiIso
    (WeilConjectures.SfbHomFilteredColimit.roofDenominator.{u + 1, u, u} J R P L
      (T.obj i))) ∧
  QuasiIso
    ((WeilConjectures.SfbHomFilteredColimit.comparison.{u + 1, u, u} J R P L).app c.pt) ∧
  QuasiIso
    (WeilConjectures.SfbHomFilteredColimit.roofDenominator.{u + 1, u, u} J R P L c.pt) ∧
  (colimit.post T
      (WeilConjectures.SfbHomFilteredColimit.tensorFixed.{u + 1, u, u} J R
        ((WeilConjectures.SfbHomFilteredColimit.homFixed.{u + 1, u, u} J R P).obj L)) ≫
        (WeilConjectures.SfbHomFilteredColimit.comparison.{u + 1, u, u} J R P L).app
          (colimit T) =
    colimMap (Functor.whiskerLeft T
      (WeilConjectures.SfbHomFilteredColimit.comparison.{u + 1, u, u} J R P L)) ≫
        colimit.post T
          (WeilConjectures.SfbHomFilteredColimit.tensorFixed.{u + 1, u, u} J R
            ((WeilConjectures.coefficientHomResolution.{u, u + 1, u} J R).obj L) ⋙
              WeilConjectures.SfbHomFilteredColimit.homFixed.{u + 1, u, u} J R P)) ∧
  (∀ i,
    (WeilConjectures.SfbHomFilteredColimit.homFixed.{u + 1, u, u} J R P).map
        ((WeilConjectures.SfbHomFilteredColimit.tensor.{u + 1, u, u} J R).map
          (c.ι.app i, 𝟙 L)) ≫
      WeilConjectures.SfbHomFilteredColimit.roofDenominator.{u + 1, u, u} J R P L c.pt =
    WeilConjectures.SfbHomFilteredColimit.roofDenominator.{u + 1, u, u} J R P L
        (T.obj i) ≫
      (WeilConjectures.SfbHomFilteredColimit.homFixed.{u + 1, u, u} J R P).map
        ((WeilConjectures.SfbHomFilteredColimit.tensor.{u + 1, u, u} J R).map
          (c.ι.app i, 𝟙 ((WeilConjectures.coefficientHomResolution.{u, u + 1, u} J R).obj L))))

attribute [local irreducible] coefficients coefficientCocone complexForward

/-- The strict formula on the given finite-field diagram and its specified closure vertex.
Source: DAG displayed three-arrow formula; Bhatt--Scholze 6.8.2(2)
(blueprint: lem-sfb-qlbar-internal-hom-coefficient-comparison). -/
def ColimitFormula (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (P L : CochainComplex (Modules (Profinite.continuousMapRingObj E) X) ℤ) : Prop :=
  StrictColimitFormula (Scheme.ProEt.topology X)
    (ring (Profinite.continuousMapRingObj E) X) (coefficients X ℓ E)
      (coefficientCocone X ℓ E) P L

/-- The tail is small, filtered and cofinal, and its stages are finite free.
Source: DAG proof steps 1--2, Bhatt--Scholze 6.8.2(2).
(blueprint: lem-sfb-qlbar-internal-hom-coefficient-comparison).
Proof: E is an initial tail object. Finite composita give common upper bounds;
EH shows cofinality above any finite field H. Transport through AsSmall. A finite
E-basis of F gives the finite free module isomorphism after inverse image; F=E
uses the rank-one identity. This is det-def-sfb-qlbar-condensed-subextensions and
sk-prop-sfb-cartesian-coefficients, without a geometric hypothesis on X. -/
theorem fieldDiagram (E : PadicAlgCl.FiniteIntermediateField ℓ) :
    IsFiltered (AsSmall.{u + 1} (Under E)) ∧ (fields ℓ E).Final ∧
    ∀ (F : PadicAlgCl.FiniteIntermediateField ℓ) (h : E ≤ F),
      ∃ d : ℕ, Nonempty
        (Mod.finiteFree (padicSubfieldRingObj X ℓ E) d ≅
          (Mod.comap (padicSubfieldRingObjMap X ℓ h)).obj
            (Mod.regular (padicSubfieldRingObj X ℓ F))) := by
  sorry

attribute [local irreducible] completedSubfieldCocone ColimitFormula Continuous

/-- The complex-defined coefficient diagram has the actual regular field coefficients.
The identifications retain every field inclusion and the closure cocone legs.
Source: DAG coefficient diagram and proof steps 2--3, Bhatt--Scholze 6.8.2(2)
(blueprint: lem-sfb-qlbar-internal-hom-coefficient-comparison).
Proof: extension of the regular E-module is the regular target module by
multiplication, s tensor e maps to s e. Its inverse sends s to s tensor 1.
Apply section reconstruction in degree zero. The actual mixedScalarMap and its
extend-pi formula give the transition and closure equations on these generators. -/
theorem coefficientModules (E : PadicAlgCl.FiniteIntermediateField ℓ) :
    ∃ (stage : ∀ i : AsSmall.{u + 1} (Under E),
        (coefficients X ℓ E).obj i ≅ qlbarTailStage X ℓ
          (leOfHom (((AsSmall.equiv (C := Under E)).inverse.obj i).hom)))
      (vertex : (coefficientCocone X ℓ E).pt ≅ qlbarTailVertex X ℓ E),
      (∀ (i j : AsSmall.{u + 1} (Under E)) (f : i ⟶ j) (V : X.ProEtᵒᵖ)
        (x : ((coefficients X ℓ E).obj i).val.obj V),
        (stage j).hom.val.app V (((coefficients X ℓ E).map f).val.app V x) =
          (padicSubfieldRingObjMap X ℓ (leOfHom ((fields ℓ E).map f))).hom.app V
            ((stage i).hom.val.app V x)) ∧
      (∀ (i : AsSmall.{u + 1} (Under E)) (V : X.ProEtᵒᵖ)
        (x : ((coefficients X ℓ E).obj i).val.obj V),
        vertex.hom.val.app V (((coefficientCocone X ℓ E).ι.app i).val.app V x) =
          (padicSubfieldRingObjToPadicAlgCl X ℓ ((fields ℓ E).obj i)).hom.app V
            ((stage i).hom.val.app V x)) := by
  sorry

/-- The algebraic-closure cocone is also the ring-algebra colimit on the tail.
Source: DAG coefficient-colimit clause, Bhatt--Scholze 6.8.2(2)
(blueprint: lem-sfb-qlbar-internal-hom-coefficient-comparison).
Proof: fieldDiagram gives cofinality. Restrict completedSubfieldCocone along fields.
For a tail cocone extend its H-leg through EH. The full coefficient colimit yields
a unique map; its E-leg fixes the E-algebra structure, so it is the algebra colimit. -/
theorem coefficientRingColimit (E : PadicAlgCl.FiniteIntermediateField ℓ) :
    Nonempty (IsColimit ((completedSubfieldCocone X ℓ).whisker (fields ℓ E))) := by
  sorry

/-- All three arrows of the strict colimit formula and the transition squares.
Representatives alone are K-flat and bounded: these impose no condition on K,L beyond
those in the main theorem. The numerator is the unique evaluation-normalized map.
Source: DAG displayed formula, Bhatt--Scholze 6.8.14--6.8.15
(blueprint: lem-sfb-qlbar-internal-hom-coefficient-comparison).
Proof: the coefficient module cocone is a colimit by the tail-module lemma. Tensor
preserves this colimit. Finite freeness makes every stage numerator a quasi-isomorphism.
Exact filtered colimits preserve their quasi-isomorphisms. Apply continuity to the
common lower bound of F tensor L; the resolution units identify the I(L) models.
K-flatness gives the denominator quasi-isomorphisms.
Naturality of the normalized numerator and resolution unit gives both cocone squares.
The evaluation-roof identity of the general comparison identifies the resulting
numerator/inverse-denominator roof with the restriction characterized above. -/
theorem coefficient_colimit_formula
    (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (K : DerivedCategory (Internal (Profinite.continuousMapRingObj E) X))
    (hK : Continuous X ℓ E K)
    (P L : CochainComplex (Modules (Profinite.continuousMapRingObj E) X) ℤ)
    (eP : DerivedCategory.Q.obj P ≅ (forward (Profinite.continuousMapRingObj E) X).obj K)
    (hP : CochainComplex.IsKFlatIndependentCoefficients
      (J := Scheme.ProEt.topology X) (R := ring (Profinite.continuousMapRingObj E) X) P)
    (hflat : ∀ n : ℤ, SheafOfModules.IsFlatOnSite
      (J := Scheme.ProEt.topology X) (R := ring (Profinite.continuousMapRingObj E) X) (P.X n))
    (hL : ∃ b : ℤ, ∀ n : ℤ, n < b → IsZero (L.X n)) :
    ColimitFormula X ℓ E P L := by
  sorry

/-- Evaluation normalization of the internal-to-section Hom isomorphism.
This is precisely the equation in the recorded module-object comparison.
Source: DAG proof step 5, Stacks 08J9
(blueprint: lem-sfb-qlbar-internal-hom-coefficient-comparison). -/
def HomTransportNormalized
    (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj R] [IsCommMonObj R]
    (S : WeilConjectures.CoefficientClosedStructure (hom R X))
    (T : WeilConjectures.CoefficientTensorModels.{u, u + 1, u, u + 1}
      (Scheme.ProEt.topology X) (ring R X) S)
    (t : TensorComparison R X S T)
    (θ : Functor.uncurry.obj (CondensedRing.derivedHom R X) ⋙ forward R X ≅
      ((forward R X).op.prod (forward R X)) ⋙ hom R X) : Prop :=
  ∀ K N : DerivedCategory (Internal R X),
    (forward R X).map
      ((@BraidedCategory.braiding _ _ _ (internalBraiding R X)
          (((CondensedRing.derivedHom R X).obj (op K)).obj N) K).hom ≫
        (CondensedRing.derivedTensorHomAdjunction R K).counit.app N) =
      t.iso.hom.app (((CondensedRing.derivedHom R X).obj (op K)).obj N, K) ≫
        S.tensor.map
          (X := ((forward R X).obj (((CondensedRing.derivedHom R X).obj (op K)).obj N),
            (forward R X).obj K))
          (Y := ((hom R X).obj (op ((forward R X).obj K), (forward R X).obj N),
            (forward R X).obj K))
          (θ.hom.app (op K, N), 𝟙 ((forward R X).obj K)) ≫
        S.evaluation ((forward R X).obj K) ((forward R X).obj N)

section ScalarRoof
variable {R S : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
  [MonObj R] [IsCommMonObj R] [MonObj S] [IsCommMonObj S]
  (a : R ⟶ S) [IsMonHom a]
  [∀ Z : Scheme.{u}, PreservesFiniteLimits (Mod.extendScalars (coefficientMap a Z))]

set_option hygiene false in
local notation "J" => Scheme.ProEt.topology X
set_option hygiene false in
local notation "B" => CondensedRing.internalScalarExtension a X
set_option hygiene false in
local notation "U" => Mod.comap (coefficientMap a X)
set_option hygiene false in
local notation "b" => InternalAbelianSheafModule.sectionScalarMap.{u + 1, u + 1, u}
  (Scheme.ProEt.topology X) (coefficientMap a X)

/-- The native evaluation transpose agrees with the normalized ringed evaluation roof.
The scalar unit fixes the extension transport, restriction fixes every section, and
both Hom transports preserve evaluation. The fixed roof supplies the strict numerator
and inverse denominator in coefficient_colimit_formula.
Source: DAG displayed formula and proof steps 5--6, Stacks 08J9 and 0A95
(blueprint: lem-sfb-qlbar-internal-hom-coefficient-comparison).
Proof: apply the section scalar-adjunction comparison to a. Localize its identity
restriction and generator-normalized extension. Choose simultaneous normalized ringed
closed and scalar models. The module-object tensor-Hom comparison supplies tR,tS and
the evaluation-normalized theta maps. The scalar-unit equation follows from equality
of the derived transposes. Transpose both sides of the final equation: the pure-tensor
normalizations give the same extended evaluation, hence the maps are equal. The
recorded flat evaluation-roof theorem provides the last roof data. -/
theorem coefficient_comparison_roof :
    letI : ∀ A : Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1},
        HasDerivedCategory.{u + 1}
          (SheafOfModules.scalarModules (Scheme.ProEt.topology X) A) :=
      fun A ↦ inferInstanceAs (HasDerivedCategory.{u + 1}
        (WeilConjectures.SfbHomFilteredColimit.Modules.{u + 1, u, u}
          (Scheme.ProEt.topology X) A))
    ∃ (M : ScalarHomModels.{u + 1, u, u, u + 1} J)
      (μ : ∀ {A D : Sheaf J CommRingCat.{u + 1}} (f : A ⟶ D),
        ScalarHomTensorComparison.{u + 1, u, u, u + 1} M f)
      (α : ScalarInternalHomAdjunction.{u + 1, u, u, u + 1} M μ)
      (r : U ⋙ (equivalence R X).functor ≅
        (equivalence S X).functor ⋙ SheafOfModules.scalarRestriction.{u + 1, u, u + 1} b),
      (∀ (N : Internal S X) (V : X.ProEtᵒᵖ)
        (x : (((U ⋙ (equivalence R X).functor).obj N).val.obj V)),
        HEq ((r.hom.app N).val.app V x) x) ∧
      ∃ (γ : B ⋙ forward S X ≅ forward R X ⋙ (M.scalar b).derived)
        (ρ : (Mod.comap (coefficientMap a X)).mapDerivedCategory ⋙ forward R X ≅
          forward S X ⋙ SheafOfModules.scalarDerivedRestriction b)
        (tR : TensorComparison R X (M.closed (ring R X)) (M.model (ring R X)))
        (tS : TensorComparison S X (M.closed (ring S X)) (M.model (ring S X)))
        (θR : Functor.uncurry.obj (CondensedRing.derivedHom R X) ⋙ forward R X ≅
          ((forward R X).op.prod (forward R X)) ⋙ hom R X)
        (θS : Functor.uncurry.obj (CondensedRing.derivedHom S X) ⋙ forward S X ≅
          ((forward S X).op.prod (forward S X)) ⋙ hom S X),
        HomTransportNormalized X R (M.closed (ring R X)) (M.model (ring R X)) tR θR ∧
        HomTransportNormalized X S (M.closed (ring S X)) (M.model (ring S X)) tS θS ∧
        HEq ρ
          ((Functor.mapDerivedCategoryCompIso U (equivalence R X).functor).symm ≪≫
            Functor.mapDerivedCategoryNatIso r ≪≫
            Functor.mapDerivedCategoryCompIso (equivalence S X).functor
              (SheafOfModules.scalarRestriction.{u + 1, u, u + 1} b)) ∧
        (∀ K : DerivedCategory (Internal R X),
          (forward R X).map
              ((Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap a X)).unit.app K) ≫
            ρ.hom.app ((CondensedRing.internalScalarExtension a X).obj K) ≫
            (SheafOfModules.scalarDerivedRestriction b).map (γ.hom.app K) =
          (M.scalar b).adjunction.unit.app ((forward R X).obj K)) ∧
        Nonempty (SfbFlatHom.EvaluationRoof.{u + 1, u, u, u + 1} M μ α) ∧
        ∀ K L : DerivedCategory (Internal R X),
          (forward S X).map (evaluationComparison X a K L) ≫
              θS.hom.app (op ((CondensedRing.internalScalarExtension a X).obj K),
                (CondensedRing.internalScalarExtension a X).obj L) ≫
              (hom S X).map (Prod.mkHom (γ.inv.app K).op (γ.hom.app L)) =
            γ.hom.app (((CondensedRing.derivedHom R X).obj (op K)).obj L) ≫
              (M.scalar b).derived.map (θR.hom.app (op K, L)) ≫
              SfbFlatHom.comparison.{u + 1, u, u, u + 1} M μ b
                ((forward R X).obj K) ((forward R X).obj L) := by
  sorry

end ScalarRoof

/-- The canonical comparison is invertible for every continuous first input and every
cohomologically bounded-below second input, in the ordinary module-object categories.
Source: Bhatt--Scholze 6.8.14--6.8.15; explicit conditional argument of the DAG
(blueprint: lem-sfb-qlbar-internal-hom-coefficient-comparison).
Proof:
1. fieldDiagram gives the small filtered cofinal tail and finite free stages.
2. The coefficient maps compose by lem-sfb-subfield-coefficient-map-comp.
   Restrict the ring cocone of sk-prop-sfb-qlbar-colimit-x to the cofinal tail.
   lem-sfb-qlbar-tail-module-colimit identifies its underlying module colimit
   with the same legs and scalar action.
3. Exact filtered colimits follow from the faithful exact module forgetful functor
   and exact filtered colimits of abelian sheaves (03DA, 03DB, 03CO).
4. lem-sfb-module-object-ringed-site-derived-comparison and
   lem-pe-internal-section-tensor-comparison transport tensor, Hom, evaluation,
   lower bounds and the continuity hypothesis to ringed-site module sheaves.
5. Choose a K-flat representative of K and a bounded-below representative of L.
   Apply lem-sfb-dc-hom-filtered-colimit to the finite-free coefficient diagram.
   Its scalarComparison_restriction and filteredColimit_comparison give the
   three-arrow colimit formula. Evaluation normalization identifies its map with
   evaluationComparison. Transport back. No bound on RHom(K,L) is used. -/
theorem qlbar_internalHom_coefficient_comparison
    (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (K L : DerivedCategory (Internal (Profinite.continuousMapRingObj E) X))
    (hK : Continuous X ℓ E K) (hL : ∃ b : ℤ, L.IsGE b) :
    IsIso (evaluationComparison X (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E) K L) := by
  sorry

end AlgebraicGeometry.ProEtale.QlbarInternalHom
