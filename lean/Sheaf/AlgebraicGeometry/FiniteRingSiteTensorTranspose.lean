/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q21
-/
module

public import Sheaf.Paper.FiniteFieldFiber
public import Sheaf.Paper.FiniteComparisonLocalizing
public import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjection
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.FlatModuleCat
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.Monoidal
public import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategoryBraided
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ComparisonMonoidal
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriekProjection

public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekLeftAdjoint
public import Sheaf.Paper.LocalizingExceptionalAdjoint
public import Sheaf.AlgebraicGeometry.ProEtaleExtensionZeroComparison
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.AB
public import Sheaf.AlgebraicGeometry.ProperProjectionFormula
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Topology.Defs.Filter
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
public import WeilConjectures.SixFunctors.Etale.Derived.Tensor
import Sheaf.AlgebraicGeometry.FiniteRingEtaleCompactGenerators
import WeilConjectures.CategoryTheory.WeakTriangulatedGenerator
import WeilConjectures.CategoryTheory.CompactGeneratorsBuildObjects
import Sheaf.AlgebraicGeometry.UnboundedSiteComparison
import Sheaf.AlgebraicGeometry.ProEtaleOpenTensor
import Sheaf.AlgebraicGeometry.ProEtaleIntrinsicExtensionByZeroAdjunction
import Sheaf.AlgebraicGeometry.ProEtaleIntrinsicExtensionByZeroExact
import Sheaf.AlgebraicGeometry.UnboundedDirectImageComparison
import WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjection
import WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekProjection
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs

/-!
# Finite-ring transport of projection maps and integration transposes

Source: blueprint main-20261015, sec-smooth-purity/sk-thm-smooth-purity/
sk-thm-smooth-purity-general-ring.proof.md, Proof (3), and
lem-pur-finite-ring-site-tensor-transpose, assertions 1--3
(blueprint: lem-pur-finite-ring-site-tensor-transpose).

All categories below are ordinary unbounded categories with constant finite coefficients.
The pro-etale closure is the recorded closure transported by the finite-discrete ring
identification. The auxiliary abbreviations expose the specified functors and canonical maps.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u uA v

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

/-- Exact, termwise site inverse image. Source: blueprint, assertion 1
(blueprint: lem-pur-finite-ring-site-tensor-transpose). -/
abbrev finiteRingSitePull (B : Type) [CommRing B] [Finite B] (T : Scheme.{u}) :=
  (comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1} B)) T).mapDerivedCategory

/-- Canonical tensor comparison, transported from the left derived functor to the
termwise exact inverse image. Its K-flat normalization is the ordinary pure-tensor map.
Source: blueprint proof step 5; Stacks 07A4
(blueprint: lem-pur-finite-ring-site-tensor-transpose). -/
@[irreducible] def finiteRingSiteTensor
    (A : Type uA) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
    [SymmetricCategory A] [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
    (T : Scheme.{u}) [(comparisonUpperStar A T).PreservesFlat]
    (M N : DerivedCategory (Sheaf T.smallEtaleTopology A)) :
    (comparisonUpperStar A T).mapDerivedCategory.obj (M ⊗ N) ≅
      (comparisonUpperStar A T).mapDerivedCategory.obj M ⊗
        (comparisonUpperStar A T).mapDerivedCategory.obj N :=
  (derivedTensorObjCompMapDerivedCategoryComparisonUpperStarIso A M).app N

/-- The unit comparison is the image of the ordinary constant-ring unit comparison.
Source: blueprint proof step 5; Stacks 07A4
(blueprint: lem-pur-finite-ring-site-tensor-transpose). -/
@[irreducible] def finiteRingSiteUnit (A : Type uA) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
    [SymmetricCategory A] [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
    (T : Scheme.{u}) :
    (comparisonUpperStar A T).mapDerivedCategory.obj (𝟙_ _) ≅ 𝟙_ _ :=
  ((comparisonUpperStar A T).mapDerivedCategoryFactors).app _ ≪≫
  DerivedCategory.Q.mapIso
    (((HomologicalComplex.singleMapHomologicalComplex
      (comparisonUpperStar A T) (.up ℤ) 0).app _) ≪≫
    (HomologicalComplex.single _ (.up ℤ) 0).mapIso
      (Functor.Monoidal.εIso
        (comparisonUpperStar A T)).symm)

/-- The pullback identification with the derived inverse images used by the projection maps.
Source: blueprint proof step 5; the exact/left-derived identifications are canonical
(blueprint: lem-pur-finite-ring-site-tensor-transpose). -/
@[irreducible] def finiteRingSitePullback
    (A : Type uA) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
    [SymmetricCategory A] [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (square : (comparisonUpperStar A Y).mapDerivedCategory ⋙
      (upperStar A f).mapDerivedCategory ≅
        (Etale.upperStar A f).mapDerivedCategory ⋙ (comparisonUpperStar A X).mapDerivedCategory)
    (K : DerivedCategory (Sheaf Y.smallEtaleTopology A)) :
    (comparisonUpperStar A X).mapDerivedCategory.obj
        ((Etale.upperStar A f).leftDerivedFunctor.obj K) ≅
      (upperStar A f).leftDerivedFunctor.obj
        ((comparisonUpperStar A Y).mapDerivedCategory.obj K) :=
  (comparisonUpperStar A X).mapDerivedCategory.mapIso
    ((Etale.upperStar A f).leftDerivedFunctorIsoMapDerivedCategory.app K) ≪≫
  square.symm.app K ≪≫
  ((upperStar A f).leftDerivedFunctorIsoMapDerivedCategory.app
    ((comparisonUpperStar A Y).mapDerivedCategory.obj K)).symm

/-- Ordinary etale compact supports for the fixed compactification.
Source: blueprint assertion 1 (blueprint: lem-pur-finite-ring-site-tensor-transpose). -/
abbrev finiteRingEtaleShriek (B : Type) [CommRing B] {X Y : Scheme.{u}}
    {f : X ⟶ Y} (c : Compactification f) :=
  Etale.rightDerivedLowerShriekOfCompactification
    (ModuleCat.{u + 1} (ULift.{u + 1} B)) c

/-- Ordinary pro-etale compact supports before restriction to the localizing closure.
Source: blueprint assertion 1 (blueprint: lem-pur-finite-ring-site-tensor-transpose). -/
abbrev finiteRingProShriek (B : Type) [CommRing B] {X Y : Scheme.{u}}
    {f : X ⟶ Y} (c : Compactification f) :=
  rightDerivedLowerShriekOfCompactification
    (ModuleCat.{u + 1} (ULift.{u + 1} B)) c

/-- The canonical etale projection-map component, with abstract coefficients.
Source: blueprint assertion 2 (blueprint: lem-pur-finite-ring-site-tensor-transpose). -/
@[irreducible] def finiteRingEtalePF
    (A : Type uA) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
    [SymmetricCategory A] [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
    [Etale.UpperStarPreservesFlat A]
    {FC : A → A → Type v} {CC : A → Type (u + 1)}
    [∀ P Q : A, FunLike (FC P Q) (CC P) (CC Q)] [ConcreteCategory.{u + 1} A FC]
    [(CategoryTheory.forget A).ReflectsIsomorphisms]
    [PreservesFilteredColimitsOfSize.{u + 1, u + 1} (CategoryTheory.forget A)]
    [∀ Z : Scheme.{u}, Z.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget A)]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (M : DerivedCategory (Sheaf X.smallEtaleTopology A))
    (K : DerivedCategory (Sheaf Y.smallEtaleTopology A)) :
    (Etale.rightDerivedLowerShriekOfCompactification A c).obj M ⊗ K ⟶
      (Etale.rightDerivedLowerShriekOfCompactification A c).obj
        (M ⊗ (Etale.upperStar A f).leftDerivedFunctor.obj K) :=
  ((Etale.projectionMapOfCompactification A c).app M).app K

/-- The canonical pro-etale projection-map component, with abstract coefficients.
Source: blueprint assertion 2 (blueprint: lem-pur-finite-ring-site-tensor-transpose). -/
@[irreducible] def finiteRingProPF
    (A : Type uA) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
    [SymmetricCategory A] [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
    [UpperStarPreservesFlat A]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (M : DerivedCategory (Sheaf (Scheme.ProEt.topology X) A))
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology Y) A)) :
    (rightDerivedLowerShriekOfCompactification A c).obj M ⊗ K ⟶
      (rightDerivedLowerShriekOfCompactification A c).obj
        (M ⊗ (upperStar A f).leftDerivedFunctor.obj K) :=
  ((projectionMapOfCompactification A c).app M).app K

universe u₁ u₂ u₃ u₄ v₁ v₂ v₃ v₄

/-- Restriction of a functor to the indicated full subcategories.
Source: blueprint assertion 1 (blueprint: lem-pur-finite-ring-site-tensor-transpose). -/
abbrev finiteRingRestriction
    {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    (F : C ⥤ D) (P : ObjectProperty C) (Q : ObjectProperty D)
    (h : ∀ N, P N → Q (F.obj N)) :=
  Q.lift (P.ι ⋙ F) (fun N ↦ h N.obj N.property)

/-- Restriction of the codomain of the exact site comparison to its image.
Source: blueprint assertion 1 (blueprint: lem-pur-finite-ring-site-tensor-transpose). -/
abbrev finiteRingImageLift
    {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    (E : C ⥤ D) (P : ObjectProperty D) (h : ∀ M, P (E.obj M)) :=
  P.lift E h

/-- The composite tensor and pullback comparison, retaining its specified two factors.
Source: blueprint proof step 5 (blueprint: lem-pur-finite-ring-site-tensor-transpose). -/
def finiteRingTensorPullbackComparison
    {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
    {D : Type u₂} [Category.{v₂} D]
    {C' : Type u₃} [Category.{v₃} C'] [MonoidalCategory C']
    {D' : Type u₄} [Category.{v₄} D']
    (E : C ⥤ C') (P : D ⥤ C) (P' : D' ⥤ C') (E' : D ⥤ D')
    (tensor : ∀ M N, E.obj (M ⊗ N) ≅ E.obj M ⊗ E.obj N)
    (pullback : ∀ K, E.obj (P.obj K) ≅ P'.obj (E'.obj K))
    (M : C) (K : D) :
    E.obj (M ⊗ P.obj K) ≅ E.obj M ⊗ P'.obj (E'.obj K) :=
  tensor M (P.obj K) ≪≫ tensorIso (Iso.refl _) (pullback K)

/-- The three categorical assertions of finite-ring site transport, with the categories
and the specified maps kept abstract to avoid expanding K-flat constructions at each use.
The main theorem specializes every argument to its recorded canonical construction.
Source: blueprint assertions 1--3
(blueprint: lem-pur-finite-ring-site-tensor-transpose). -/
def finiteRingSiteTensorTransposeStatement
    {EXCat : Type u₁} [Category.{v₁} EXCat] [MonoidalCategory EXCat]
    {EYCat : Type u₂} [Category.{v₂} EYCat] [MonoidalCategory EYCat]
    {PXCat : Type u₃} [Category.{v₃} PXCat] [MonoidalCategory PXCat]
    {PYCat : Type u₄} [Category.{v₄} PYCat] [MonoidalCategory PYCat]
    (EX : EXCat ⥤ PXCat) (EY : EYCat ⥤ PYCat)
    (FE : EXCat ⥤ EYCat) (FP : PXCat ⥤ PYCat)
    (PE : EYCat ⥤ EXCat) (PP : PYCat ⥤ PXCat)
    (PX : ObjectProperty PXCat) (PY : ObjectProperty PYCat)
    (beta : ∀ M, EY.obj (FE.obj M) ⟶ FP.obj (EX.obj M))
    (tensorX : ∀ M N, EX.obj (M ⊗ N) ≅ EX.obj M ⊗ EX.obj N)
    (tensorY : ∀ M N, EY.obj (M ⊗ N) ≅ EY.obj M ⊗ EY.obj N)
    (unitY : EY.obj (𝟙_ EYCat) ≅ 𝟙_ PYCat)
    (pullback : ∀ K, EX.obj (PE.obj K) ≅ PP.obj (EY.obj K))
    (symE : BraidedCategory EXCat)
    (symP : BraidedCategory PXCat)
    (pfE : ∀ M K, FE.obj M ⊗ K ⟶ FE.obj (M ⊗ PE.obj K))
    (pfP : ∀ M K, FP.obj M ⊗ K ⟶ FP.obj (M ⊗ PP.obj K)) : Prop :=
    (EX).Full ∧ (EX).Faithful ∧
    (∀ N, (EX).essImage N ↔ PX N) ∧
    ∃ (hX : ∀ M, PX ((EX).obj M))
      (hY : ∀ K, PY ((EY).obj K))
      (b : FE ⋙ EY ≅
        EX ⋙ FP),
      (∀ M, b.hom.app M = beta M) ∧
      ∀ (hs : ∀ N, PX N →
          PY ((FP).obj N))
        (R : EYCat ⥤
          EXCat)
        (ae : FE ⊣ R)
        (G : (PY).FullSubcategory ⥤
          (PX).FullSubcategory)
        (ap : finiteRingRestriction FP PX PY hs ⊣ G),
        ∃ (rho : R ⋙ finiteRingImageLift EX PX hX ≅ finiteRingImageLift EY PY hY ⋙ G),
          (∀ L, b.hom.app (R.obj L) ≫
              (FP).map (rho.hom.app L).hom ≫
              (ap.counit.app ((finiteRingImageLift EY PY hY).obj L)).hom =
            (EY).map (ae.counit.app L)) ∧
          (∀ sigma : R ⋙ finiteRingImageLift EX PX hX ≅
              finiteRingImageLift EY PY hY ⋙ G,
            (∀ L, b.hom.app (R.obj L) ≫
                (FP).map (sigma.hom.app L).hom ≫
                (ap.counit.app ((finiteRingImageLift EY PY hY).obj L)).hom =
              (EY).map (ae.counit.app L)) → sigma = rho) ∧
          ∃ (pe : ∀ M K, (FE).obj M ⊗ K ≅
              (FE).obj ((M ⊗ PE.obj K)))
            (pp : ∀ M K, (FP).obj ((EX).obj M) ⊗
                (EY).obj K ≅
              (FP).obj ((EX.obj M ⊗ PP.obj (EY.obj K))))
            (ht : ∀ M K,
              PX ((EX.obj M ⊗ PP.obj (EY.obj K)))),
            (∀ M K, (pe M K).hom =
              pfE M K) ∧
            (∀ M K, (pp M K).hom =
              pfP (EX.obj M) (EY.obj K)) ∧
            (∀ M K,
              (EY).map
                  (pfE M K) ≫
                  b.hom.app ((M ⊗ PE.obj K)) ≫
                  (FP).map
                    (finiteRingTensorPullbackComparison EX PE PP EY tensorX pullback M K).hom =
                (tensorY (FE.obj M) K).hom ≫
                  (b.hom.app M ⊗ₘ 𝟙 ((EY).obj K)) ≫
                  pfP (EX.obj M) (EY.obj K)) ∧
            (∀ (M : EXCat)
              (K : EYCat)
              (e : (FE).obj M ⟶ 𝟙_ _),
              (EX).map
                  (ae.homEquiv _ _ ((pe M K).inv ≫ (e ⊗ₘ 𝟙 K) ≫ (λ_ K).hom)) ≫
                  (rho.hom.app K).hom =
                (finiteRingTensorPullbackComparison EX PE PP EY tensorX pullback M K).hom ≫
                  (ap.homEquiv ⟨(EX.obj M ⊗ PP.obj (EY.obj K)), ht M K⟩
                    ((finiteRingImageLift EY PY hY).obj K)
                    (ObjectProperty.homMk ((pp M K).inv ≫
                      (((b.app M).inv ≫ (EY).map e ≫
                        (unitY).hom) ⊗ₘ
                          𝟙 ((EY).obj K)) ≫
                      (λ_ ((EY).obj K)).hom))).hom) ∧
            (∀ (M : EXCat)
              (K : EYCat)
              (e : (FE).obj M ⟶ 𝟙_ _),
              (EX).map
                  ((@BraidedCategory.braiding EXCat _ _ symE (PE.obj K) M).hom ≫
                    ae.homEquiv _ _ ((pe M K).inv ≫ (e ⊗ₘ 𝟙 K) ≫ (λ_ K).hom)) ≫
                  (rho.hom.app K).hom =
                (tensorX (PE.obj K) M).hom ≫
                  ((pullback K).hom ⊗ₘ
                    𝟙 ((EX).obj M)) ≫
                  (@BraidedCategory.braiding PXCat _ _ symP (PP.obj (EY.obj K)) (EX.obj M)).hom ≫
                  (ap.homEquiv ⟨(EX.obj M ⊗ PP.obj (EY.obj K)), ht M K⟩
                    ((finiteRingImageLift EY PY hY).obj K)
                    (ObjectProperty.homMk ((pp M K).inv ≫
                      (((b.app M).inv ≫ (EY).map e ≫
                        (unitY).hom) ⊗ₘ
                          𝟙 ((EY).obj K)) ≫
                      (λ_ ((EY).obj K)).hom))).hom)

/-- The categorical transport formulas applied to the actual six site functors.
Keeping this partial application named shares the derived-category instance data.
Source: blueprint assertions 1--3
(blueprint: lem-pur-finite-ring-site-tensor-transpose). -/
@[irreducible] def finiteRingSiteTensorTransposeSiteFunctors
    (A : Type uA) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
    [SymmetricCategory A] [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
    [Etale.UpperStarPreservesFlat A] [UpperStarPreservesFlat A]
    {FC : A → A → Type v} {CC : A → Type (u + 1)}
    [∀ P Q : A, FunLike (FC P Q) (CC P) (CC Q)] [ConcreteCategory.{u + 1} A FC]
    [(CategoryTheory.forget A).ReflectsIsomorphisms]
    [PreservesFilteredColimitsOfSize.{u + 1, u + 1} (CategoryTheory.forget A)]
    [∀ T : Scheme.{u}, T.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget A)]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) :=
  finiteRingSiteTensorTransposeStatement
    (comparisonUpperStar A X).mapDerivedCategory
    (comparisonUpperStar A Y).mapDerivedCategory
    (Etale.rightDerivedLowerShriekOfCompactification A c)
    (rightDerivedLowerShriekOfCompactification A c)
    (Etale.upperStar A f).leftDerivedFunctor (upperStar A f).leftDerivedFunctor

/-- The site transport assertion with its canonical tensor, unit and pullback maps.
Source: blueprint proof step 5 (blueprint: lem-pur-finite-ring-site-tensor-transpose). -/
@[irreducible] def finiteRingSiteTensorTransposeCanonicalTensor
    (A : Type uA) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
    [SymmetricCategory A] [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
    [Etale.UpperStarPreservesFlat A] [UpperStarPreservesFlat A]
    {FC : A → A → Type v} {CC : A → Type (u + 1)}
    [∀ P Q : A, FunLike (FC P Q) (CC P) (CC Q)] [ConcreteCategory.{u + 1} A FC]
    [(CategoryTheory.forget A).ReflectsIsomorphisms]
    [PreservesFilteredColimitsOfSize.{u + 1, u + 1} (CategoryTheory.forget A)]
    [∀ T : Scheme.{u}, T.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget A)]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    [(comparisonUpperStar A X).PreservesFlat] [(comparisonUpperStar A Y).PreservesFlat]
    (PX : ObjectProperty (DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)))
    (PY : ObjectProperty (DerivedCategory (Sheaf (Scheme.ProEt.topology Y) A)))
    (beta : ∀ M, (comparisonUpperStar A Y).mapDerivedCategory.obj
        ((Etale.rightDerivedLowerShriekOfCompactification A c).obj M) ⟶
      (rightDerivedLowerShriekOfCompactification A c).obj
        ((comparisonUpperStar A X).mapDerivedCategory.obj M))
    (square : (comparisonUpperStar A Y).mapDerivedCategory ⋙
      (upperStar A f).mapDerivedCategory ≅
        (Etale.upperStar A f).mapDerivedCategory ⋙ (comparisonUpperStar A X).mapDerivedCategory) :=
  finiteRingSiteTensorTransposeSiteFunctors A c
    PX PY beta (finiteRingSiteTensor A X) (finiteRingSiteTensor A Y)
    (finiteRingSiteUnit A Y) (finiteRingSitePullback A f square)

/-- The site transport assertion with the canonical signed symmetries on both sites.
Source: blueprint proof step 11 (blueprint: lem-pur-finite-ring-site-tensor-transpose). -/
@[irreducible] def finiteRingSiteTensorTransposeCanonicalSymmetry
    (A : Type uA) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
    [SymmetricCategory A] [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
    [Etale.UpperStarPreservesFlat A] [UpperStarPreservesFlat A]
    {FC : A → A → Type v} {CC : A → Type (u + 1)}
    [∀ P Q : A, FunLike (FC P Q) (CC P) (CC Q)] [ConcreteCategory.{u + 1} A FC]
    [(CategoryTheory.forget A).ReflectsIsomorphisms]
    [PreservesFilteredColimitsOfSize.{u + 1, u + 1} (CategoryTheory.forget A)]
    [∀ T : Scheme.{u}, T.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget A)]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    [(comparisonUpperStar A X).PreservesFlat] [(comparisonUpperStar A Y).PreservesFlat]
    (PX : ObjectProperty (DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)))
    (PY : ObjectProperty (DerivedCategory (Sheaf (Scheme.ProEt.topology Y) A)))
    (beta : ∀ M, (comparisonUpperStar A Y).mapDerivedCategory.obj
        ((Etale.rightDerivedLowerShriekOfCompactification A c).obj M) ⟶
      (rightDerivedLowerShriekOfCompactification A c).obj
        ((comparisonUpperStar A X).mapDerivedCategory.obj M))
    (square : (comparisonUpperStar A Y).mapDerivedCategory ⋙
      (upperStar A f).mapDerivedCategory ≅
        (Etale.upperStar A f).mapDerivedCategory ⋙ (comparisonUpperStar A X).mapDerivedCategory) :=
  finiteRingSiteTensorTransposeCanonicalTensor A c PX PY beta square
    (DerivedCategory.braidedCategory' (Sheaf X.smallEtaleTopology A))
    (DerivedCategory.braidedCategory' (Sheaf (Scheme.ProEt.topology X) A))

/-- The specified site transport assertion with its coefficient category abstract.
Every tensor, pullback, unit and symmetry argument is its canonical construction;
only the two closure predicates and the recorded compact-support comparison vary here.
Source: blueprint assertions 1--3
(blueprint: lem-pur-finite-ring-site-tensor-transpose). -/
def finiteRingSiteTensorTransposeWithCoefficients
    (A : Type uA) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
    [SymmetricCategory A] [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
    [Etale.UpperStarPreservesFlat A] [UpperStarPreservesFlat A]
    {FC : A → A → Type v} {CC : A → Type (u + 1)}
    [∀ P Q : A, FunLike (FC P Q) (CC P) (CC Q)] [ConcreteCategory.{u + 1} A FC]
    [(CategoryTheory.forget A).ReflectsIsomorphisms]
    [PreservesFilteredColimitsOfSize.{u + 1, u + 1} (CategoryTheory.forget A)]
    [∀ T : Scheme.{u}, T.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget A)]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    [(comparisonUpperStar A X).PreservesFlat] [(comparisonUpperStar A Y).PreservesFlat]
    (PX : ObjectProperty (DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)))
    (PY : ObjectProperty (DerivedCategory (Sheaf (Scheme.ProEt.topology Y) A)))
    (beta : ∀ M, (comparisonUpperStar A Y).mapDerivedCategory.obj
        ((Etale.rightDerivedLowerShriekOfCompactification A c).obj M) ⟶
      (rightDerivedLowerShriekOfCompactification A c).obj
        ((comparisonUpperStar A X).mapDerivedCategory.obj M))
    (square : (comparisonUpperStar A Y).mapDerivedCategory ⋙
      (upperStar A f).mapDerivedCategory ≅
        (Etale.upperStar A f).mapDerivedCategory ⋙ (comparisonUpperStar A X).mapDerivedCategory) :
    Prop :=
  finiteRingSiteTensorTransposeCanonicalSymmetry A c PX PY beta square
    (finiteRingEtalePF A c) (finiteRingProPF A c)

variable (B : Type) [CommRing B] [Finite B] [TopologicalSpace B]
  [DiscreteTopology B] [IsTopologicalRing B]
  (eR : Sheaf.sheafifyRingPresheaf.{u + 1, u, u + 1} (coherentTopology Profinite.{u})
    ((Functor.const Profinite.{u}ᵒᵖ).obj (RingCat.of (ULift.{u + 1} B))) ≅
      Profinite.continuousMapRingObj.{u} B) [IsMonHom eR.hom]

/-- Transport of the compact-support projection maps and integration transposes for
arbitrary finite primary rings. Right adjoints and their adjunctions are arbitrary choices
of the adjoints specified in the statement. Membership proofs only type the restrictions.
The isomorphisms `b`, `pe`, `pp` are pinned to the named canonical maps by their hom equations.

Source: blueprint main-20261015, sk-thm-smooth-purity-general-ring.proof.md, Proof (3),
and the full statement of lem-pur-finite-ring-site-tensor-transpose
(blueprint: lem-pur-finite-ring-site-tensor-transpose).

Proof (the node's eleven steps):
1. Finite-type schemes over the field are Noetherian by
   lem-weil-pbc-finite-type-over-noetherian, including the compactification scheme.
2. lem-pur-etale-finite-ring-compact-generators gives compact finite-Tor constructible
   generators. Detection gives def-pc-generators; lem-pc-compact-generators-build-objects
   expresses every object as the sequential homotopy colimit of sums, shifts and cones
   of these generators. Therefore their etale localizing closure is the entire category.
3. lem-sfb-unbounded-site-comparison gives fully faithful exact sum-preserving comparison.
   det-ctf-finite-comparison-localizing identifies its image with the indicated pro-etale
   closure, using the finite-discrete coefficient identification. Its compact-support
   comparison is lem-sfb-unbounded-direct-image-comparison at the open extension, followed
   by direct image of lem-cbc-proetale-extension-zero-comparison. Exactness of the two open
   extensions descends that comparison termwise, without bounds.
4. Transport thm-amb-etale-exceptional-adjoint through these equivalences. Its counit is
   the comparison image of the etale counit after the inverse compact-support comparison.
   det-sp-unique-right-adjoint compares it with sk-prop-sf-existence and proves the unique
   counit equation and naturality of rho.
5. On K-flat flat-term representatives the tensor and pullback comparisons of
   lem-weil-pbc-ringed-topoi-derived-tensor-pullback agree on every pure tensor. This also
   verifies the unit and signed symmetry, degree by degree in the total complexes.
6. For the proper factor transpose the transported projection map. The normalization of
   lem-sfb-unbounded-direct-image-comparison replaces its counit with the etale counit.
   The definition def-kun-projection-formula-map and cancellation of the comparison and
   its inverse leave exactly the counit tensored with identity. Adjunct injectivity gives
   equality with the pro-etale proper projection map.
7. lem-amb-proper-coproducts-projection makes the etale map invertible, in either tensor
   order; step 6 then makes its pro-etale counterpart invertible on comparison images.
8. The two open tensor comparisons commute with the open site comparison: restrict their
   adjuncts to the open, where both send each pure tensor to itself. Use
   lem-weil-extension-by-zero-adjunction, lem-pur-etale-open-derived-tensor and
   lem-trf-open-tensor. The equality descends from K-flat representatives.
9. Paste the proper and open squares. Naturality of the proper comparison identifies
   their outside edge with exactly the named compact-support comparison. Both etale
   factors are invertible; this square gives invertibility on pro-etale images as well.
10. For e, transpose its tensor composite on each site. Naturality of the comparison and
    the counit equation for rho identify the adjunct of the transported etale transpose.
    Invert step 9's square and use the unit normalization from step 5. This adjunct is
    precisely the pro-etale tensor composite, so injectivity of adjunction gives equality.
11. Precompose the transposes with the canonical signed symmetries to reverse the tensor
    order; step 5 carries those symmetries to each other. Empty schemes and the zero ring
    give zero categories and the same identities, with no nonemptiness assumption. -/
theorem finiteRingSiteTensorTranspose
    (D : WeilConjectures.FiniteFieldDatum.{u}) (ℓ : ℕ) [Fact ℓ.Prime]
    (hℓ : ℓ ≠ D.p) (hB : ∃ n : ℕ, (ℓ : B) ^ n = 0)
    {X Y : Scheme.{u}} [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [IsSeparated (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
    [IsSeparated (Y ↘ Spec (.of D.k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of D.k))] (c : Compactification f)
    [c.Z.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (c.Z ↘ Spec (.of D.k))] [QuasiCompact (c.Z ↘ Spec (.of D.k))]
    [IsSeparated (c.Z ↘ Spec (.of D.k))]
    [c.i.IsOver (Spec (.of D.k))] [c.g.IsOver (Spec (.of D.k))] :
    finiteRingSiteTensorTransposeWithCoefficients
      (ModuleCat.{u + 1} (ULift.{u + 1} B)) c
      (finiteComparisonProEtaleClosure B eR X) (finiteComparisonProEtaleClosure B eR Y)
      (finiteComparisonCompactSupportMap B c.i c.g)
      (unboundedDirectImagePullbackIso (ULift.{u + 1} B) f) := by
  sorry

end AlgebraicGeometry.ProEtale
