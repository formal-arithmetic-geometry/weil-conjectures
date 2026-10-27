/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q149
-/
module

public import Sheaf.Algebra.Homology.OrdinaryModuleDerivedInternalHom
public import Sheaf.Algebra.Homology.SitePerfectModelRestriction
public import Sheaf.CategoryTheory.LocalCoefficientLocalization
public import Sheaf.Paper.CoefficientHomRepresentativeEvaluation
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.CategoryTheory.Triangulated.HomologicalFunctor
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses

/-! # Local derived Hom, cohomological sequences, and the lower bound

Source: Stacks Project, sites-cohomology.tex, Tags 0A94 and 0A95; Modules on Sites,
Tag 03EI; Derived Categories, Tag 0149.
(blueprint: lem-per-rhom-local-cohomological-bound).
The local comparison retains the module structure, derived restriction, the cocycle
normalization, and the boundary, using the actual sheaf Hom complex and localization.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe uC vC u w wSlice
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite
namespace CategoryTheory.LocalRHom

variable {C : Type uC} [Category.{vC} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{max uC vC u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max uC vC u}]
  (R : Sheaf J CommRingCat.{max uC vC u})

/-- Forget commutativity without changing the coefficient universe. Source: Stacks 03DH
(blueprint: lem-per-rhom-local-cohomological-bound). -/
abbrev rings := (sheafCompose J (forget₂ CommRingCat.{max uC vC u} RingCat.{max uC vC u})).obj R

/-- The recorded module category. Source: Stacks 03DH
(blueprint: lem-per-rhom-local-cohomological-bound). -/
abbrev Mod := ringedSiteModules.{max uC vC u} (rings.{uC, vC, u} J R)

variable [∀ U : C, HasSheafify (J.over U) AddCommGrpCat.{max uC vC u}]
  [∀ U : C, (J.over U).WEqualsLocallyBijective AddCommGrpCat.{max uC vC u}]
  [HasDerivedCategory.{w} (Mod.{uC, vC, u} J R)]
  [∀ U : C, HasDerivedCategory.{wSlice} (SheafOfModules.{max uC vC u} ((rings.{uC, vC, u} J R).over
    U))]

/-- The recorded derived category. Source: Stacks 05RR
(blueprint: lem-per-rhom-local-cohomological-bound). -/
abbrev D := DerivedCategory (Mod.{uC, vC, u} J R)

/-- The recorded derived internal Hom with fixed source. Source: Stacks 0A95
(blueprint: lem-per-rhom-local-cohomological-bound). -/
abbrev RH (K : D.{uC, vC, u, w} J R) :=
  (Functor.curry.obj (derivedInternalHomOfUniverses.{uC, vC, u, w} J R)).obj (op K)

/-- The functor T^n. Source: Stacks 0A94
(blueprint: lem-per-rhom-local-cohomological-bound). -/
abbrev T (K : D.{uC, vC, u, w} J R) (n : ℤ) := RH.{uC, vC, u, w} J R K ⋙
  DerivedCategory.homologyFunctor (Mod.{uC, vC, u} J R) n

/-- Exact slice restriction, with its existing derived localization. Source: Stacks 03DJ
(blueprint: lem-per-rhom-local-cohomological-bound). -/
def res (U : C) : D.{uC, vC, u, w} J R ⥤
    DerivedCategory.{wSlice} (SheafOfModules.{max uC vC u} ((rings.{uC, vC, u} J R).over U)) :=
  haveI := (SheafOfModules.overFunctor_exact_ofUniverses.{uC, vC, max uC vC u} (rings.{uC, vC, u} J
    R) U).1
  haveI := (SheafOfModules.overFunctor_exact_ofUniverses.{uC, vC, max uC vC u} (rings.{uC, vC, u} J
    R) U).2
  (SheafOfModules.overFunctor.{max uC vC u} (rings.{uC, vC, u} J R) U).mapDerivedCategory

/-- Multiplication by a local section on slice restriction, using the existing
sectionwise multiplication construction at the full coefficient universe.
Source: Stacks 03DI and 0997 (blueprint: lem-per-rhom-local-cohomological-bound).
This is the general-universe form of `localSectionMultiplicationNatTrans`. -/
def sectionMultiplication (U : C) (a : R.obj.obj (op U)) :
    SheafOfModules.overFunctor.{max uC vC u} (rings.{uC, vC, u} J R) U ⟶
      SheafOfModules.overFunctor.{max uC vC u} (rings.{uC, vC, u} J R) U where
  app M := ⟨PresheafOfModules.sectionsSMul
    (S := (Over.forget U).op ⋙ R.obj)
    ((SheafOfModules.overFunctor.{max uC vC u} (rings.{uC, vC, u} J R) U).obj M).val
    (PresheafOfModules.overSections (R := R.obj) U a)⟩
  naturality {_M _N} f := congrArg SheafOfModules.Hom.mk
    (PresheafOfModules.sectionsSMul_naturality
      ((SheafOfModules.overFunctor.{max uC vC u} (rings.{uC, vC, u} J R) U).map f).val
      (PresheafOfModules.overSections (R := R.obj) U a))

/-- The canonical multiplication endomorphism after localization at quasi-isomorphisms.
Source: Stacks 03DI and 0997 (blueprint: lem-per-rhom-local-cohomological-bound).
Termwise multiplication is descended with the exact restriction's actual localization
factorization; no derived endomorphism or comparison is selected arbitrarily. -/
def sectionDerivedMultiplication (U : C) (a : R.obj.obj (op U)) :
    res.{uC, vC, u, w, wSlice} J R U ⟶ res.{uC, vC, u, w, wSlice} J R U :=
  haveI := (SheafOfModules.overFunctor_exact_ofUniverses.{uC, vC, max uC vC u} (rings.{uC, vC, u} J
    R) U).1
  haveI := (SheafOfModules.overFunctor_exact_ofUniverses.{uC, vC, max uC vC u} (rings.{uC, vC, u} J
    R) U).2
  haveI : Localization.Lifting DerivedCategory.Q
      (HomologicalComplex.quasiIso _ (ComplexShape.up ℤ))
      ((SheafOfModules.overFunctor.{max uC vC u} (rings.{uC, vC, u} J R) U).mapHomologicalComplex
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Q) (res.{uC, vC, u, w, wSlice} J R U) :=
    ⟨(SheafOfModules.overFunctor.{max uC vC u} (rings.{uC, vC, u} J R) U).mapDerivedCategoryFactors⟩
  Localization.liftNatTrans DerivedCategory.Q
    (HomologicalComplex.quasiIso _ (ComplexShape.up ℤ)) _ _ _ _
    (Functor.whiskerRight (NatTrans.mapHomologicalComplex
      (sectionMultiplication.{uC, vC, u} J R U a) (ComplexShape.up ℤ)) DerivedCategory.Q)

/-- Further derived restriction, induced by the existing exact overMap. Source: Stacks 04IX
(blueprint: lem-per-rhom-local-cohomological-bound). -/
def further {U V : C} (f : V ⟶ U) :
    DerivedCategory.{wSlice} (SheafOfModules.{max uC vC u} ((rings.{uC, vC, u} J R).over U)) ⥤
      DerivedCategory.{wSlice} (SheafOfModules.{max uC vC u} ((rings.{uC, vC, u} J R).over V)) :=
  haveI := (SheafOfModules.overMap_exact_ofUniverses.{uC, vC, max uC vC u} (rings.{uC, vC, u} J R)
    f).1
  haveI := (SheafOfModules.overMap_exact_ofUniverses.{uC, vC, max uC vC u} (rings.{uC, vC, u} J R)
    f).2
  (SheafOfModules.overMap.{max uC vC u} (rings.{uC, vC, u} J R) f).mapDerivedCategory

/-- The canonical composition comparison, induced from overFunctorMap. Source: Stacks 04IX
(blueprint: lem-per-rhom-local-cohomological-bound). -/
def resComp {U V : C} (f : V ⟶ U) : res.{uC, vC, u, w, wSlice} J R U ⋙ further.{uC, vC, u, wSlice} J
  R f ≅ res.{uC, vC, u, w, wSlice} J R V :=
  haveI := (SheafOfModules.overFunctor_exact_ofUniverses.{uC, vC, max uC vC u} (rings.{uC, vC, u} J
    R) U).1
  haveI := (SheafOfModules.overFunctor_exact_ofUniverses.{uC, vC, max uC vC u} (rings.{uC, vC, u} J
    R) U).2
  haveI := (SheafOfModules.overFunctor_exact_ofUniverses.{uC, vC, max uC vC u} (rings.{uC, vC, u} J
    R) V).1
  haveI := (SheafOfModules.overFunctor_exact_ofUniverses.{uC, vC, max uC vC u} (rings.{uC, vC, u} J
    R) V).2
  haveI := (SheafOfModules.overMap_exact_ofUniverses.{uC, vC, max uC vC u} (rings.{uC, vC, u} J R)
    f).1
  haveI := (SheafOfModules.overMap_exact_ofUniverses.{uC, vC, max uC vC u} (rings.{uC, vC, u} J R)
    f).2
  (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryNatIso (SheafOfModules.overFunctorMap (rings.{uC, vC, u} J R) f)

/-- Local Hom restriction, including the canonical composition comparisons. Source: Stacks 0A94
(blueprint: lem-per-rhom-local-cohomological-bound). -/
def restrictHom {K M : D.{uC, vC, u, w} J R} {U V : C} (f : V ⟶ U)
    (a : (res.{uC, vC, u, w, wSlice} J R U).obj K ⟶ (res.{uC, vC, u, w, wSlice} J R U).obj M) :
    (res.{uC, vC, u, w, wSlice} J R V).obj K ⟶ (res.{uC, vC, u, w, wSlice} J R V).obj M :=
  (resComp.{uC, vC, u, w, wSlice} J R f).inv.app K ≫ (further.{uC, vC, u, wSlice} J R f).map a ≫
    (resComp.{uC, vC, u, w, wSlice} J R f).hom.app M

/-- Termwise restriction of representatives. Source: Stacks 0A94
(blueprint: lem-per-rhom-local-cohomological-bound). -/
abbrev complexRes (U : C) :=
  (SheafOfModules.overFunctor.{max uC vC u} (rings.{uC, vC, u} J R) U).mapHomologicalComplex
    (ComplexShape.up ℤ)

/-- The canonical termwise-to-derived comparison. Source: Stacks 015F
(blueprint: lem-per-rhom-local-cohomological-bound). -/
def resQ (U : C) (P : CochainComplex (Mod.{uC, vC, u} J R) ℤ) :
    (res.{uC, vC, u, w, wSlice} J R U).obj (DerivedCategory.Q.obj P) ≅
      DerivedCategory.Q.obj ((complexRes.{uC, vC, u} J R U).obj P) :=
  haveI := (SheafOfModules.overFunctor_exact_ofUniverses.{uC, vC, max uC vC u} (rings.{uC, vC, u} J
    R) U).1
  haveI := (SheafOfModules.overFunctor_exact_ofUniverses.{uC, vC, max uC vC u} (rings.{uC, vC, u} J
    R) U).2
  (SheafOfModules.overFunctor.{max uC vC u} (rings.{uC, vC, u} J R) U).mapDerivedCategoryFactors.app
    P

/-- The sheafification functor of the recorded module presheaves. Source: Stacks 03CY
(blueprint: lem-per-rhom-local-cohomological-bound). -/
abbrev sh := PresheafOfModules.sheafification.{max uC vC u} (𝟙 (rings.{uC, vC, u} J R).obj)

/-- The normalized boundary transported from a coherent shift sequence. Source: Stacks 0149
(blueprint: lem-per-rhom-local-cohomological-bound). -/
def boundary (K : D.{uC, vC, u, w} J R) (S : (T.{uC, vC, u, w} J R K 0).ShiftSequence ℤ)
    (τ : ∀ n : ℤ, S.sequence n ≅ T.{uC, vC, u, w} J R K n) (A : Triangle (D.{uC, vC, u, w} J R)) (n
      : ℤ) :
    (T.{uC, vC, u, w} J R K n).obj A.obj₃ ⟶ (T.{uC, vC, u, w} J R K (n + 1)).obj A.obj₁ :=
  (τ n).inv.app A.obj₃ ≫ (S.sequence n).map A.mor₃ ≫
    (S.shiftIso 1 n (n + 1) (add_comm 1 n)).hom.app A.obj₁ ≫
    (τ (n + 1)).hom.app A.obj₁

/-- The map of Hom complexes induced by the fixed K-injective augmentation.
Source: Stacks 0A95 (blueprint: lem-per-rhom-local-cohomological-bound). -/
def homAugmentation (P I : CochainComplex (Mod.{uC, vC, u} J R) ℤ) :
    homComplex.{uC, vC, max uC vC u, max uC vC u} (R := R) P I ⟶ homComplex.{uC, vC, max uC vC u,
      max uC vC u} (R := R) P
      ((WeilConjectures.coefficientHomResolution.{u, uC, vC} J R).obj I) :=
  haveI :=
    (SheafOfModules.grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses.{uC, vC, u}
      J R).1
  ((homComplexFunctor.{uC, vC, max uC vC u, max uC vC u} (R := R)).obj (op P)).map
    ((CochainComplex.toKInjectiveResolution.{max uC vC u} _).app I)

/-- A cocycle's cohomology class transported through a specified representative comparison.
Source: Stacks 0A94 (blueprint: lem-per-rhom-local-cohomological-bound). -/
def cycleClass (P I : CochainComplex (Mod.{uC, vC, u} J R) ℤ)
    (h : (RH.{uC, vC, u, w} J R (DerivedCategory.Q.obj P)).obj (DerivedCategory.Q.obj I) ≅
      DerivedCategory.Q.obj (homComplex.{uC, vC, max uC vC u, max uC vC u} (R := R) P I)) (n : ℤ) (U
        : C)
    (z : ((homComplex.{uC, vC, max uC vC u, max uC vC u} (R := R) P I).cycles n).val.obj (op U)) :
    ((T.{uC, vC, u, w} J R (DerivedCategory.Q.obj P) n).obj (DerivedCategory.Q.obj I)).val.obj (op
      U) :=
  (((DerivedCategory.homologyFunctorFactors (Mod.{uC, vC, u} J R) n).inv.app
      (homComplex.{uC, vC, max uC vC u, max uC vC u} (R := R) P I) ≫
    (DerivedCategory.homologyFunctor (Mod.{uC, vC, u} J R) n).map h.inv).val.app (op U))
    (((homComplex.{uC, vC, max uC vC u, max uC vC u} (R := R) P I).homologyπ n).val.app (op U) z)

/-- Localization of a local degree-n chain map, with the termwise and shift comparisons.
Source: Stacks 0A94 and 015F (blueprint: lem-per-rhom-local-cohomological-bound). -/
def localizedCocycle (P I : CochainComplex (Mod.{uC, vC, u} J R) ℤ) (n : ℤ) (U : C)
    (a : (complexRes.{uC, vC, u} J R U).obj P ⟶ (complexRes.{uC, vC, u} J R U).obj (I⟦n⟧)) :
    (res.{uC, vC, u, w, wSlice} J R U).obj (DerivedCategory.Q.obj P) ⟶
      (res.{uC, vC, u, w, wSlice} J R U).obj ((DerivedCategory.Q.obj I)⟦n⟧) :=
  (resQ.{uC, vC, u, w, wSlice} J R U P).hom ≫ DerivedCategory.Q.map a ≫ (resQ.{uC, vC, u, w, wSlice}
    J R U (I⟦n⟧)).inv ≫
    (res.{uC, vC, u, w, wSlice} J R U).map ((DerivedCategory.Q.commShiftIso n).hom.app I)

end CategoryTheory.LocalRHom
