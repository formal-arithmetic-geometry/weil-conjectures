# CategoryTheory.CechLocalizationUnit model definitions

## Reason

The two remaining strict-family assembly lemmas must refer to the assigned theorem's
model types. Move those types to a separate publicly imported module to avoid an import
cycle. Every original declaration, signature, universe, attribute and body is preserved
verbatim. The assigned theorem's signature is also verbatim. Two new structures describe
separate input and abstract comparison interfaces; neither contains a construction by
arbitrary choice or a proof hole. The unchanged point/column/total definitions still
normalize the actual adjunction unit.

## Old

The supporting declarations in Sheaf.CategoryTheory.CechLocalizationUnitTotalization:

```lean
/-- Finite-diagonal totalization followed by extension by zero in negative degrees.
Source: Stacks 015J (blueprint: lem-sfb-cech-localization-unit-totalization). -/
def total (A : Type u) [Category.{v} A] [Abelian A] [HasFiniteCoproducts A] :
    CosimplicialObject (CochainComplex A ℕ) ⥤ CochainComplex A ℤ :=
  AlgebraicTopology.alternatingCofaceMapComplex (CochainComplex A ℕ) ⋙
    HomologicalComplex₂.totalFunctor A (.up ℕ) (.up ℕ) (.up ℕ) ⋙
      ComplexShape.embeddingUpNat.extendFunctor A

/-- Apply an exact natural transformation to the ordinary unbounded derived categories.
Source: Stacks 015F (blueprint: lem-sfb-cech-localization-unit-totalization). -/
def derivedNatTrans {A : Type uA} {B : Type uB} [Category.{vA} A] [Category.{vB} B]
    [Abelian A] [Abelian B] [HasDerivedCategory.{wA} A] [HasDerivedCategory.{wB} B]
    {F G : A ⥤ B} [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] (a : F ⟶ G) :
    F.mapDerivedCategory ⟶ G.mapDerivedCategory :=
  Localization.liftNatTrans DerivedCategory.Q
    (HomologicalComplex.quasiIso A (.up ℤ))
    (F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (G.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    F.mapDerivedCategory G.mapDerivedCategory
    (Functor.whiskerRight (NatTrans.mapHomologicalComplex a (.up ℤ)) DerivedCategory.Q)

/-- Nonnegative complexes viewed in the ordinary unbounded derived category.
Source: Stacks 015J (blueprint: lem-sfb-cech-localization-unit-totalization). -/
def QNN (A : Type u) [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A] :
    CochainComplex A ℕ ⥤ DerivedCategory A :=
  ComplexShape.embeddingUpNat.extendFunctor A ⋙ DerivedCategory.Q

/-- A nonnegative augmented cosimplicial model, with its normalized total augmentation.
The equation fixes the total map on every nonnegative degree, including degree zero.
Source: Stacks 03FC and 015J (blueprint: lem-sfb-cech-localization-unit-totalization). -/
structure AugmentedModel (A : Type u) [Category.{v} A] [Abelian A]
    [HasFiniteCoproducts A] (P : Type uP) [Category.{vP} P] where
  point : P ⥤ CochainComplex A ℕ
  columns : P ⥤ CosimplicialObject (CochainComplex A ℕ)
  augmentation : point ⋙ Functor.const SimplexCategory ⟶ columns
  totalAugmentation : point ⋙ ComplexShape.embeddingUpNat.extendFunctor A ⟶ columns ⋙ total A
  total_formula : ∀ (p : P) (q : ℕ),
    ((point.obj p).extendXIso ComplexShape.embeddingUpNat (i := q) rfl).inv ≫
        (totalAugmentation.app p).f (q : ℤ) ≫
        ((HomologicalComplex₂.total
          ((AlgebraicTopology.alternatingCofaceMapComplex (CochainComplex A ℕ)).obj
            (columns.obj p)) (.up ℕ)).extendXIso
              ComplexShape.embeddingUpNat (i := q) rfl).hom =
      ((augmentation.app p).app (SimplexCategory.mk 0)).f q ≫
        HomologicalComplex₂.ιTotal
          ((AlgebraicTopology.alternatingCofaceMapComplex (CochainComplex A ℕ)).obj
            (columns.obj p)) (.up ℕ) 0 q q (by simp [ComplexShape.π])
  total_quasiIso : ∀ p : P, QuasiIso (totalAugmentation.app p)

/-- Exact descent of the specified unit, including the identity-functor normalization.
Source: Stacks 015F (blueprint: lem-sfb-cech-localization-unit-totalization). -/
def exactUnit {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
    {H : A ⥤ A} [H.Additive] [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    (η : 𝟭 A ⟶ H) : 𝟭 (DerivedCategory A) ⟶ H.mapDerivedCategory :=
  (Functor.mapDerivedCategoryIdIso A).inv ≫ derivedNatTrans η

/-- The recorded module category, after forgetting a commutative ring to a ring.
Source: Stacks 03CX (blueprint: lem-sfb-cech-localization-unit-totalization). -/
abbrev Modules {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{u}) : Type (u + 1) :=
  ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)

section Comparison

variable {CX : Type u} [SmallCategory CX] {JX : GrothendieckTopology CX}
  (RX : Sheaf JX CommRingCat.{u})
  (D : CoherentCechImageModel ((sheafCompose JX (forget₂ CommRingCat RingCat)).obj RX))

variable {AV : Type (u + 1)} [Category.{u} AV] [Abelian AV]
  {AY : Type (u + 1)} [Category.{u} AY] [Abelian AY]
  {AB : Type (u + 1)} [Category.{u} AB] [Abelian AB]
  [HasFiniteCoproducts AB]
  [HasDerivedCategory.{u + 1} (Modules RX)] [HasDerivedCategory.{u + 1} AV]
  [HasDerivedCategory.{u + 1} AY] [HasDerivedCategory.{u + 1} AB]
  [Abelian.HasKInjectiveResolutions (Modules RX)] [Abelian.HasKInjectiveResolutions AV]
  [Abelian.HasKInjectiveResolutions AY]
  (F : (Modules RX) ⥤ AV) [F.Additive] (G : AV ⥤ AY) [G.Additive]
  (T : AY ⥤ AB) [T.Additive] [PreservesFiniteLimits T] [PreservesFiniteColimits T]
  (H : AV ⥤ AV) [H.Additive] [PreservesFiniteLimits H] [PreservesFiniteColimits H]
  (η : 𝟭 AV ⟶ H)
  {P : Type uP} [Category.{vP} P]
  (V : Pᵒᵖ ⥤ Sheaf JX (Type u)) (N : P ⥤ (Modules RX))

/-- The power sheaf defining the n-th Cech slice.
Source: Stacks 03FC (blueprint: lem-sfb-cech-localization-unit-totalization). -/
def power (p : P) (n : SimplexCategory) : Sheaf JX (Type u) :=
  (sheafCoverNerve (V.obj (op p))).obj (op n)

/-- The module endofunctor j_n* j_n^* for the n-th slice.
Source: Stacks 03FC and 04IE (blueprint: lem-sfb-cech-localization-unit-totalization). -/
abbrev slice (p : P) (n : SimplexCategory) : (Modules RX) ⥤ (Modules RX) :=
  D.image.obj (op (power V p n))

/-- Additivity transported from the actual localization composite.
Source: Stacks 04IE (blueprint: lem-sfb-cech-localization-unit-totalization). -/
instance image_additive (A : Sheaf JX (Type u)) : (D.image.obj (op A)).Additive :=
  letI := (D.adj A).isLeftAdjoint
  letI : HasBinaryBiproducts (Modules RX) := Abelian.hasBinaryBiproducts
  letI := preservesBinaryBiproducts_of_preservesBinaryCoproducts
    (elementModulePullback ((sheafCompose JX (forget₂ CommRingCat RingCat)).obj RX) A)
  letI : (elementModulePullback
      ((sheafCompose JX (forget₂ CommRingCat RingCat)).obj RX) A).Additive :=
    Functor.additive_of_preservesBinaryBiproducts _
  Functor.additive_of_iso (D.imageIso A).symm

/-- The derived Cech column, canonically identified with R(f v_n)_*(v_n^*N[0]).
Deriving j_n* j_n^* is Rj_n* j_n^*, since j_n^* is exact and preserves injectives;
the latter follows from its exact left adjoint j_n!. The normalized composition
comparison then gives R(f v_n)_*.
Source: Stacks 03FC and 0D6E (blueprint: lem-sfb-cech-localization-unit-totalization). -/
def baseColumn (p : P) (n : SimplexCategory) : DerivedCategory AV :=
  F.rightDerivedFunctor.obj
    ((slice RX D V p n).rightDerivedFunctor.obj ((DerivedCategory.singleFunctor (Modules RX) 0).obj
      (N.obj p)))

/-- Every Cech operator on the canonical derived columns, including degeneracies.
Source: Stacks 03FC (blueprint: lem-sfb-cech-localization-unit-totalization). -/
def columnOperator (p : P) {n m : SimplexCategory} (θ : n ⟶ m) :
    baseColumn RX D F V N p n ⟶ baseColumn RX D F V N p m :=
  F.rightDerivedFunctor.map ((Functor.rightDerivedFunctorNatTrans
    (D.image.map (((sheafCoverNerve (V.obj (op p))).map θ.op).op))).app
      ((DerivedCategory.singleFunctor (Modules RX) 0).obj (N.obj p)))

/-- Simultaneous change of coefficients and refinement of the covering sheaf.
The direction P^op -> covers makes a refinement V_q -> V_p accompany N_p -> N_q.
Source: Stacks 03FC (blueprint: lem-sfb-cech-localization-unit-totalization). -/
def columnChange {p q : P} (a : p ⟶ q) (n : SimplexCategory) :
    baseColumn RX D F V N p n ⟶ baseColumn RX D F V N q n :=
  F.rightDerivedFunctor.map
    ((Functor.rightDerivedFunctorNatTrans
      (D.image.map (((Arrow.mapCechNerve
        (Arrow.homMk (V.map a.op) (𝟙 _) (terminal.hom_ext _ _) :
          Arrow.mk (terminal.from (V.obj (op q))) ⟶
            Arrow.mk (terminal.from (V.obj (op p))))).app (op n)).op))).app
        ((DerivedCategory.singleFunctor (Modules RX) 0).obj (N.obj p)) ≫
      (slice RX D V q n).rightDerivedFunctor.map
        ((DerivedCategory.singleFunctor (Modules RX) 0).map (N.map a)))

/-- The actual derived restriction-of-sections augmentation in every Cech degree.
Source: Stacks 03FC and 015F (blueprint: lem-sfb-cech-localization-unit-totalization). -/
def columnAugmentation (p : P) (n : SimplexCategory) :
    F.rightDerivedFunctor.obj ((DerivedCategory.singleFunctor (Modules RX) 0).obj (N.obj p)) ⟶
      baseColumn RX D F V N p n :=
  F.rightDerivedFunctor.map (((Functor.mapDerivedCategoryIdIso _).inv ≫
      (Functor.rightDerivedFunctorIsoMapDerivedCategory (𝟭 _)).inv ≫
        Functor.rightDerivedFunctorNatTrans (D.augmentation (power V p n))).app
          ((DerivedCategory.singleFunctor (Modules RX) 0).obj (N.obj p)))

/-- Complete compatible models for the two augmented Cech comparisons.
All resolutions, isomorphisms and lifts are conclusions of the theorem. Column maps
and augmentations are fixed by the displayed canonical derived maps, not freely supplied.
Source: Stacks 03FC, 015J, 015F (blueprint: lem-sfb-cech-localization-unit-totalization). -/
structure Comparison where
  source : AugmentedModel AB P
  target : AugmentedModel AB P
  sourcePoint :
    N ⋙ DerivedCategory.singleFunctor (Modules RX) 0 ⋙ F.rightDerivedFunctor ⋙
      G.rightDerivedFunctor ⋙
      T.mapDerivedCategory ≅ source.point ⋙ QNN AB
  targetPoint :
    N ⋙ DerivedCategory.singleFunctor (Modules RX) 0 ⋙ F.rightDerivedFunctor ⋙
      H.mapDerivedCategory ⋙ G.rightDerivedFunctor ⋙
      T.mapDerivedCategory ≅ target.point ⋙ QNN AB
  sourceColumns : ∀ (p : P) (n : SimplexCategory),
    T.mapDerivedCategory.obj (G.rightDerivedFunctor.obj (baseColumn RX D F V N p n)) ≅
      (QNN AB).obj ((source.columns.obj p).obj n)
  targetColumns : ∀ (p : P) (n : SimplexCategory),
    T.mapDerivedCategory.obj (G.rightDerivedFunctor.obj
      (H.mapDerivedCategory.obj (baseColumn RX D F V N p n))) ≅
      (QNN AB).obj ((target.columns.obj p).obj n)
  source_operator : ∀ (p : P) (n m : SimplexCategory) (θ : n ⟶ m),
    T.mapDerivedCategory.map (G.rightDerivedFunctor.map (columnOperator RX D F V N p θ)) ≫
      (sourceColumns p m).hom = (sourceColumns p n).hom ≫
        (QNN AB).map ((source.columns.obj p).map θ)
  target_operator : ∀ (p : P) (n m : SimplexCategory) (θ : n ⟶ m),
    T.mapDerivedCategory.map (G.rightDerivedFunctor.map
      (H.mapDerivedCategory.map (columnOperator RX D F V N p θ))) ≫
      (targetColumns p m).hom = (targetColumns p n).hom ≫
        (QNN AB).map ((target.columns.obj p).map θ)
  source_natural : ∀ (p q : P) (b : p ⟶ q) (n : SimplexCategory),
    T.mapDerivedCategory.map (G.rightDerivedFunctor.map (columnChange RX D F V N b n)) ≫
      (sourceColumns q n).hom = (sourceColumns p n).hom ≫
        (QNN AB).map ((source.columns.map b).app n)
  target_natural : ∀ (p q : P) (b : p ⟶ q) (n : SimplexCategory),
    T.mapDerivedCategory.map (G.rightDerivedFunctor.map
      (H.mapDerivedCategory.map (columnChange RX D F V N b n))) ≫
      (targetColumns q n).hom = (targetColumns p n).hom ≫
        (QNN AB).map ((target.columns.map b).app n)
  source_augmentation : ∀ (p : P) (n : SimplexCategory),
    sourcePoint.hom.app p ≫ (QNN AB).map ((source.augmentation.app p).app n) =
      T.mapDerivedCategory.map (G.rightDerivedFunctor.map
        (columnAugmentation RX D F V N p n)) ≫ (sourceColumns p n).hom
  target_augmentation : ∀ (p : P) (n : SimplexCategory),
    targetPoint.hom.app p ≫ (QNN AB).map ((target.augmentation.app p).app n) =
      T.mapDerivedCategory.map (G.rightDerivedFunctor.map
        (H.mapDerivedCategory.map (columnAugmentation RX D F V N p n))) ≫
          (targetColumns p n).hom
  unitColumns : source.columns ⟶ target.columns
  unit_columns : ∀ (p : P) (n : SimplexCategory),
    (sourceColumns p n).hom ≫ (QNN AB).map ((unitColumns.app p).app n) =
      T.mapDerivedCategory.map (G.rightDerivedFunctor.map
        ((exactUnit η).app (baseColumn RX D F V N p n))) ≫ (targetColumns p n).hom
  sourceComparison :
    N ⋙ DerivedCategory.singleFunctor (Modules RX) 0 ⋙ F.rightDerivedFunctor ⋙
      G.rightDerivedFunctor ⋙
      T.mapDerivedCategory ≅ source.columns ⋙ total AB ⋙ DerivedCategory.Q
  targetComparison :
    N ⋙ DerivedCategory.singleFunctor (Modules RX) 0 ⋙ F.rightDerivedFunctor ⋙
      H.mapDerivedCategory ⋙ G.rightDerivedFunctor ⋙
      T.mapDerivedCategory ≅ target.columns ⋙ total AB ⋙ DerivedCategory.Q
  source_normalization : ∀ p : P,
    sourcePoint.hom.app p ≫ DerivedCategory.Q.map (source.totalAugmentation.app p) =
      sourceComparison.hom.app p
  target_normalization : ∀ p : P,
    targetPoint.hom.app p ≫ DerivedCategory.Q.map (target.totalAugmentation.app p) =
      targetComparison.hom.app p
  unit_total : ∀ p : P,
    T.mapDerivedCategory.map (G.rightDerivedFunctor.map
      ((exactUnit η).app (F.rightDerivedFunctor.obj
        ((DerivedCategory.singleFunctor (Modules RX) 0).obj (N.obj p))))) ≫
      targetComparison.hom.app p = sourceComparison.hom.app p ≫
        DerivedCategory.Q.map ((total AB).map (unitColumns.app p))

/-- Applying a specified exact restriction to the whole comparison square.
The arrow inside S.map is the original derived unit, as in Comparison.unit_total.
Source: Stacks 03DJ and 015F (blueprint: lem-sfb-cech-localization-unit-totalization). -/
def Comparison.Restricts
    (c : Comparison RX D F G T H η V N)
    {E : Type v} [Category.{w} E] (S : DerivedCategory AB ⥤ E) : Prop :=
  ∀ p : P,
    S.map (T.mapDerivedCategory.map (G.rightDerivedFunctor.map
      ((exactUnit η).app (F.rightDerivedFunctor.obj
        ((DerivedCategory.singleFunctor (Modules RX) 0).obj (N.obj p))))) ≫
          c.targetComparison.hom.app p) =
      S.map (c.sourceComparison.hom.app p ≫
        DerivedCategory.Q.map ((total AB).map (c.unitColumns.app p)))

end Comparison



/-- Exact restriction of the ordinary derived category to the genuine ringed slice site.
The localization model on the slice is the standard one; the underlying functor is
exactly the recorded overFunctor, with its explicit site universes.
Source: Stacks 03DJ and 04IX (blueprint: lem-sfb-cech-localization-unit-totalization). -/
def restrictDerived {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{u}) [HasDerivedCategory.{u + 1} (Modules R)] (U : C) :
    letI : HasDerivedCategory.{u + 1}
      (SheafOfModules.{u} (((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).over U)) :=
      HasDerivedCategory.standard _
    DerivedCategory (Modules R) ⥤
      DerivedCategory
        (SheafOfModules.{u} (((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).over U)) :=
  letI : HasDerivedCategory.{u + 1}
      (SheafOfModules.{u} (((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).over U)) :=
    HasDerivedCategory.standard _
  (SheafOfModules.localizedSystemRestriction.{u, u, u} R U).mapDerivedCategory

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits
```

## New

The same declarations now live in Sheaf.CategoryTheory.CechLocalizationUnitModels and
are publicly re-exported by the original module. The new module, including the two
additional family interfaces, is:

```lean
/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N6
-/
module

public import Sheaf.CategoryTheory.RingedToposMorphism
public import Sheaf.CategoryTheory.LocalizedModuleExactForSystems
public import Sheaf.CategoryTheory.SiteCoveringAxioms
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions
public import Sheaf.CategoryTheory.CoherentCechImageModel
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
public import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
public import WeilConjectures.Mathlib.Algebra.Homology.TotalComplex
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory
public import WeilConjectures.CategoryTheory.DoubleComplexTotal

/-! # Data for augmented Cech localization comparisons

Source: main-20261015, direct-images.proof.md (3); Stacks Tags 03FC, 015J and 015F.
(blueprint: lem-sfb-cech-localization-unit-totalization).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v w uP vP uA vA wA uB vB wB

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory.CechLocalizationUnit

/-- Finite-diagonal totalization followed by extension by zero in negative degrees.
Source: Stacks 015J (blueprint: lem-sfb-cech-localization-unit-totalization). -/
def total (A : Type u) [Category.{v} A] [Abelian A] [HasFiniteCoproducts A] :
    CosimplicialObject (CochainComplex A ℕ) ⥤ CochainComplex A ℤ :=
  AlgebraicTopology.alternatingCofaceMapComplex (CochainComplex A ℕ) ⋙
    HomologicalComplex₂.totalFunctor A (.up ℕ) (.up ℕ) (.up ℕ) ⋙
      ComplexShape.embeddingUpNat.extendFunctor A

/-- Apply an exact natural transformation to the ordinary unbounded derived categories.
Source: Stacks 015F (blueprint: lem-sfb-cech-localization-unit-totalization). -/
def derivedNatTrans {A : Type uA} {B : Type uB} [Category.{vA} A] [Category.{vB} B]
    [Abelian A] [Abelian B] [HasDerivedCategory.{wA} A] [HasDerivedCategory.{wB} B]
    {F G : A ⥤ B} [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] (a : F ⟶ G) :
    F.mapDerivedCategory ⟶ G.mapDerivedCategory :=
  Localization.liftNatTrans DerivedCategory.Q
    (HomologicalComplex.quasiIso A (.up ℤ))
    (F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (G.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    F.mapDerivedCategory G.mapDerivedCategory
    (Functor.whiskerRight (NatTrans.mapHomologicalComplex a (.up ℤ)) DerivedCategory.Q)

/-- Nonnegative complexes viewed in the ordinary unbounded derived category.
Source: Stacks 015J (blueprint: lem-sfb-cech-localization-unit-totalization). -/
def QNN (A : Type u) [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A] :
    CochainComplex A ℕ ⥤ DerivedCategory A :=
  ComplexShape.embeddingUpNat.extendFunctor A ⋙ DerivedCategory.Q

/-- A nonnegative augmented cosimplicial model, with its normalized total augmentation.
The equation fixes the total map on every nonnegative degree, including degree zero.
Source: Stacks 03FC and 015J (blueprint: lem-sfb-cech-localization-unit-totalization). -/
structure AugmentedModel (A : Type u) [Category.{v} A] [Abelian A]
    [HasFiniteCoproducts A] (P : Type uP) [Category.{vP} P] where
  point : P ⥤ CochainComplex A ℕ
  columns : P ⥤ CosimplicialObject (CochainComplex A ℕ)
  augmentation : point ⋙ Functor.const SimplexCategory ⟶ columns
  totalAugmentation : point ⋙ ComplexShape.embeddingUpNat.extendFunctor A ⟶ columns ⋙ total A
  total_formula : ∀ (p : P) (q : ℕ),
    ((point.obj p).extendXIso ComplexShape.embeddingUpNat (i := q) rfl).inv ≫
        (totalAugmentation.app p).f (q : ℤ) ≫
        ((HomologicalComplex₂.total
          ((AlgebraicTopology.alternatingCofaceMapComplex (CochainComplex A ℕ)).obj
            (columns.obj p)) (.up ℕ)).extendXIso
              ComplexShape.embeddingUpNat (i := q) rfl).hom =
      ((augmentation.app p).app (SimplexCategory.mk 0)).f q ≫
        HomologicalComplex₂.ιTotal
          ((AlgebraicTopology.alternatingCofaceMapComplex (CochainComplex A ℕ)).obj
            (columns.obj p)) (.up ℕ) 0 q q (by simp [ComplexShape.π])
  total_quasiIso : ∀ p : P, QuasiIso (totalAugmentation.app p)

/-- Exact descent of the specified unit, including the identity-functor normalization.
Source: Stacks 015F (blueprint: lem-sfb-cech-localization-unit-totalization). -/
def exactUnit {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
    {H : A ⥤ A} [H.Additive] [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    (η : 𝟭 A ⟶ H) : 𝟭 (DerivedCategory A) ⟶ H.mapDerivedCategory :=
  (Functor.mapDerivedCategoryIdIso A).inv ≫ derivedNatTrans η

/-- The recorded module category, after forgetting a commutative ring to a ring.
Source: Stacks 03CX (blueprint: lem-sfb-cech-localization-unit-totalization). -/
abbrev Modules {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{u}) : Type (u + 1) :=
  ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)

section Comparison

variable {CX : Type u} [SmallCategory CX] {JX : GrothendieckTopology CX}
  (RX : Sheaf JX CommRingCat.{u})
  (D : CoherentCechImageModel ((sheafCompose JX (forget₂ CommRingCat RingCat)).obj RX))

variable {AV : Type (u + 1)} [Category.{u} AV] [Abelian AV]
  {AY : Type (u + 1)} [Category.{u} AY] [Abelian AY]
  {AB : Type (u + 1)} [Category.{u} AB] [Abelian AB]
  [HasFiniteCoproducts AB]
  [HasDerivedCategory.{u + 1} (Modules RX)] [HasDerivedCategory.{u + 1} AV]
  [HasDerivedCategory.{u + 1} AY] [HasDerivedCategory.{u + 1} AB]
  [Abelian.HasKInjectiveResolutions (Modules RX)] [Abelian.HasKInjectiveResolutions AV]
  [Abelian.HasKInjectiveResolutions AY]
  (F : (Modules RX) ⥤ AV) [F.Additive] (G : AV ⥤ AY) [G.Additive]
  (T : AY ⥤ AB) [T.Additive] [PreservesFiniteLimits T] [PreservesFiniteColimits T]
  (H : AV ⥤ AV) [H.Additive] [PreservesFiniteLimits H] [PreservesFiniteColimits H]
  (η : 𝟭 AV ⟶ H)
  {P : Type uP} [Category.{vP} P]
  (V : Pᵒᵖ ⥤ Sheaf JX (Type u)) (N : P ⥤ (Modules RX))

/-- The power sheaf defining the n-th Cech slice.
Source: Stacks 03FC (blueprint: lem-sfb-cech-localization-unit-totalization). -/
def power (p : P) (n : SimplexCategory) : Sheaf JX (Type u) :=
  (sheafCoverNerve (V.obj (op p))).obj (op n)

/-- The module endofunctor j_n* j_n^* for the n-th slice.
Source: Stacks 03FC and 04IE (blueprint: lem-sfb-cech-localization-unit-totalization). -/
abbrev slice (p : P) (n : SimplexCategory) : (Modules RX) ⥤ (Modules RX) :=
  D.image.obj (op (power V p n))

/-- Additivity transported from the actual localization composite.
Source: Stacks 04IE (blueprint: lem-sfb-cech-localization-unit-totalization). -/
instance image_additive (A : Sheaf JX (Type u)) : (D.image.obj (op A)).Additive :=
  letI := (D.adj A).isLeftAdjoint
  letI : HasBinaryBiproducts (Modules RX) := Abelian.hasBinaryBiproducts
  letI := preservesBinaryBiproducts_of_preservesBinaryCoproducts
    (elementModulePullback ((sheafCompose JX (forget₂ CommRingCat RingCat)).obj RX) A)
  letI : (elementModulePullback
      ((sheafCompose JX (forget₂ CommRingCat RingCat)).obj RX) A).Additive :=
    Functor.additive_of_preservesBinaryBiproducts _
  Functor.additive_of_iso (D.imageIso A).symm

/-- The derived Cech column, canonically identified with R(f v_n)_*(v_n^*N[0]).
Deriving j_n* j_n^* is Rj_n* j_n^*, since j_n^* is exact and preserves injectives;
the latter follows from its exact left adjoint j_n!. The normalized composition
comparison then gives R(f v_n)_*.
Source: Stacks 03FC and 0D6E (blueprint: lem-sfb-cech-localization-unit-totalization). -/
def baseColumn (p : P) (n : SimplexCategory) : DerivedCategory AV :=
  F.rightDerivedFunctor.obj
    ((slice RX D V p n).rightDerivedFunctor.obj ((DerivedCategory.singleFunctor (Modules RX) 0).obj
      (N.obj p)))

/-- Every Cech operator on the canonical derived columns, including degeneracies.
Source: Stacks 03FC (blueprint: lem-sfb-cech-localization-unit-totalization). -/
def columnOperator (p : P) {n m : SimplexCategory} (θ : n ⟶ m) :
    baseColumn RX D F V N p n ⟶ baseColumn RX D F V N p m :=
  F.rightDerivedFunctor.map ((Functor.rightDerivedFunctorNatTrans
    (D.image.map (((sheafCoverNerve (V.obj (op p))).map θ.op).op))).app
      ((DerivedCategory.singleFunctor (Modules RX) 0).obj (N.obj p)))

/-- Simultaneous change of coefficients and refinement of the covering sheaf.
The direction P^op -> covers makes a refinement V_q -> V_p accompany N_p -> N_q.
Source: Stacks 03FC (blueprint: lem-sfb-cech-localization-unit-totalization). -/
def columnChange {p q : P} (a : p ⟶ q) (n : SimplexCategory) :
    baseColumn RX D F V N p n ⟶ baseColumn RX D F V N q n :=
  F.rightDerivedFunctor.map
    ((Functor.rightDerivedFunctorNatTrans
      (D.image.map (((Arrow.mapCechNerve
        (Arrow.homMk (V.map a.op) (𝟙 _) (terminal.hom_ext _ _) :
          Arrow.mk (terminal.from (V.obj (op q))) ⟶
            Arrow.mk (terminal.from (V.obj (op p))))).app (op n)).op))).app
        ((DerivedCategory.singleFunctor (Modules RX) 0).obj (N.obj p)) ≫
      (slice RX D V q n).rightDerivedFunctor.map
        ((DerivedCategory.singleFunctor (Modules RX) 0).map (N.map a)))

/-- The actual derived restriction-of-sections augmentation in every Cech degree.
Source: Stacks 03FC and 015F (blueprint: lem-sfb-cech-localization-unit-totalization). -/
def columnAugmentation (p : P) (n : SimplexCategory) :
    F.rightDerivedFunctor.obj ((DerivedCategory.singleFunctor (Modules RX) 0).obj (N.obj p)) ⟶
      baseColumn RX D F V N p n :=
  F.rightDerivedFunctor.map (((Functor.mapDerivedCategoryIdIso _).inv ≫
      (Functor.rightDerivedFunctorIsoMapDerivedCategory (𝟭 _)).inv ≫
        Functor.rightDerivedFunctorNatTrans (D.augmentation (power V p n))).app
          ((DerivedCategory.singleFunctor (Modules RX) 0).obj (N.obj p)))

/-- Complete compatible models for the two augmented Cech comparisons.
All resolutions, isomorphisms and lifts are conclusions of the theorem. Column maps
and augmentations are fixed by the displayed canonical derived maps, not freely supplied.
Source: Stacks 03FC, 015J, 015F (blueprint: lem-sfb-cech-localization-unit-totalization). -/
structure Comparison where
  source : AugmentedModel AB P
  target : AugmentedModel AB P
  sourcePoint :
    N ⋙ DerivedCategory.singleFunctor (Modules RX) 0 ⋙ F.rightDerivedFunctor ⋙
      G.rightDerivedFunctor ⋙
      T.mapDerivedCategory ≅ source.point ⋙ QNN AB
  targetPoint :
    N ⋙ DerivedCategory.singleFunctor (Modules RX) 0 ⋙ F.rightDerivedFunctor ⋙
      H.mapDerivedCategory ⋙ G.rightDerivedFunctor ⋙
      T.mapDerivedCategory ≅ target.point ⋙ QNN AB
  sourceColumns : ∀ (p : P) (n : SimplexCategory),
    T.mapDerivedCategory.obj (G.rightDerivedFunctor.obj (baseColumn RX D F V N p n)) ≅
      (QNN AB).obj ((source.columns.obj p).obj n)
  targetColumns : ∀ (p : P) (n : SimplexCategory),
    T.mapDerivedCategory.obj (G.rightDerivedFunctor.obj
      (H.mapDerivedCategory.obj (baseColumn RX D F V N p n))) ≅
      (QNN AB).obj ((target.columns.obj p).obj n)
  source_operator : ∀ (p : P) (n m : SimplexCategory) (θ : n ⟶ m),
    T.mapDerivedCategory.map (G.rightDerivedFunctor.map (columnOperator RX D F V N p θ)) ≫
      (sourceColumns p m).hom = (sourceColumns p n).hom ≫
        (QNN AB).map ((source.columns.obj p).map θ)
  target_operator : ∀ (p : P) (n m : SimplexCategory) (θ : n ⟶ m),
    T.mapDerivedCategory.map (G.rightDerivedFunctor.map
      (H.mapDerivedCategory.map (columnOperator RX D F V N p θ))) ≫
      (targetColumns p m).hom = (targetColumns p n).hom ≫
        (QNN AB).map ((target.columns.obj p).map θ)
  source_natural : ∀ (p q : P) (b : p ⟶ q) (n : SimplexCategory),
    T.mapDerivedCategory.map (G.rightDerivedFunctor.map (columnChange RX D F V N b n)) ≫
      (sourceColumns q n).hom = (sourceColumns p n).hom ≫
        (QNN AB).map ((source.columns.map b).app n)
  target_natural : ∀ (p q : P) (b : p ⟶ q) (n : SimplexCategory),
    T.mapDerivedCategory.map (G.rightDerivedFunctor.map
      (H.mapDerivedCategory.map (columnChange RX D F V N b n))) ≫
      (targetColumns q n).hom = (targetColumns p n).hom ≫
        (QNN AB).map ((target.columns.map b).app n)
  source_augmentation : ∀ (p : P) (n : SimplexCategory),
    sourcePoint.hom.app p ≫ (QNN AB).map ((source.augmentation.app p).app n) =
      T.mapDerivedCategory.map (G.rightDerivedFunctor.map
        (columnAugmentation RX D F V N p n)) ≫ (sourceColumns p n).hom
  target_augmentation : ∀ (p : P) (n : SimplexCategory),
    targetPoint.hom.app p ≫ (QNN AB).map ((target.augmentation.app p).app n) =
      T.mapDerivedCategory.map (G.rightDerivedFunctor.map
        (H.mapDerivedCategory.map (columnAugmentation RX D F V N p n))) ≫
          (targetColumns p n).hom
  unitColumns : source.columns ⟶ target.columns
  unit_columns : ∀ (p : P) (n : SimplexCategory),
    (sourceColumns p n).hom ≫ (QNN AB).map ((unitColumns.app p).app n) =
      T.mapDerivedCategory.map (G.rightDerivedFunctor.map
        ((exactUnit η).app (baseColumn RX D F V N p n))) ≫ (targetColumns p n).hom
  sourceComparison :
    N ⋙ DerivedCategory.singleFunctor (Modules RX) 0 ⋙ F.rightDerivedFunctor ⋙
      G.rightDerivedFunctor ⋙
      T.mapDerivedCategory ≅ source.columns ⋙ total AB ⋙ DerivedCategory.Q
  targetComparison :
    N ⋙ DerivedCategory.singleFunctor (Modules RX) 0 ⋙ F.rightDerivedFunctor ⋙
      H.mapDerivedCategory ⋙ G.rightDerivedFunctor ⋙
      T.mapDerivedCategory ≅ target.columns ⋙ total AB ⋙ DerivedCategory.Q
  source_normalization : ∀ p : P,
    sourcePoint.hom.app p ≫ DerivedCategory.Q.map (source.totalAugmentation.app p) =
      sourceComparison.hom.app p
  target_normalization : ∀ p : P,
    targetPoint.hom.app p ≫ DerivedCategory.Q.map (target.totalAugmentation.app p) =
      targetComparison.hom.app p
  unit_total : ∀ p : P,
    T.mapDerivedCategory.map (G.rightDerivedFunctor.map
      ((exactUnit η).app (F.rightDerivedFunctor.obj
        ((DerivedCategory.singleFunctor (Modules RX) 0).obj (N.obj p))))) ≫
      targetComparison.hom.app p = sourceComparison.hom.app p ≫
        DerivedCategory.Q.map ((total AB).map (unitColumns.app p))

/-- Applying a specified exact restriction to the whole comparison square.
The arrow inside S.map is the original derived unit, as in Comparison.unit_total.
Source: Stacks 03DJ and 015F (blueprint: lem-sfb-cech-localization-unit-totalization). -/
def Comparison.Restricts
    (c : Comparison RX D F G T H η V N)
    {E : Type v} [Category.{w} E] (S : DerivedCategory AB ⥤ E) : Prop :=
  ∀ p : P,
    S.map (T.mapDerivedCategory.map (G.rightDerivedFunctor.map
      ((exactUnit η).app (F.rightDerivedFunctor.obj
        ((DerivedCategory.singleFunctor (Modules RX) 0).obj (N.obj p))))) ≫
          c.targetComparison.hom.app p) =
      S.map (c.sourceComparison.hom.app p ≫
        DerivedCategory.Q.map ((total AB).map (c.unitColumns.app p)))

end Comparison



/-- Exact restriction of the ordinary derived category to the genuine ringed slice site.
The localization model on the slice is the standard one; the underlying functor is
exactly the recorded overFunctor, with its explicit site universes.
Source: Stacks 03DJ and 04IX (blueprint: lem-sfb-cech-localization-unit-totalization). -/
def restrictDerived {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{u}) [HasDerivedCategory.{u + 1} (Modules R)] (U : C) :
    letI : HasDerivedCategory.{u + 1}
      (SheafOfModules.{u} (((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).over U)) :=
      HasDerivedCategory.standard _
    DerivedCategory (Modules R) ⥤
      DerivedCategory
        (SheafOfModules.{u} (((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).over U)) :=
  letI : HasDerivedCategory.{u + 1}
      (SheafOfModules.{u} (((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).over U)) :=
    HasDerivedCategory.standard _
  (SheafOfModules.localizedSystemRestriction.{u, u, u} R U).mapDerivedCategory

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits


section PushforwardFamily

variable {CX CV : Type u} [SmallCategory CX] [SmallCategory CV]
  {JX : GrothendieckTopology CX} {JV : GrothendieckTopology CV}
  (RX : Sheaf JX CommRingCat.{u}) (RV : Sheaf JV CommRingCat.{u})
  [HasDerivedCategory.{u + 1} (Modules RX)] [HasDerivedCategory.{u + 1} (Modules RV)]
  [Abelian.HasKInjectiveResolutions (Modules RX)]
  (D : CoherentCechImageModel ((sheafCompose JX (forget₂ CommRingCat RingCat)).obj RX))
  (F : Modules RX ⥤ Modules RV) [F.Additive]
  {P : Type uP} [Category.{vP} P]
  (V : Pᵒᵖ ⥤ Sheaf JX (Type u)) (N : P ⥤ Modules RX)

/-- A strict functorial version of the normalized pushforward model, before applying
any additional derived direct image or exact unit.
Source: Stacks 03FC (blueprint: def-sfb-cech-localization-unit-models). -/
structure PushforwardFamily where
  model : AugmentedModel (Modules RV) P
  pointIso : N ⋙ DerivedCategory.singleFunctor (Modules RX) 0 ⋙ F.rightDerivedFunctor ≅
    model.point ⋙ QNN (Modules RV)
  columnIso : ∀ (p : P) (n : SimplexCategory),
    baseColumn RX D F V N p n ≅ (QNN (Modules RV)).obj ((model.columns.obj p).obj n)
  operator : ∀ (p : P) (n m : SimplexCategory) (θ : n ⟶ m),
    F.rightDerivedFunctor.map ((Functor.rightDerivedFunctorNatTrans
      (D.image.map (((sheafCoverNerve (V.obj (op p))).map θ.op).op))).app
        ((DerivedCategory.singleFunctor (Modules RX) 0).obj (N.obj p))) ≫
      (columnIso p m).hom = (columnIso p n).hom ≫
        (QNN (Modules RV)).map ((model.columns.obj p).map θ)
  natural : ∀ (p q : P) (b : p ⟶ q) (n : SimplexCategory),
    columnChange RX D F V N b n ≫ (columnIso q n).hom =
      (columnIso p n).hom ≫ (QNN (Modules RV)).map ((model.columns.map b).app n)
  augmentation : ∀ (p : P) (n : SimplexCategory),
    pointIso.hom.app p ≫ (QNN (Modules RV)).map ((model.augmentation.app p).app n) =
      columnAugmentation RX D F V N p n ≫ (columnIso p n).hom

end PushforwardFamily

section UnitFamily

variable {A : Type (u + 1)} [Category.{u} A] [Abelian A]
  {B : Type (u + 1)} [Category.{u} B] [Abelian B]
  {C : Type (u + 1)} [Category.{u} C] [Abelian C]
  [HasDerivedCategory.{u + 1} A] [HasDerivedCategory.{u + 1} B]
  [HasDerivedCategory.{u + 1} C]
  [Abelian.HasKInjectiveResolutions A] [Abelian.HasKInjectiveResolutions B]
  (G : A ⥤ B) [G.Additive]
  (T : B ⥤ C) [T.Additive] [PreservesFiniteLimits T] [PreservesFiniteColimits T]
  (H : A ⥤ A) [H.Additive] [PreservesFiniteLimits H] [PreservesFiniteColimits H]
  (η : 𝟭 A ⟶ H)
  {P : Type uP} [Category.{vP} P]
  (M : P ⥤ DerivedCategory A) (b : AugmentedModel A P)
  (a : M ≅ b.point ⋙ QNN A)

/-- The exact-unit comparison for an arbitrary supplied augmented family. There are no
sites, covers or localization adjunctions in these data.
Source: Stacks 015F and 015J (blueprint: def-sfb-cech-localization-unit-models). -/
structure UnitFamily where
  source : AugmentedModel C P
  target : AugmentedModel C P
  sourcePoint : M ⋙ G.rightDerivedFunctor ⋙ T.mapDerivedCategory ≅ source.point ⋙ QNN C
  targetPoint : M ⋙ H.mapDerivedCategory ⋙ G.rightDerivedFunctor ⋙ T.mapDerivedCategory ≅
    target.point ⋙ QNN C
  sourceColumns : ∀ (p : P) (n : SimplexCategory),
    T.mapDerivedCategory.obj (G.rightDerivedFunctor.obj
      ((QNN A).obj ((b.columns.obj p).obj n))) ≅
        (QNN C).obj ((source.columns.obj p).obj n)
  targetColumns : ∀ (p : P) (n : SimplexCategory),
    T.mapDerivedCategory.obj (G.rightDerivedFunctor.obj
      (H.mapDerivedCategory.obj ((QNN A).obj ((b.columns.obj p).obj n)))) ≅
        (QNN C).obj ((target.columns.obj p).obj n)
  source_operator : ∀ (p : P) (n m : SimplexCategory) (θ : n ⟶ m),
    T.mapDerivedCategory.map (G.rightDerivedFunctor.map
      ((QNN A).map ((b.columns.obj p).map θ))) ≫ (sourceColumns p m).hom =
        (sourceColumns p n).hom ≫ (QNN C).map ((source.columns.obj p).map θ)
  target_operator : ∀ (p : P) (n m : SimplexCategory) (θ : n ⟶ m),
    T.mapDerivedCategory.map (G.rightDerivedFunctor.map (H.mapDerivedCategory.map
      ((QNN A).map ((b.columns.obj p).map θ)))) ≫ (targetColumns p m).hom =
        (targetColumns p n).hom ≫ (QNN C).map ((target.columns.obj p).map θ)
  source_natural : ∀ (p q : P) (k : p ⟶ q) (n : SimplexCategory),
    T.mapDerivedCategory.map (G.rightDerivedFunctor.map
      ((QNN A).map ((b.columns.map k).app n))) ≫ (sourceColumns q n).hom =
        (sourceColumns p n).hom ≫ (QNN C).map ((source.columns.map k).app n)
  target_natural : ∀ (p q : P) (k : p ⟶ q) (n : SimplexCategory),
    T.mapDerivedCategory.map (G.rightDerivedFunctor.map (H.mapDerivedCategory.map
      ((QNN A).map ((b.columns.map k).app n)))) ≫ (targetColumns q n).hom =
        (targetColumns p n).hom ≫ (QNN C).map ((target.columns.map k).app n)
  source_augmentation : ∀ (p : P) (n : SimplexCategory),
    sourcePoint.hom.app p ≫ (QNN C).map ((source.augmentation.app p).app n) =
      T.mapDerivedCategory.map (G.rightDerivedFunctor.map
        (a.hom.app p ≫ (QNN A).map ((b.augmentation.app p).app n))) ≫
          (sourceColumns p n).hom
  target_augmentation : ∀ (p : P) (n : SimplexCategory),
    targetPoint.hom.app p ≫ (QNN C).map ((target.augmentation.app p).app n) =
      T.mapDerivedCategory.map (G.rightDerivedFunctor.map (H.mapDerivedCategory.map
        (a.hom.app p ≫ (QNN A).map ((b.augmentation.app p).app n)))) ≫
          (targetColumns p n).hom
  unitColumns : source.columns ⟶ target.columns
  unit_columns : ∀ (p : P) (n : SimplexCategory),
    (sourceColumns p n).hom ≫ (QNN C).map ((unitColumns.app p).app n) =
      T.mapDerivedCategory.map (G.rightDerivedFunctor.map
        ((exactUnit η).app ((QNN A).obj ((b.columns.obj p).obj n)))) ≫
          (targetColumns p n).hom
  sourceComparison : M ⋙ G.rightDerivedFunctor ⋙ T.mapDerivedCategory ≅
    source.columns ⋙ total C ⋙ DerivedCategory.Q
  targetComparison : M ⋙ H.mapDerivedCategory ⋙ G.rightDerivedFunctor ⋙
    T.mapDerivedCategory ≅ target.columns ⋙ total C ⋙ DerivedCategory.Q
  source_normalization : ∀ p : P,
    sourcePoint.hom.app p ≫ DerivedCategory.Q.map (source.totalAugmentation.app p) =
      sourceComparison.hom.app p
  target_normalization : ∀ p : P,
    targetPoint.hom.app p ≫ DerivedCategory.Q.map (target.totalAugmentation.app p) =
      targetComparison.hom.app p
  unit_total : ∀ p : P,
    T.mapDerivedCategory.map (G.rightDerivedFunctor.map ((exactUnit η).app (M.obj p))) ≫
      targetComparison.hom.app p = sourceComparison.hom.app p ≫
        DerivedCategory.Q.map ((total C).map (unitColumns.app p))

end UnitFamily

end CategoryTheory.CechLocalizationUnit

```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.CategoryTheory.CechLocalizationUnitTotalization | K5 | Publicly imports the extracted definitions; its original theorem statement is identical. |
| Sheaf.CategoryTheory.CechPushforwardAugmentedFamily | K5, new | Uses the pushforward family interface only; no exact-unit comparison assumed. |
| Sheaf.CategoryTheory.ExactUnitAugmentedFamily | K5, new | Uses the abstract augmented-family interface; no Cech pushforward or localization assumed. |

The repository has no direct Lean importers of the assigned module: the anchored
import search over lean/ returned no files. No existing consumer or target needs
adaptation. The DAG parents continue to refer to the same theorem and statement.

## Status

landed 20261026T091916-L-3386165 2026-10-26 (merge of deliver/K5/Sheaf.CategoryTheory.CechLocalizationUnitTotalization)
