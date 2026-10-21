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
import Sheaf.CategoryTheory.DerivedCechImageTotalization
import Sheaf.CategoryTheory.NonnegativeDerivedTotalization
public import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
public import WeilConjectures.Mathlib.Algebra.Homology.TotalComplex
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory
import Sheaf.CategoryTheory.DerivedCategory.CompositionAdjunctionNormalization
import Sheaf.CategoryTheory.Sites.ToposLocalizationSitePresentation
public import WeilConjectures.CategoryTheory.DoubleComplexTotal

/-! # The closed-localization unit under nonnegative Cech descent

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

set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedVariables false in
/-- The specified exact-adjunction unit is preserved by augmented nonnegative Cech descent,
by derived direct images, and by exact restriction to an object of B's site.

Source: main-20261015 direct-images.proof.md (3), the agent-formulated first-quadrant
input preceding the root-tower calculation; Stacks 03FC, 015J, 015F, 09T5, 0D6E,
03DJ and 04IX (blueprint: lem-sfb-cech-localization-unit-totalization).

Proof: Resolve N functorially in nonnegative degrees. Apply the Cech slice direct-image
functors to that resolution. Use D.image and its specified localization adjunctions, with
D.unit fixing D.augmentation to restriction of sections. D.augmentation_naturality
fixes compatibility with every nerve and refinement map. Injective sheaves have acyclic
augmented Cech complexes,
so its finite-diagonal total is a quasi-isomorphism (03FC). Apply f_* and the
nonnegative derived-totalization comparison, normalized at that augmentation (015J).
Exactness of f^* and the slice inverse images identifies the columns with R(f v_n)_*
by the adjunction-normalized composition comparison (09T5, 0D6E). Apply the exact
H termwise. Naturality of the specified unit on every finite biproduct inclusion
identifies eta on the total with the total of eta on the columns, with the same signs.
Resolve both resulting diagrams compatibly in nonnegative degrees before applying g_*;
015J applied to their strict unit map gives the commuting square. Apply exact t^*;
it preserves each finite diagonal. These constructions commute with all coefficient
maps, all Cech operators and all cover refinements, giving the natural isomorphisms
recorded in Comparison. Their augmentation equations retain the original restriction
of sections. Finally apply the exact overFunctor on B at U (03DJ, 04IX) to the whole
square, with the pulled-back coefficient ring. This is precisely the restriction of
the original specified unit, and uses no sliced version of the arbitrary h adjunction.
All complexes used for totalization are nonnegative; no unbounded product is used. -/
theorem cech_localization_unit_totalization
    {CX CV CY CZ CB : Type u}
    [SmallCategory CX] [SmallCategory CV] [SmallCategory CY]
    [SmallCategory CZ] [SmallCategory CB]
    {JX : GrothendieckTopology CX} {JV : GrothendieckTopology CV}
    {JY : GrothendieckTopology CY} {JZ : GrothendieckTopology CZ}
    {JB : GrothendieckTopology CB}
    (RX : Sheaf JX CommRingCat.{u}) (RV : Sheaf JV CommRingCat.{u})
    (RY : Sheaf JY CommRingCat.{u}) (RZ : Sheaf JZ CommRingCat.{u})
    (RB : Sheaf JB CommRingCat.{u})
    [IsGrothendieckAbelian.{u} (Modules RX)] [IsGrothendieckAbelian.{u} (Modules RV)]
    [IsGrothendieckAbelian.{u} (Modules RY)] [IsGrothendieckAbelian.{u} (Modules RZ)]
    [IsGrothendieckAbelian.{u} (Modules RB)]
    [HasDerivedCategory.{u + 1} (Modules RX)] [HasDerivedCategory.{u + 1} (Modules RV)]
    [HasDerivedCategory.{u + 1} (Modules RY)] [HasDerivedCategory.{u + 1} (Modules RZ)]
    [HasDerivedCategory.{u + 1} (Modules RB)]
    (f : RingedToposMorphism
      ((sheafCompose JX (forget₂ CommRingCat RingCat)).obj RX)
      ((sheafCompose JV (forget₂ CommRingCat RingCat)).obj RV))
    (g : RingedToposMorphism
      ((sheafCompose JV (forget₂ CommRingCat RingCat)).obj RV)
      ((sheafCompose JY (forget₂ CommRingCat RingCat)).obj RY))
    (t : RingedToposMorphism
      ((sheafCompose JB (forget₂ CommRingCat RingCat)).obj RB)
      ((sheafCompose JY (forget₂ CommRingCat RingCat)).obj RY))
    (fInverse : Modules RV ⥤ Modules RX) [fInverse.Additive]
    [PreservesFiniteLimits fInverse] [PreservesFiniteColimits fInverse]
    (fAdj : fInverse ⊣ f.modules)
    (gInverse : Modules RY ⥤ Modules RV) [gInverse.Additive]
    [PreservesFiniteLimits gInverse] [PreservesFiniteColimits gInverse]
    (gAdj : gInverse ⊣ g.modules)
    (tInverse : Modules RY ⥤ Modules RB) [tInverse.Additive]
    [PreservesFiniteLimits tInverse] [PreservesFiniteColimits tInverse]
    (tAdj : tInverse ⊣ t.modules)
    (hInverse : Modules RV ⥤ Modules RZ) (hDirect : Modules RZ ⥤ Modules RV)
    [hInverse.Additive] [hDirect.Additive]
    [PreservesFiniteLimits hInverse] [PreservesFiniteColimits hInverse]
    [PreservesFiniteLimits hDirect] [PreservesFiniteColimits hDirect]
    (hAdj : hInverse ⊣ hDirect)
    {P : Type uP} [Category.{vP} P]
    (V : Pᵒᵖ ⥤ Sheaf JX (Type u)) (N : P ⥤ Modules RX)
    (cover : ∀ p : P, Epi (terminal.from (V.obj (op p))))
    (D : CoherentCechImageModel ((sheafCompose JX (forget₂ CommRingCat RingCat)).obj RX)) :
    ∃ (c : Comparison RX D f.modules g.modules tInverse
      (hInverse ⋙ hDirect) hAdj.unit V N),
      ∀ U : CB,
        Comparison.Restricts RX D f.modules g.modules tInverse
          (hInverse ⋙ hDirect) hAdj.unit V N c (restrictDerived RB U) := by
  sorry

end CategoryTheory.CechLocalizationUnit
