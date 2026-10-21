module

public import Sheaf.CategoryTheory.CondensedNormalInvariantData
public import Sheaf.CategoryTheory.CondensedActionModule
public import Sheaf.Topology.ProfiniteCondensedRing
public import Sheaf.CategoryTheory.CondensedEquivariantBarData
public import Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions
public import Mathlib.Topology.Algebra.Category.ProfiniteGrp.Basic
public import Mathlib.Topology.Algebra.OpenSubgroup
public import Mathlib.Topology.Algebra.Group.Quotient
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedComp
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Adjunction

import Sheaf.CategoryTheory.DerivedCategory.CompositionAdjunctionNormalization
import Sheaf.CategoryTheory.RingedToposMorphism
import Sheaf.CategoryTheory.RingedDerivedCompositionCocycle
import WeilConjectures.CategoryTheory.RingedSiteGrothendieckAbelian
import Sheaf.CategoryTheory.CondensedSplitCosetInduction
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
import Sheaf.CategoryTheory.InternalActionSitePresentation
import Sheaf.CategoryTheory.KInjectiveExactSquareComparison
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
import Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition

/-! # Normalized derived invariants through an open normal subgroup

Source: blueprint direct-image stability, paragraph (3)
(blueprint: lem-sfb-derived-invariants-normal-subgroup-comparison).

## Main declarations

* NormalQuotient and NormalDerivedComparison retain the fixed-section normalizations.
* normalBeta and normalComparison are the canonical unbounded comparison isomorphisms.
* NormalAssertion states all compatibility diagrams and categorical conclusions.
* normal_subgroup_comparison is the sole postponed theorem.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.CondensedBar (Ring ScalarAction ActionAbelian)
namespace Profinite.CondensedAction

variable [C : NormalComparisonCategories.{u}]

/-- The existing internal-module scalar restriction, with its source and target fixed
before using it in derived diagrams. Its data is precisely Mod.comap.
Source: internal module scalar restriction and blueprint paragraph (3)
(blueprint: lem-sfb-derived-invariants-normal-subgroup-comparison). -/
def normalScalarRestriction (A B : Ring.{u}) (a : B ⟶ A) :
    Modules A.toMon ⥤ Modules B.toMon := Mod.comap a.hom.hom

/-- Coefficient restriction on the existing internal modules and equivariant modules.
The underlying comparison and action formula in ScalarAction pin this to scalar
restriction along the specified condensed-ring morphism.
Source: blueprint paragraph (3), coefficient normalization
(blueprint: lem-sfb-derived-invariants-normal-subgroup-comparison). -/
class NormalScalars where
  action : ∀ (A B : Ring.{u}) (a : B ⟶ A) (P : ProfiniteGrp.{u}), ScalarAction a P
  exact : ∀ (A B : Ring.{u}) (a : B ⟶ A) (P : ProfiniteGrp.{u}),
    NormalExact (action A B a P).functor
  modulesExact : ∀ (A B : Ring.{u}) (a : B ⟶ A),
    NormalExact (normalScalarRestriction A B a)

attribute [instance] NormalScalars.exact NormalScalars.modulesExact

/-- The specified scalar restriction followed by restriction of the auxiliary group.
Source: blueprint paragraph (3)
(blueprint: lem-sfb-derived-invariants-normal-subgroup-comparison). -/
def normalChange [S : NormalScalars.{u}]
    (A B : Ring.{u}) (a : B ⟶ A) (G L L' : ProfiniteGrp.{u}) (h : L' →ₜ* L) :
    ActionModule A.toMon (G × L) ⥤ ActionModule B.toMon (G × L') :=
  (S.action A B a (normalProduct G L)).functor ⋙
    inflate (ContinuousMonoidHom.prodMap (ContinuousMonoidHom.id G) h)

/-- Exactness of the constructed coefficient and auxiliary-group restriction.
Source: blueprint paragraph (3)
(blueprint: lem-sfb-derived-invariants-normal-subgroup-comparison). -/
instance normalChangeExact [V : NormalInvariantFamily.{u}] [S : NormalScalars.{u}]
    (A B : Ring.{u}) (a : B ⟶ A) (G L L' : ProfiniteGrp.{u}) (h : L' →ₜ* L) :
    NormalExact (normalChange A B a G L L' h) := by
  let : NormalExact (S.action A B a (normalProduct G L)).functor :=
    S.exact A B a (normalProduct G L)
  let : NormalExact (inflate (R := B.toMon)
      (ContinuousMonoidHom.prodMap (ContinuousMonoidHom.id G) h)) :=
    V.restrictExact B (G × L') (G × L)
      (ContinuousMonoidHom.prodMap (ContinuousMonoidHom.id G) h)
  exact normalExactComp _ _

/-- Ordinary invariants commute with scalar restriction and include into invariants after
restriction of the auxiliary action. These ordinary maps are normalized on section
inclusions; their derived maps are the canonical normalSquare transformations.
Source: blueprint paragraph (3), proof steps 9 to 11
(blueprint: lem-sfb-derived-invariants-normal-subgroup-comparison). -/
structure NormalChangeData [V : NormalInvariantFamily.{u}] [W : NormalSystem.{u}]
    [S : NormalScalars.{u}] (A B : Ring.{u}) (a : B ⟶ A)
    (G L L' : ProfiniteGrp.{u}) (K : OpenNormalSubgroup G) (h : L' →ₜ* L) where
  quotient : (W.quotient A G L K).functor ⋙
      normalChange A B a (normalQuotient G K) L L' h ⟶
    normalChange A B a G L L' h ⋙ (W.quotient B G L' K).functor
  total : (V.invariants A (normalProduct G L)).functor ⋙
      (normalScalarRestriction A B a) ⟶
    normalChange A B a G L L' h ⋙ (V.invariants B (normalProduct G L')).functor
  outer : (V.invariants A (normalProduct (normalQuotient G K) L)).functor ⋙
      (normalScalarRestriction A B a) ⟶
    normalChange A B a (normalQuotient G K) L L' h ⋙
      (V.invariants B (normalProduct (normalQuotient G K) L')).functor
  kernel : (V.invariants A (normalKernel G K)).functor ⋙
      (normalScalarRestriction A B a) ≅
    (S.action A B a (normalKernel G K)).functor ⋙
      (V.invariants B (normalKernel G K)).functor
  kernelRestriction : normalChange A B a G L L' h ⋙
      inflate (R := B.toMon) (normalKernelInclusion G K L') ≅
    inflate (R := A.toMon) (normalKernelInclusion G K L) ⋙
      (S.action A B a (normalKernel G K)).functor
  kernelRestriction_underlying : ∀ N,
    (kernelRestriction.hom.app N).val ≫
      (S.action A B a (normalKernel G K)).underlying.hom.app
        ((inflate (R := A.toMon) (normalKernelInclusion G K L)).obj N) =
      (S.action A B a (normalProduct G L)).underlying.hom.app N
  total_inclusion : ∀ N,
    total.app N ≫ (V.invariants B (normalProduct G L')).inclusion.app
        ((normalChange A B a G L L' h).obj N) ≫
      (S.action A B a (normalProduct G L)).underlying.hom.app N =
    ((normalScalarRestriction A B a)).map
      ((V.invariants A (normalProduct G L)).inclusion.app N)
  outer_inclusion : ∀ N,
    outer.app N ≫ (V.invariants B (normalProduct (normalQuotient G K) L')).inclusion.app
        ((normalChange A B a (normalQuotient G K) L L' h).obj N) ≫
      (S.action A B a (normalProduct (normalQuotient G K) L)).underlying.hom.app N =
    ((normalScalarRestriction A B a)).map
      ((V.invariants A (normalProduct (normalQuotient G K) L)).inclusion.app N)
  quotient_inclusion : ∀ N,
    (quotient.app N).val ≫ (W.quotient B G L' K).inclusion.app
        ((normalChange A B a G L L' h).obj N) ≫
      (S.action A B a (normalProduct G L)).underlying.hom.app N =
    (S.action A B a (normalProduct (normalQuotient G K) L)).underlying.hom.app
        ((W.quotient A G L K).functor.obj N) ≫
      ((normalScalarRestriction A B a)).map
        ((W.quotient A G L K).inclusion.app N)
  kernel_inclusion : ∀ N,
    kernel.hom.app N ≫ (V.invariants B (normalKernel G K)).inclusion.app
        (((S.action A B a (normalKernel G K)).functor).obj N) ≫
      (S.action A B a (normalKernel G K)).underlying.hom.app N =
    ((normalScalarRestriction A B a)).map
      ((V.invariants A (normalKernel G K)).inclusion.app N)

/-- The canonical total-invariant transformation of coefficient and auxiliary-group change.
Source: blueprint paragraph (3)
(blueprint: lem-sfb-derived-invariants-normal-subgroup-comparison). -/
def NormalChangeData.derivedTotal [V : NormalInvariantFamily.{u}] [W : NormalSystem.{u}]
    [S : NormalScalars.{u}] {A B : Ring.{u}} {a : B ⟶ A}
    {G L L' : ProfiniteGrp.{u}} {K : OpenNormalSubgroup G} {h : L' →ₜ* L}
    (e : NormalChangeData A B a G L L' K h) :=
  letI : NormalExact (normalChange A B a G L L' h) :=
    normalChangeExact A B a G L L' h
  letI : NormalExact (normalChange A B a (normalQuotient G K) L L' h) :=
    normalChangeExact A B a (normalQuotient G K) L L' h
  normalSquare (V.invariants A (normalProduct G L)).functor
    (V.invariants B (normalProduct G L')).functor
    (normalChange A B a G L L' h)
    (normalScalarRestriction A B a) e.total

/-- The canonical quotient-invariant transformation of the same change.
Source: blueprint paragraph (3)
(blueprint: lem-sfb-derived-invariants-normal-subgroup-comparison). -/
def NormalChangeData.derivedQuotient [V : NormalInvariantFamily.{u}] [W : NormalSystem.{u}]
    [S : NormalScalars.{u}] {A B : Ring.{u}} {a : B ⟶ A}
    {G L L' : ProfiniteGrp.{u}} {K : OpenNormalSubgroup G} {h : L' →ₜ* L}
    (e : NormalChangeData A B a G L L' K h) :=
  letI : NormalExact (normalChange A B a G L L' h) :=
    normalChangeExact A B a G L L' h
  letI : NormalExact (normalChange A B a (normalQuotient G K) L L' h) :=
    normalChangeExact A B a (normalQuotient G K) L L' h
  normalSquare (W.quotient A G L K).functor (W.quotient B G L' K).functor
    (normalChange A B a G L L' h)
    (normalChange A B a (normalQuotient G K) L L' h) e.quotient

/-- The canonical residual-invariant transformation of the same change.
Source: blueprint paragraph (3)
(blueprint: lem-sfb-derived-invariants-normal-subgroup-comparison). -/
def NormalChangeData.derivedOuter [V : NormalInvariantFamily.{u}] [W : NormalSystem.{u}]
    [S : NormalScalars.{u}] {A B : Ring.{u}} {a : B ⟶ A}
    {G L L' : ProfiniteGrp.{u}} {K : OpenNormalSubgroup G} {h : L' →ₜ* L}
    (e : NormalChangeData A B a G L L' K h) :=
  letI : NormalExact (normalChange A B a G L L' h) :=
    normalChangeExact A B a G L L' h
  letI : NormalExact (normalChange A B a (normalQuotient G K) L L' h) :=
    normalChangeExact A B a (normalQuotient G K) L L' h
  normalSquare (V.invariants A (normalProduct (normalQuotient G K) L)).functor
    (V.invariants B (normalProduct (normalQuotient G K) L')).functor
    (normalChange A B a (normalQuotient G K) L L' h)
    (normalScalarRestriction A B a) e.outer

/-- Coefficient and auxiliary-group change commute with the normalized derived composition
comparison, as an equality of arrows at every unbounded derived object. Since each side
is a natural transformation this also includes every equivariant map N → Res N'.
Source: blueprint paragraph (3), proof steps 9 to 11
(blueprint: lem-sfb-derived-invariants-normal-subgroup-comparison). -/
def NormalChangeCompatible [V : NormalInvariantFamily.{u}] [W : NormalSystem.{u}]
    [S : NormalScalars.{u}] {A B : Ring.{u}} {a : B ⟶ A}
    {G L L' : ProfiniteGrp.{u}} {K : OpenNormalSubgroup G} {h : L' →ₜ* L}
    (e : NormalChangeData A B a G L L' K h) : Prop :=
  ∀ N : DerivedCategory (ActionModule A.toMon (G × L)),
    e.derivedTotal.app N ≫
      (normalComparison B G L' K (W.comparisons B G L' K)).hom.app
        ((normalChange A B a G L L' h).mapDerivedCategory.obj N) =
    ((normalScalarRestriction A B a)).mapDerivedCategory.map
        ((normalComparison A G L K (W.comparisons A G L K)).hom.app N) ≫
      e.derivedOuter.app ((W.quotient A G L K).functor.rightDerivedFunctor.obj N) ≫
      (V.invariants B (normalProduct (normalQuotient G K) L')).functor.rightDerivedFunctor.map
        (e.derivedQuotient.app N)

/-- Scalar restriction commutes with forgetting the remaining quotient action.
Source: blueprint paragraph (3)
(blueprint: lem-sfb-derived-invariants-normal-subgroup-comparison). -/
def normalChangeForget [V : NormalInvariantFamily.{u}] [S : NormalScalars.{u}]
    (A B : Ring.{u}) (a : B ⟶ A) (P L L' : ProfiniteGrp.{u}) (h : L' →ₜ* L) :
    (normalChange A B a P L L' h).mapDerivedCategory ⋙
        (forgetAction (R := B.toMon) (P := P × L')).mapDerivedCategory ≅
      (forgetAction (R := A.toMon) (P := P × L)).mapDerivedCategory ⋙
        (normalScalarRestriction A B a).mapDerivedCategory :=
  (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryNatIso (S.action A B a (normalProduct P L)).underlying ≪≫
    Functor.mapDerivedCategoryCompIso _ _

/-- The exact derived square for restriction to the kernel.
Source: blueprint paragraph (3)
(blueprint: lem-sfb-derived-invariants-normal-subgroup-comparison). -/
def NormalChangeData.derivedKernelRestriction [V : NormalInvariantFamily.{u}]
    [W : NormalSystem.{u}] [S : NormalScalars.{u}] {A B : Ring.{u}} {a : B ⟶ A}
    {G L L' : ProfiniteGrp.{u}} {K : OpenNormalSubgroup G} {h : L' →ₜ* L}
    (e : NormalChangeData A B a G L L' K h) :=
  letI : NormalExact (S.action A B a (normalKernel G K)).functor :=
    S.exact A B a (normalKernel G K)
  (Functor.mapDerivedCategoryCompIso (normalChange A B a G L L' h)
    (inflate (R := B.toMon) (normalKernelInclusion G K L'))).symm ≪≫
    Functor.mapDerivedCategoryNatIso e.kernelRestriction ≪≫
    Functor.mapDerivedCategoryCompIso
      (inflate (R := A.toMon) (normalKernelInclusion G K L))
      (S.action A B a (normalKernel G K)).functor

/-- The canonical K-invariant scalar transformation.
Source: blueprint paragraph (3)
(blueprint: lem-sfb-derived-invariants-normal-subgroup-comparison). -/
def NormalChangeData.derivedKernel [V : NormalInvariantFamily.{u}]
    [W : NormalSystem.{u}] [S : NormalScalars.{u}] {A B : Ring.{u}} {a : B ⟶ A}
    {G L L' : ProfiniteGrp.{u}} {K : OpenNormalSubgroup G} {h : L' →ₜ* L}
    (e : NormalChangeData A B a G L L' K h) :=
  letI : NormalExact (S.action A B a (normalKernel G K)).functor :=
    S.exact A B a (normalKernel G K)
  normalSquare (V.invariants A (normalKernel G K)).functor
    (V.invariants B (normalKernel G K)).functor (S.action A B a (normalKernel G K)).functor
    (normalScalarRestriction A B a) e.kernel.hom

/-- The first comparison commutes with all auxiliary-group and coefficient transformations.
Every transformation is obtained by deriving its section-normalized ordinary square.
Source: blueprint paragraph (3), proof steps 9 to 11
(blueprint: lem-sfb-derived-invariants-normal-subgroup-comparison). -/
def NormalBetaCompatible [V : NormalInvariantFamily.{u}] [W : NormalSystem.{u}]
    [NormalKernelPreserves.{u}] [S : NormalScalars.{u}] {A B : Ring.{u}} {a : B ⟶ A}
    {G L L' : ProfiniteGrp.{u}} {K : OpenNormalSubgroup G} {h : L' →ₜ* L}
    (e : NormalChangeData A B a G L L' K h) : Prop :=
  ∀ N : DerivedCategory (ActionModule A.toMon (G × L)),
    (normalChangeForget A B a (normalQuotient G K) L L' h).inv.app
        ((W.quotient A G L K).functor.rightDerivedFunctor.obj N) ≫
      (forgetAction (R := B.toMon) (P := (G ⧸ K.toSubgroup) × L')).mapDerivedCategory.map
        (e.derivedQuotient.app N) ≫
      (normalBeta B G L' K (W.comparisons B G L' K)).hom.app
        ((normalChange A B a G L L' h).mapDerivedCategory.obj N) =
    (normalScalarRestriction A B a).mapDerivedCategory.map
        ((normalBeta A G L K (W.comparisons A G L K)).hom.app N) ≫
      e.derivedKernel.app
        ((inflate (R := A.toMon) (normalKernelInclusion G K L)).mapDerivedCategory.obj N) ≫
      (V.invariants B (normalKernel G K)).functor.rightDerivedFunctor.map
        (e.derivedKernelRestriction.inv.app N)

/-- The ordinary quotient-change map applied to complexes, with the actual functor
composition identifications. Source: blueprint paragraph (3)
(blueprint: lem-sfb-derived-invariants-normal-subgroup-comparison). -/
def NormalChangeData.quotientComplex [V : NormalInvariantFamily.{u}] [W : NormalSystem.{u}]
    [S : NormalScalars.{u}] {A B : Ring.{u}} {a : B ⟶ A}
    {G L L' : ProfiniteGrp.{u}} {K : OpenNormalSubgroup G} {h : L' →ₜ* L}
    (e : NormalChangeData A B a G L L' K h)
    (X : CochainComplex (ActionModule A.toMon (G × L)) ℤ) :=
  letI : NormalExact (normalChange A B a (normalQuotient G K) L L' h) :=
    normalChangeExact A B a (normalQuotient G K) L L' h
  (Functor.mapHomologicalComplexCompIso
    (Iso.refl ((W.quotient A G L K).functor ⋙
      normalChange A B a (normalQuotient G K) L L' h)) (.up ℤ)).hom.app X ≫
    (NatTrans.mapHomologicalComplex e.quotient (.up ℤ)).app X ≫
    (Functor.mapHomologicalComplexCompIso
      (Iso.refl (normalChange A B a G L L' h ⋙ (W.quotient B G L' K).functor))
      (.up ℤ)).inv.app X

/-- Inflation and the resolution unit respect auxiliary-group and coefficient change.
The square includes all complexes, hence in particular all modules in degree zero.
Source: blueprint paragraph (3), proof steps 7 to 11
(blueprint: lem-sfb-derived-invariants-normal-subgroup-comparison). -/
def NormalInflationCompatible [V : NormalInvariantFamily.{u}] [W : NormalSystem.{u}]
    [S : NormalScalars.{u}] {A B : Ring.{u}} {a : B ⟶ A}
    {G L L' : ProfiniteGrp.{u}} {K : OpenNormalSubgroup G} {h : L' →ₜ* L}
    (e : NormalChangeData A B a G L L' K h) : Prop :=
  letI : NormalExact (normalChange A B a (normalQuotient G K) L L' h) :=
    normalChangeExact A B a (normalQuotient G K) L L' h
  ∀ X : CochainComplex (ActionModule A.toMon (G × L)) ℤ,
    e.derivedOuter.app (DerivedCategory.Q.obj
        (((W.quotient A G L K).functor.mapHomologicalComplex (.up ℤ)).obj X)) ≫
      (V.invariants B (normalProduct (normalQuotient G K) L')).functor.rightDerivedFunctor.map
        ((normalChange A B a (normalQuotient G K) L L' h).mapDerivedCategoryFactors.hom.app
            (((W.quotient A G L K).functor.mapHomologicalComplex (.up ℤ)).obj X) ≫
          DerivedCategory.Q.map (e.quotientComplex X)) ≫
      normalInflation B G L' K (W.comparisons B G L' K)
        (((normalChange A B a G L L' h).mapHomologicalComplex (.up ℤ)).obj X) =
    (normalScalarRestriction A B a).mapDerivedCategory.map
        (normalInflation A G L K (W.comparisons A G L K) X) ≫
      e.derivedTotal.app (DerivedCategory.Q.obj X) ≫
      (V.invariants B (normalProduct G L')).functor.rightDerivedFunctor.map
        ((normalChange A B a G L L' h).mapDerivedCategoryFactors.hom.app X)

/-- Functoriality of the actual inflation arrow in all equivariant chain maps.
Source: blueprint paragraph (3), proof step 8
(blueprint: lem-sfb-derived-invariants-normal-subgroup-comparison). -/
def NormalInflationNatural [V : NormalInvariantFamily.{u}] [W : NormalSystem.{u}]
    (A : Ring.{u}) (G L : ProfiniteGrp.{u}) (K : OpenNormalSubgroup G) : Prop :=
  ∀ (X Y : CochainComplex (ActionModule A.toMon (G × L)) ℤ) (f : X ⟶ Y),
    (V.invariants A (normalProduct (normalQuotient G K) L)).functor.rightDerivedFunctor.map
        (DerivedCategory.Q.map (((W.quotient A G L K).functor.mapHomologicalComplex
          (.up ℤ)).map f)) ≫ normalInflation A G L K (W.comparisons A G L K) Y =
      normalInflation A G L K (W.comparisons A G L K) X ≫
        (V.invariants A (normalProduct G L)).functor.rightDerivedFunctor.map
          (DerivedCategory.Q.map f)

/-- Addition for the actual composite quotient functor.
Source: sectionwise addition of action maps
(blueprint: lem-sfb-derived-invariants-normal-subgroup-comparison). -/
instance normalTowerAdditive [V : NormalInvariantFamily.{u}] [W : NormalSystem.{u}]
    (A : Ring.{u}) (G L : ProfiniteGrp.{u}) (K : OpenNormalSubgroup G)
    (J : OpenNormalSubgroup (normalQuotient G K)) :
    ((W.quotient A G L K).functor ⋙
      (W.quotient A (normalQuotient G K) L J).functor).Additive := by
  let : (W.quotient A G L K).functor.Additive := (W.quotient A G L K).additive
  let : (W.quotient A (normalQuotient G K) L J).functor.Additive :=
    (W.quotient A (normalQuotient G K) L J).additive
  infer_instance

/-- The ordinary identity of invariants for two successive quotient projections. Its
inclusion is the composite of the two kernel-fixed inclusions.
Source: blueprint paragraph (3), proof step 12
(blueprint: lem-sfb-derived-invariants-normal-subgroup-comparison). -/
def normalTowerOrdinary [V : NormalInvariantFamily.{u}] [W : NormalSystem.{u}]
    (A : Ring.{u}) (G L : ProfiniteGrp.{u}) (K : OpenNormalSubgroup G)
    (J : OpenNormalSubgroup (normalQuotient G K)) :=
  (W.comparisons A G L K).ordinary ≪≫
    Functor.isoWhiskerLeft (W.quotient A G L K).functor
      (W.comparisons A (normalQuotient G K) L J).ordinary ≪≫
    (Functor.associator _ _ _).symm

/-- The composite quotient functor preserves K-injective complexes, with the actual
composition identification on complexes.
Source: Stacks 08BJ, applied twice
(blueprint: lem-sfb-derived-invariants-normal-subgroup-comparison). -/
instance normalTowerPreserves [V : NormalInvariantFamily.{u}] [W : NormalSystem.{u}]
    (A : Ring.{u}) (G L : ProfiniteGrp.{u}) (K : OpenNormalSubgroup G)
    (J : OpenNormalSubgroup (normalQuotient G K)) :
    ((W.quotient A G L K).functor ⋙
      (W.quotient A (normalQuotient G K) L J).functor).PreservesKInjectiveComplexes where
  isKInjective_map X _ := by
    let : (W.quotient A G L K).functor.Additive := (W.quotient A G L K).additive
    let : (W.quotient A (normalQuotient G K) L J).functor.Additive :=
      (W.quotient A (normalQuotient G K) L J).additive
    let : (W.quotient A G L K).functor.PreservesKInjectiveComplexes :=
      (W.quotient A G L K).preserves
    let : (W.quotient A (normalQuotient G K) L J).functor.PreservesKInjectiveComplexes :=
      (W.quotient A (normalQuotient G K) L J).preserves
    let : CochainComplex.IsKInjective
        (((W.quotient A G L K).functor.mapHomologicalComplex (.up ℤ)).obj X) :=
      (W.quotient A G L K).preserves.isKInjective_map X
    let h₂ : CochainComplex.IsKInjective
        (((W.quotient A (normalQuotient G K) L J).functor.mapHomologicalComplex
          (.up ℤ)).obj
            (((W.quotient A G L K).functor.mapHomologicalComplex (.up ℤ)).obj X)) :=
      (W.quotient A (normalQuotient G K) L J).preserves.isKInjective_map _
    exact @CochainComplex.isKInjective_of_iso _ _ _ _ _
      ((Functor.mapHomologicalComplexCompIso
        (F := (W.quotient A G L K).functor)
        (G := (W.quotient A (normalQuotient G K) L J).functor)
        (Iso.refl ((W.quotient A G L K).functor ⋙
          (W.quotient A (normalQuotient G K) L J).functor)) (.up ℤ)).app X) h₂


/-- The canonical comparison for the composite projection and composite invariant
inclusion. It derives their ordinary identity directly, before any reassociation.
Source: blueprint paragraph (3), proof step 12
(blueprint: lem-sfb-derived-invariants-normal-subgroup-comparison). -/
def normalTowerComparison [V : NormalInvariantFamily.{u}] [W : NormalSystem.{u}]
    (A : Ring.{u}) (G L : ProfiniteGrp.{u}) (K : OpenNormalSubgroup G)
    (J : OpenNormalSubgroup (normalQuotient G K)) :=
  letI : (W.quotient A G L K).functor.Additive := (W.quotient A G L K).additive
  letI : (W.quotient A (normalQuotient G K) L J).functor.Additive :=
    (W.quotient A (normalQuotient G K) L J).additive
  letI := normalTowerAdditive A G L K J
  letI := normalTowerPreserves A G L K J
  Functor.rightDerivedFunctorNatIso (normalTowerOrdinary A G L K J) ≪≫
    Functor.rightDerivedFunctorCompIso
      ((W.quotient A G L K).functor ⋙ (W.quotient A (normalQuotient G K) L J).functor)
      (V.invariants A (normalProduct (normalQuotient (normalQuotient G K) J) L)).functor

/-- Inflation attached directly to the composite quotient projection. Its source is
written with successive complexes and transported by the canonical composition iso.
Source: blueprint paragraph (3), proof step 13
(blueprint: lem-sfb-derived-invariants-normal-subgroup-comparison). -/
def normalTowerInflation [V : NormalInvariantFamily.{u}] [W : NormalSystem.{u}]
    (A : Ring.{u}) (G L : ProfiniteGrp.{u}) (K : OpenNormalSubgroup G)
    (J : OpenNormalSubgroup (normalQuotient G K))
    (X : CochainComplex (ActionModule A.toMon (G × L)) ℤ) :=
  letI : (W.quotient A G L K).functor.Additive := (W.quotient A G L K).additive
  letI : (W.quotient A (normalQuotient G K) L J).functor.Additive :=
    (W.quotient A (normalQuotient G K) L J).additive
  letI := normalTowerAdditive A G L K J
  letI := normalTowerPreserves A G L K J
  (V.invariants A
      (normalProduct (normalQuotient (normalQuotient G K) J) L)).functor.rightDerivedFunctor.map
      (DerivedCategory.Q.map
        ((Functor.mapHomologicalComplexCompIso
          (Iso.refl ((W.quotient A G L K).functor ⋙
            (W.quotient A (normalQuotient G K) L J).functor)) (.up ℤ)).hom.app X)) ≫
    (V.invariants A
      (normalProduct (normalQuotient (normalQuotient G K) J) L)).functor.rightDerivedFunctor.map
      (normalResolutionUnit
        ((W.quotient A G L K).functor ⋙
          (W.quotient A (normalQuotient G K) L J).functor) X) ≫
    (normalTowerComparison A G L K J).inv.app (DerivedCategory.Q.obj X)

/-- The comparison and actual inflation arrow respect successive quotient projections.
Source: blueprint paragraph (3), proof steps 12 and 13
(blueprint: lem-sfb-derived-invariants-normal-subgroup-comparison). -/
def NormalTowerCompatible [V : NormalInvariantFamily.{u}] [W : NormalSystem.{u}]
    (A : Ring.{u}) (G L : ProfiniteGrp.{u}) (K : OpenNormalSubgroup G)
    (J : OpenNormalSubgroup (normalQuotient G K)) : Prop :=
  letI : (W.quotient A G L K).functor.Additive := (W.quotient A G L K).additive
  letI : (W.quotient A (normalQuotient G K) L J).functor.Additive :=
    (W.quotient A (normalQuotient G K) L J).additive
  letI := normalTowerAdditive A G L K J
  (∀ N : DerivedCategory (ActionModule A.toMon (G × L)),
    (normalTowerComparison A G L K J).hom.app N ≫
      (V.invariants A
      (normalProduct (normalQuotient (normalQuotient G K) J) L)).functor.rightDerivedFunctor.map
        ((Functor.rightDerivedFunctorCompIso
          (W.quotient A G L K).functor
          (W.quotient A (normalQuotient G K) L J).functor).hom.app N) =
    (normalComparison A G L K (W.comparisons A G L K)).hom.app N ≫
      (normalComparison A (normalQuotient G K) L J
        (W.comparisons A (normalQuotient G K) L J)).hom.app
          ((W.quotient A G L K).functor.rightDerivedFunctor.obj N)) ∧
  ∀ X : CochainComplex (ActionModule A.toMon (G × L)) ℤ,
    normalTowerInflation A G L K J X =
      normalInflation A (normalQuotient G K) L J
          (W.comparisons A (normalQuotient G K) L J)
          (((W.quotient A G L K).functor.mapHomologicalComplex (.up ℤ)).obj X) ≫
        normalInflation A G L K (W.comparisons A G L K) X

/-- The composition comparison is the conjugate of the identity of exact inflation
functors under the specified normalized derived adjunctions.
Source: Stacks 09T5 and 0D6E; blueprint paragraph (3)
(blueprint: lem-sfb-derived-invariants-normal-subgroup-comparison). -/
def NormalAdjunctionNormalized [V : NormalInvariantFamily.{u}] [W : NormalSystem.{u}]
    (A : Ring.{u}) (G L : ProfiniteGrp.{u}) (K : OpenNormalSubgroup G) : Prop :=
  normalComparison A G L K (W.comparisons A G L K) =
    conjugateIsoEquiv
      (V.invariants A (normalProduct G L)).adjunction.mapDerivedCategoryRightDerivedAdjunction
      ((V.invariants A
        (normalProduct
          (normalQuotient G K) L)).adjunction.mapDerivedCategoryRightDerivedAdjunction.comp
        (W.quotient A G L K).adjunction.mapDerivedCategoryRightDerivedAdjunction)
      (normalDerivedInflationIso A G L K (W.comparisons A G L K))

/-- With trivial kernel, the invariant inclusion and the resolution unit are invertible;
they are the evident identifications with the original object. The two comparisons above
are fixed by those identifications and by the normalized derived units.
Source: blueprint paragraph (3), proof step 14
(blueprint: lem-sfb-derived-invariants-normal-subgroup-comparison). -/
def NormalTrivialKernel [V : NormalInvariantFamily.{u}] [W : NormalSystem.{u}]
    (A : Ring.{u}) (G L : ProfiniteGrp.{u}) (K : OpenNormalSubgroup G) : Prop :=
  Subsingleton K.toSubgroup → IsIso (W.quotient A G L K).inclusion ∧
    ∀ X : CochainComplex (ActionModule A.toMon (G × L)) ℤ,
      IsIso (normalResolutionUnit (W.quotient A G L K).functor X)

end Profinite.CondensedAction

namespace Profinite.CondensedAction

/-- The complete normal-subgroup assertion. Categorical structures and invariants are
existential conclusions. Coefficients range over all commutative condensed rings, not
only those arising from a topological ring; the change squares include nonflat maps.
Source: blueprint paragraph (3)
(blueprint: lem-sfb-derived-invariants-normal-subgroup-comparison). -/
def NormalAssertion : Prop :=
  ∃ C : NormalComparisonCategories.{u},
    letI : NormalComparisonCategories.{u} := C
    ∃ V : NormalInvariantFamily.{u},
      letI : NormalInvariantFamily.{u} := V
      ∃ W : NormalSystem.{u},
        letI : NormalSystem.{u} := W
        ∃ H : NormalKernelPreserves.{u},
          letI : NormalKernelPreserves.{u} := H
          ∃ S : NormalScalars.{u},
            letI : NormalScalars.{u} := S
            (∀ (A : Ring.{u}) (G L : ProfiniteGrp.{u}) (K : OpenNormalSubgroup G),
              NormalInflationEquation A G L K ∧ NormalBetaUnit A G L K ∧
              NormalInflationResolution A G L K ∧ NormalInflationNatural A G L K ∧
              NormalAdjunctionNormalized A G L K ∧ NormalTrivialKernel A G L K ∧
              ∀ J : OpenNormalSubgroup (normalQuotient G K), NormalTowerCompatible A G L K J) ∧
            (∀ (A B : Ring.{u}) (a : B ⟶ A) (G L L' : ProfiniteGrp.{u})
              (K : OpenNormalSubgroup G) (h : L' →ₜ* L),
              ∃ e : NormalChangeData A B a G L L' K h,
                NormalChangeCompatible e ∧ NormalBetaCompatible e ∧ NormalInflationCompatible e) ∧
            ∀ (A B : Ring.{u}) (a : B ⟶ A) (G L : ProfiniteGrp.{u}) (K : OpenNormalSubgroup G),
              ∃ e : NormalChangeData A B a G L L K (ContinuousMonoidHom.id L),
                NormalChangeCompatible e ∧ NormalBetaCompatible e ∧ NormalInflationCompatible e ∧
                IsIso e.derivedTotal ∧ IsIso e.derivedOuter ∧ IsIso e.derivedQuotient ∧
                IsIso e.derivedKernel

/-- Normalized unbounded derived invariants for an open normal subgroup, over every
commutative condensed ring. The structures in NormalAssertion are conclusions, not
additional assumptions on the coefficients or action categories.

Source: literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/
sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability-direct-images.proof.md, paragraph (3);
Stacks Tags 03DA, 03DB, 03EW, 07A5, 08BJ, 070I, 070Y, 070K, 09T5, and 0D6E.

Proof (the detailed fourteen-step proof recorded in the DAG):

1. Apply the internal action-site presentation with the sheaf of groups $S\mapsto C(S,P)$ and
the trivial action on $A$, for each $P=1,K,G\times L,Q\times L$. Its small ringed action site
presents $\mathcal A_P(A)$ as a module-sheaf category. The ringed-site Grothendieck theorem
therefore makes all these categories Grothendieck abelian. The presentation creates kernels and
cokernels after forgetting actions. Changing an action by precomposition leaves the underlying
module and its morphisms unchanged, so restriction, inflation and forgetting are additive and
exact. These assertions also hold after a change of coefficient ring: scalar restriction leaves
the underlying abelian sheaf, its kernels, and its sheaf-cokernels unchanged.

2. The disjoint open cosets of $K$ cover compact $G$, so a finite subcover exhausts them. Choose
one representative of each of the finitely many cosets of the open subgroup $K$ in $G$. This
gives a continuous set section $s:Q\to G$. Define $T(M)$ by the sections fixed by $K$ after
every profinite base change. The condition is local and preserved by restriction, so this is an
internal submodule. Normality makes it $G\times L$-stable: $k(gm)=g((g^{-1}kg)m)=gm$. Every map
into $Q\times L$ lifts using $(s,1_L)$, so its action on these sections is independent of the
lift and defines the residual condensed $Q\times L$-action. A map from an inflated module lands
in $T(M)$, since its source is $K$-fixed; conversely the invariant inclusion makes every map
into $T(M)$ equivariant after inflation. These inverse operations give precisely the normalized
adjunction. Applying the same fixed-section definition gives the identity $\Gamma_{G\times
L}=\Gamma_{Q\times L}T$ on objects and maps, since every $(g,l)$ is a lift of $(\bar g,l)$ and
the kernel is $K$.

3. Put $P=G\times L$ and identify $H=K\times\{1\}$ with $K$. The coset space $P/H$ is $Q\times
L$; $(q,l)\mapsto(s(q),l)$ is a continuous section of its projection. The exact condensed
induction lemma supplies an exact left adjoint to $\operatorname{Res}_K:\mathcal A_{G\times
L}(A)\to\mathcal A_K(A)$, without requiring $L$ finite. Consequently restriction to $K$
preserves K-injective complexes by the exact-left-adjoint criterion. The same criterion applied
to exact quotient inflation shows that $T$ preserves K-injectives. Applied to exact trivial
inflation, it also shows that every invariants functor $\Gamma_P$ carries K-injectives to
K-injectives.

4. There are enough K-injectives by the Grothendieck K-injective theorem. In the exact-square
comparison theorem take $H'=T$, $H=\Gamma_K$, $r=\operatorname{Res}_K$, and $s=U_{Q\times L}$.
The square $sH'=Hr$ is the fixed-section identity, and $r$ is exact and preserves K-injectives
by step 3. Its normalized isomorphism is the required $\beta:D(U_{Q\times L})RT\cong R\Gamma_K
D(\operatorname{Res}_K)$. Explicitly, on a resolution $N\to I$ both sides are represented by the
identical complex $(I|_K)^K=U(TI)$; the comparison is its identity. This also fixes the
comparison independently of all choices.

5. Apply the normalized derived adjunction-composition theorem to the exact trivial inflation
from $\mathcal A_1(A)$ to $\mathcal A_{Q\times L}(A)$, followed by exact quotient inflation to
$\mathcal A_{G\times L}(A)$. Their composite is trivial inflation to $G\times L$, and step 2
identifies the conjugate right adjoints by $\Gamma_{G\times L}=\Gamma_{Q\times L}T$, with the
specified invariant inclusions. The theorem gives $c:R\Gamma_{G\times L}\cong R\Gamma_{Q\times
L}RT$ as the conjugate of this exact inflation identity. On a K-injective $I$, the intermediate
$TI$ is K-injective by step 3, so $c$ is represented by the identity $I^{G\times
L}=(TI)^{Q\times L}$. Thus it has precisely the required adjunction normalization.

6. For a module $N$, choose a K-injective resolution $i:N[0]\to I$ in the action category. The
unit of $RT$ is represented by $T(i):T(N)[0]\to TI$. The first comparison of step 4 takes its
underlying map to $(i|_K)^K$, which is the usual invariant-to-derived-invariant map, since
$I|_K$ is K-injective. Let $a:T(N)[0]\to J$ be a K-injective resolution in the quotient-action
category. As $TI$ is K-injective, precomposition with $a$ gives a bijection of homotopy classes
of maps into $TI$. Hence there is a unique homotopy class $b:J\to TI$ with $ba=T(i)$. Applying
quotient invariants represents $R\Gamma_{Q\times L}(\eta_N)$ by $\Gamma_{Q\times L}(b)$.

7. Under the normalized inflation adjunction, $b:J\to TI$ transposes to the chain map from the
inflation of $J$ into $I$ obtained by composing with $TI\hookrightarrow I$. On invariant
complexes its map is exactly $\Gamma_{Q\times L}(b):J^{Q\times L}\to I^{G\times L}$, using
$I^{G\times L}=(TI)^{Q\times L}$. This is the derived inflation attached to the projection and
the original inclusion $\operatorname{Inf}T(N)\hookrightarrow N$: its composite with the
inflated resolution map agrees up to homotopy with $i$ composed with that inclusion, by
$ba=T(i)$. Since $c_N$ is the identity on the target invariant complex, this gives
$c_N\operatorname{inf}_N=R\Gamma_{Q\times L}(\eta_N)$. The Hom bijection in step 6 and the
derived adjunction normalization show that this description is independent of $i,a,b$.

8. For a morphism of complexes, maps between K-injective resolutions representing it are unique
up to homotopy, by the K-injective Hom bijection. Applying $T$, restriction and invariants
preserves homotopies. The identities of fixed-section submodules in steps 2, 4 and 5 commute
with every equivariant linear map. Thus $\beta,c,\eta$ and the displayed inflation equation are
natural in module maps (and $\beta,c$ are natural on the unbounded derived category). In later
steps, equality of natural derived maps may be checked on K-injectives: every object is
isomorphic to one, and their derived Hom sets equal their homotopy Hom sets.

9. For a continuous $h:L'\to L$, write $r_h$ for action restriction and use the analogous
quotient restriction. There is an equality $T' r_h=r_hT$ of underlying invariant submodules with
residual action. Full invariants have the natural inclusion $M^{G\times L}\to(r_hM)^{G\times
L'}$, and likewise for $Q$; the $K$-invariant submodule itself is unchanged. To derive these
maps on a K-injective source $I$, resolve $r_hI\to J$ in the new action category and apply these
inclusions followed by the corresponding invariant map to $J$. The target $T'J$ and $J|_K$ are
K-injective by step 3 for $L'$. All paths through $\beta$ or $c$ are therefore the same maps of
invariant complexes: use $I^{G\times L}=(TI)^{Q\times L}$, then $T'(r_hI)\to T'J$. This proves
the two naturality squares and, with $T(N)\to TI$, the inflation equation after $h$. Resolution-
independence follows from the Hom bijection; no preservation of K-injectives by $r_h$ is
asserted.

10. Use the action sites also for sheaves of sets: the same formulas as in the action-site
presentation identify a $P$-set sheaf $X$ with the sheaf having restriction $x\mapsto a f^*x$
along $(f,a)$. Restricting to $(f,1)$ is the inverse; twisting by $(1,a)$ is invertible, so the
covering-sieve criterion in that presentation identifies the two sheaf conditions. Thus the
category $B_P$ of internal $P$-set sheaves is a small-site topos. Inflation along $P\to1$ or
$G\times L\to Q\times L$ preserves finite limits, computed on underlying sheaves, and is left
adjoint to kernel invariants by the fixed-section formulas of step 2 (with sets in place of
modules). These are geometric morphisms; with the trivially acted-on ring $A$ their module
direct images are $\Gamma_P$ and $T$. A ring map $A\to A'$ is a ringed-topos morphism on the
identity underlying $B_P$, with exact module direct image scalar restriction $r_P$. For either
projection $f:B_P\to B_R$, the two composites of the coefficient-change and projection morphisms
agree, since the ring structural map is the same $A\to A'$. The ringed-topos composition theorem
gives the canonical isomorphism $$\theta_f:Rf_{*,A}D(r_P)\xrightarrow{\sim}D(r_R)Rf_{*,A'}.$$
Indeed composition identifies both sides with the direct image of that common composite. Its
normalization says: for $A'$-K-injective $I'$ and a resolution $a:r_PI'\to J$ over $A$, the map
$f_{*,A}(a)$ from $r_R f_{*,A'}I'$ to $f_{*,A}J$ is a quasi-isomorphism and represents
$\theta_f^{-1}$. Thus no scalar restriction is assumed to preserve K-injectives.

11. Let $\sigma:A\to A'$ and $v:N\to r_{G\times L}N'$ be an equivariant coefficient map. The
required coefficient transformation for invariants is explicitly $R\Gamma_A(v)$ followed by
$\theta_\Gamma$ of step 10; it derives the equality of invariants with scalar restriction. Use
the analogous $\theta_T$ for $T$. On an $A'$-K-injective $I'$ choose $a:rI'\to J$ over $A$. The
inverses of all these coefficient comparisons are represented by the invariant maps of $a$. The
square for $\beta$ is the single map $(rI')^K\to J^K$, since $T_A(a)$ has that underlying map
and $J|_K$ is K-injective. The square for $c$ is the single map $(rI')^{G\times L}\to J^{G\times
L}$, written also as quotient invariants of $T_A(a)$. The ringed-topos composition cocycle
states exactly that resolving after either of these two factorizations gives the same canonical
comparison, including coefficient changes on identity topoi. Its unit normalization agrees with
the normalization in step 5, so these are the specified $c,\theta$ rather than arbitrary
isomorphisms. Naturality of the derived unit for $N'[0]\to I'$ gives the same square for $\eta$;
composing the original invariant inclusions with $a$ gives it for inflation by step 7. Finally
compose with $R\Gamma_A(v)$. This proves every coefficient square for arbitrary $v$, without a
flatness assumption on $A'$ over $A$.

12. Consider successive quotient projections $P_0\to P_1\to P_2$ with open normal kernels,
retaining any factor $L$. Write $T_1,T_2$ for their invariant functors. A section is fixed by
the composite kernel exactly when it is $\ker(P_0\to P_1)$-fixed and its residual section is
$\ker(P_1\to P_2)$-fixed; quotient maps have the continuous set sections used in step 2.
Consequently $T_{02}=T_2T_1$ and the invariant inclusion for the composite is the composite of
the two inclusions. For a K-injective resolution $N\to I$, both $T_1I$ and $T_2T_1I$ are
K-injective. The derived composition comparisons, in either parenthesization, are the identity
on $I^{P_0}=(T_1I)^{P_1}=(T_2T_1I)^{P_2}$, by their adjunction-normalization theorem. Step 8
extends this equality to all derived objects.

13. To check inflation itself under those projections, resolve $T_1N\to J$ in the $P_1$-action
category and extend $T_1(N\to I)$ to $b:J\to T_1I$ using the Hom bijection. Resolve $T_2T_1N\to
Z$ in the $P_2$-action category. Extend $T_2(T_1N\to J)$ to $d:Z\to T_2J$; this is possible
because $T_2J$ is K-injective. The map $T_2(b)d:Z\to T_2T_1I$ extends $T_2T_1(N\to I)$. The
direct inflation uses the unique homotopy class with exactly this extension property, so it
agrees with $T_2(b)d$. Taking $P_2$-invariants identifies this map with the composite of the two
inflations, since the invariant inclusions compose as in step 12. This proves the asserted
transitivity, including its actual arrow.

14. If $K=1$, the quotient is $G$, $T$ is the identity functor, and $\Gamma_K$ is the identity
on underlying modules. Its derived unit is the class of a quasi-isomorphism $N\to I$, hence is
the identity under the exact-functor resolution identifications. The termwise fixed-section
identities defining $\beta$ and $c$ are identities too, so their normalized derived comparisons
are identities under the same identifications. The zero ring, zero module, $K=G$, and trivial
$L$ require no changes: all constructions are submodules, exact adjunctions and resolutions,
with no division by a group order.

(blueprint: lem-sfb-derived-invariants-normal-subgroup-comparison). -/
theorem normal_subgroup_comparison : NormalAssertion.{u} := by
  sorry


end Profinite.CondensedAction
