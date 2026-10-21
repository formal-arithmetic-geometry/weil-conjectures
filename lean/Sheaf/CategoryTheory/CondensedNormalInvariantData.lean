module

public import Sheaf.CategoryTheory.CondensedActionModule
public import Sheaf.Topology.ProfiniteCondensedRing
public import Sheaf.CategoryTheory.CondensedEquivariantBarData
public import Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions
public import Mathlib.Topology.Algebra.Category.ProfiniteGrp.Basic
public import Mathlib.Topology.Algebra.OpenSubgroup
public import Mathlib.Topology.Algebra.Group.Quotient
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedComp


/-! # Normalized derived invariants through an open normal subgroup

Source: blueprint direct-image stability, paragraph (3)
(blueprint: def-sfb-normal-invariant-comparison-data).

## Main definitions

* NormalSystem retains normalized fixed-section invariant and quotient data.
* normalBeta and normalComparison are the canonical derived comparison constructions.
* The resolution predicates record their unit and invariant-inclusion normalizations.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.CondensedBar (Ring ScalarAction ActionAbelian)
namespace Profinite.CondensedAction

/-- The abelian structures use the recorded addition of equivariant maps.
Source: blueprint paragraph (3)
(blueprint: def-sfb-normal-invariant-comparison-data). -/
class NormalComparisonCategories where
  actionAbelian : ∀ (A : Ring.{u}) (P : Type u) [Group P] [TopologicalSpace P]
    [IsTopologicalGroup P] [CompactSpace P] [T2Space P] [TotallyDisconnectedSpace P],
    ActionAbelian A P
  grothendieck : ∀ (A : Ring.{u}) (P : Type u) [Group P] [TopologicalSpace P]
    [IsTopologicalGroup P] [CompactSpace P] [T2Space P] [TotallyDisconnectedSpace P],
    @IsGrothendieckAbelian.{u + 1} (ActionModule A.toMon P) _
      (@CategoryTheory.CondensedBar.actionAbelian A P _ _ _ (actionAbelian A P))
  derived : ∀ (A : Ring.{u}) (P : Type u) [Group P] [TopologicalSpace P]
    [IsTopologicalGroup P] [CompactSpace P] [T2Space P] [TotallyDisconnectedSpace P],
    @HasDerivedCategory.{u + 2} (ActionModule A.toMon P) _
      (@CategoryTheory.CondensedBar.actionAbelian A P _ _ _ (actionAbelian A P))
  moduleDerived : ∀ A : Ring.{u}, HasDerivedCategory.{u + 2} (Modules A.toMon)

attribute [instance] NormalComparisonCategories.actionAbelian
attribute [instance] NormalComparisonCategories.grothendieck

variable [C : NormalComparisonCategories.{u}]

/-- The chosen localization in the fixed larger universe.
Source: blueprint universe convention
(blueprint: def-sfb-normal-invariant-comparison-data). -/
instance normalComparisonDerived (A : Ring.{u}) (P : Type u) [Group P]
    [TopologicalSpace P] [IsTopologicalGroup P] [CompactSpace P] [T2Space P]
    [TotallyDisconnectedSpace P] :
    HasDerivedCategory.{u + 2} (ActionModule A.toMon P) :=
  C.derived A P

/-- The chosen nonequivariant localization.
Source: blueprint universe convention
(blueprint: def-sfb-normal-invariant-comparison-data). -/
instance normalComparisonModuleDerived (A : Ring.{u}) :
    HasDerivedCategory.{u + 2} (Modules A.toMon) := C.moduleDerived A

/-- Product with its actual product topology and group law.
Source: blueprint paragraph (3)
(blueprint: def-sfb-normal-invariant-comparison-data). -/
abbrev normalProduct (P Q : ProfiniteGrp.{u}) : ProfiniteGrp.{u} :=
  ProfiniteGrp.of (P × Q)

/-- The actual subgroup with its induced profinite topology.
Source: blueprint paragraph (3)
(blueprint: def-sfb-normal-invariant-comparison-data). -/
def normalKernel (G : ProfiniteGrp.{u}) (K : OpenNormalSubgroup G) : ProfiniteGrp.{u} :=
  letI : CompactSpace K.toSubgroup :=
    isCompact_iff_compactSpace.mp K.toOpenSubgroup.isClosed.isCompact
  ProfiniteGrp.of K.toSubgroup

/-- The ordinary quotient, finite and discrete because K is open.
Source: blueprint paragraph (3)
(blueprint: def-sfb-normal-invariant-comparison-data). -/
abbrev normalQuotient (G : ProfiniteGrp.{u}) (K : OpenNormalSubgroup G) : ProfiniteGrp.{u} :=
  ProfiniteGrp.of (G ⧸ K.toSubgroup)

/-- Quotient projection on the first factor and identity on the second.
Source: blueprint paragraph (3)
(blueprint: def-sfb-normal-invariant-comparison-data). -/
def normalProjection (G : ProfiniteGrp.{u}) (K : OpenNormalSubgroup G)
    (L : ProfiniteGrp.{u}) : (G × L) →ₜ* ((G ⧸ K.toSubgroup) × L) :=
  ContinuousMonoidHom.prodMap
    ⟨QuotientGroup.mk' K.toSubgroup, QuotientGroup.continuous_mk⟩
    (ContinuousMonoidHom.id L)

/-- Inclusion of the kernel in the product, k ↦ (k,1).
Source: blueprint paragraph (3)
(blueprint: def-sfb-normal-invariant-comparison-data). -/
def normalKernelInclusion (G : ProfiniteGrp.{u}) (K : OpenNormalSubgroup G)
    (L : ProfiniteGrp.{u}) : normalKernel G K →ₜ* (G × L) :=
  { toMonoidHom := K.toSubgroup.subtype.prod (1 : K.toSubgroup →* L)
    continuous_toFun := continuous_subtype_val.prodMk continuous_const }

/-- The canonical resolution unit expressed in the category of complexes.
Source: Stacks Tags 070K and 070Y
(blueprint: def-sfb-normal-invariant-comparison-data). -/
def normalResolutionUnit {C D : Type (u + 2)} [Category.{u + 1} C]
    [Category.{u + 1} D] [Abelian C] [Abelian D]
    [HasDerivedCategory.{u + 2} C] [HasDerivedCategory.{u + 2} D]
    [Abelian.HasKInjectiveResolutions C] (F : C ⥤ D) [F.Additive]
    (I : CochainComplex C ℤ) :
    DerivedCategory.Q.obj ((F.mapHomologicalComplex (.up ℤ)).obj I) ⟶
      F.rightDerivedFunctor.obj (DerivedCategory.Q.obj I) :=
  (DerivedCategory.quotientCompQhIso D).inv.app _ ≫
    DerivedCategory.Qh.map ((F.mapHomotopyCategoryFactors (.up ℤ)).inv.app I) ≫
    F.rightDerivedFunctorUnit.app ((HomotopyCategory.quotient C (.up ℤ)).obj I) ≫
    F.rightDerivedFunctor.map ((DerivedCategory.quotientCompQhIso C).hom.app I)

/-- Ordinary exactness is finite-limit and finite-colimit preservation.
Source: the internal action-site presentation
(blueprint: def-sfb-normal-invariant-comparison-data). -/
class NormalExact {C D : Type (u + 2)} [Category.{u + 1} C]
    [Category.{u + 1} D] [Preadditive C] [Preadditive D] (F : C ⥤ D) : Prop where
  additive : F.Additive
  limits : PreservesFiniteLimits F
  colimits : PreservesFiniteColimits F

attribute [instance] NormalExact.additive NormalExact.limits NormalExact.colimits

/-- The canonical derived transformation of an ordinary square with exact vertical
functors, obtained by the universal derived unit. This works even when r does not
preserve K-injectives. Source: Stacks 070K and 070Y
(blueprint: def-sfb-normal-invariant-comparison-data). -/
def normalSquare {C D C' D' : Type (u + 2)}
    [Category.{u + 1} C] [Category.{u + 1} D]
    [Category.{u + 1} C'] [Category.{u + 1} D']
    [Abelian C] [Abelian D] [Abelian C'] [Abelian D']
    [HasDerivedCategory.{u + 2} C] [HasDerivedCategory.{u + 2} D]
    [HasDerivedCategory.{u + 2} C'] [HasDerivedCategory.{u + 2} D']
    [Abelian.HasKInjectiveResolutions C] [Abelian.HasKInjectiveResolutions C']
    (F : C ⥤ D) (F' : C' ⥤ D') [F.Additive] [F'.Additive]
    (r : C ⥤ C') (s : D ⥤ D') [NormalExact r] [NormalExact s]
    (t : F ⋙ s ⟶ r ⋙ F') :
    F.rightDerivedFunctor ⋙ s.mapDerivedCategory ⟶
      r.mapDerivedCategory ⋙ F'.rightDerivedFunctor :=
  (F.rightDerivedFunctor ⋙ s.mapDerivedCategory).rightDerivedDesc
    (Functor.rightDerivedFunctorCompMapDerivedCategoryUnit F s)
    (HomotopyCategory.quasiIso C (.up ℤ))
    (r.mapDerivedCategory ⋙ F'.rightDerivedFunctor)
    (Functor.whiskerRight (NatTrans.mapHomotopyCategory t (.up ℤ)) DerivedCategory.Qh ≫
      Functor.mapDerivedCategoryCompRightDerivedFunctorUnit r F')

/-- Exact functors compose with the ordinary composite additive structure.
Source: elementary functoriality of kernels and cokernels
(blueprint: def-sfb-normal-invariant-comparison-data). -/
instance normalExactComp {C D E : Type (u + 2)} [Category.{u + 1} C]
    [Category.{u + 1} D] [Category.{u + 1} E]
    [Preadditive C] [Preadditive D] [Preadditive E]
    (F : C ⥤ D) (H : D ⥤ E) [NormalExact F] [NormalExact H] : NormalExact (F ⋙ H) where
  additive := inferInstance
  limits := comp_preservesFiniteLimits F H
  colimits := comp_preservesFiniteColimits F H

/-- Normalized full invariants for every profinite group, and exact action restrictions.
Source: blueprint paragraph (3)
(blueprint: def-sfb-normal-invariant-comparison-data). -/
class NormalInvariantFamily where
  invariants : ∀ (A : Ring.{u}) (P : ProfiniteGrp.{u}), Invariants A.toMon P
  forgetExact : ∀ (A : Ring.{u}) (P : Type u) [Group P] [TopologicalSpace P]
    [IsTopologicalGroup P] [CompactSpace P] [T2Space P] [TotallyDisconnectedSpace P],
    NormalExact (forgetAction (R := A.toMon) (P := P))
  restrictExact : ∀ (A : Ring.{u}) (P Q : Type u) [Group P] [TopologicalSpace P]
    [IsTopologicalGroup P] [CompactSpace P] [T2Space P] [TotallyDisconnectedSpace P]
    [Group Q] [TopologicalSpace Q] [IsTopologicalGroup Q] [CompactSpace Q]
    [T2Space Q] [TotallyDisconnectedSpace Q] (h : P →ₜ* Q),
    NormalExact (inflate (R := A.toMon) h)
  trivialExact : ∀ (A : Ring.{u}) (P : Type u) [Group P] [TopologicalSpace P]
    [IsTopologicalGroup P] [CompactSpace P] [T2Space P] [TotallyDisconnectedSpace P],
    NormalExact (trivial (R := A.toMon) (P := P))

attribute [instance] Invariants.additive
attribute [instance] NormalInvariantFamily.forgetExact
attribute [instance] NormalInvariantFamily.restrictExact
attribute [instance] NormalInvariantFamily.trivialExact

/-- Kernel-fixed sections with their quotient action and the normalized inflation adjunction.
Source: blueprint paragraph (3), fixed-section construction
(blueprint: def-sfb-normal-invariant-comparison-data). -/
class NormalQuotient (A : Ring.{u}) (G L : ProfiniteGrp.{u})
    (K : OpenNormalSubgroup G) where
  functor : ActionModule A.toMon (G × L) ⥤
    ActionModule A.toMon ((G ⧸ K.toSubgroup) × L)
  [additive : functor.Additive]
  preserves : functor.PreservesKInjectiveComplexes
  inclusion : functor ⋙ forgetAction ⟶ forgetAction
  adjunction : inflate (R := A.toMon) (normalProjection G K L) ⊣ functor
  injective : ∀ (N : ActionModule A.toMon (G × L)) (S : Profinite.{u}),
    Function.Injective (((inclusion.app N).hom.hom.app (op S)).hom)
  image : ∀ (N : ActionModule A.toMon (G × L)) (S : Profinite.{u})
    (m : sectionModule A.toMon N.module S),
    (∃ x : sectionModule A.toMon (functor.obj N).module S,
      ((inclusion.app N).hom.hom.app (op S)).hom x = m) ↔
        Fixed N (normalProjection G K L) S m
  residual : ∀ (N : ActionModule A.toMon (G × L)) (S : Profinite.{u})
    (g : C(S, G × L)) (m : sectionModule A.toMon (functor.obj N).module S),
    ((inclusion.app N).hom.hom.app (op S)).hom
      ((functor.obj N).act S ((normalProjection G K L).toContinuousMap.comp g) m) =
    N.act S g (((inclusion.app N).hom.hom.app (op S)).hom m)
  transpose : ∀ (M : ActionModule A.toMon ((G ⧸ K.toSubgroup) × L))
    (N : ActionModule A.toMon (G × L))
    (f : (inflate (R := A.toMon) (normalProjection G K L)).obj M ⟶ N),
    (adjunction.homEquiv M N f).val ≫ inclusion.app N = f.val
  untranspose : ∀ (M : ActionModule A.toMon ((G ⧸ K.toSubgroup) × L))
    (N : ActionModule A.toMon (G × L)) (f : M ⟶ functor.obj N),
    ((adjunction.homEquiv M N).symm f).val = f.val ≫ inclusion.app N

attribute [instance] NormalQuotient.additive NormalQuotient.preserves

/-- A full-invariant comparison with kernel invariants; its ordinary normalization retains
exactly the same section map. The derived comparison is normalized by the composite unit.
Source: Stacks 09T5 and blueprint paragraph (3)
(blueprint: def-sfb-normal-invariant-comparison-data). -/
structure NormalDerivedComparison [V : NormalInvariantFamily.{u}] (A : Ring.{u})
    (G L : ProfiniteGrp.{u}) (K : OpenNormalSubgroup G)
    [T : NormalQuotient A G L K] where
  leftInflation : trivial (R := A.toMon) (P := (G ⧸ K.toSubgroup) × L) ⋙
      inflate (R := A.toMon) (normalProjection G K L) ≅
    trivial (R := A.toMon) (P := G × L)
  leftInflation_identity : ∀ M : Modules A.toMon,
    (leftInflation.hom.app M).val = 𝟙 M
  ordinary : (V.invariants A (normalProduct G L)).functor ≅
    T.functor ⋙ (V.invariants A (normalProduct (normalQuotient G K) L)).functor
  ordinary_inclusion : ∀ N,
    ordinary.hom.app N ≫ (V.invariants A (normalProduct (normalQuotient G K) L)).inclusion.app
      (T.functor.obj N) ≫ T.inclusion.app N =
        (V.invariants A (normalProduct G L)).inclusion.app N
  kernel : T.functor ⋙ forgetAction ≅
    inflate (R := A.toMon) (normalKernelInclusion G K L) ⋙
      (V.invariants A (normalKernel G K)).functor
  kernel_inclusion : ∀ N,
    kernel.hom.app N ≫ (V.invariants A (normalKernel G K)).inclusion.app
      ((inflate (R := A.toMon) (normalKernelInclusion G K L)).obj N) = T.inclusion.app N

/-- The canonical descent of the normalized identity of exact left inflation functors.
It is the inverse composition identification followed by the descent of leftInflation.
Source: Stacks 09T5 and 0D6E; blueprint paragraph (3)
(blueprint: def-sfb-normal-invariant-comparison-data). -/
def normalDerivedInflationIso [V : NormalInvariantFamily.{u}] (A : Ring.{u})
    (G L : ProfiniteGrp.{u}) (K : OpenNormalSubgroup G)
    [T : NormalQuotient A G L K] (d : NormalDerivedComparison A G L K) :
    (trivial (R := A.toMon) (P := (G ⧸ K.toSubgroup) × L)).mapDerivedCategory ⋙
        (inflate (R := A.toMon) (normalProjection G K L)).mapDerivedCategory ≅
      (trivial (R := A.toMon) (P := G × L)).mapDerivedCategory :=
  (Functor.mapDerivedCategoryCompIso
    (trivial (R := A.toMon) (P := (G ⧸ K.toSubgroup) × L))
    (inflate (R := A.toMon) (normalProjection G K L))).symm ≪≫
      Functor.mapDerivedCategoryNatIso d.leftInflation

/-- Canonical derived composition, obtained by deriving the ordinary invariant identity
and the K-injective composition unit, not by selecting an unspecified isomorphism.
Source: Stacks 09T5 and 0D6E
(blueprint: def-sfb-normal-invariant-comparison-data). -/
def normalComparison [V : NormalInvariantFamily.{u}] (A : Ring.{u})
    (G L : ProfiniteGrp.{u}) (K : OpenNormalSubgroup G)
    [T : NormalQuotient A G L K] (d : NormalDerivedComparison A G L K) :
    (V.invariants A (normalProduct G L)).functor.rightDerivedFunctor ≅
      T.functor.rightDerivedFunctor ⋙
        (V.invariants A (normalProduct (normalQuotient G K) L)).functor.rightDerivedFunctor :=
  (Functor.rightDerivedFunctorCompIso' T.functor
    (V.invariants A (normalProduct (normalQuotient G K) L)).functor d.ordinary.symm).symm

/-- Exact restriction to K preserves K-injectives because split-coset induction is exact.
Source: Stacks 08BJ and blueprint paragraph (3)
(blueprint: def-sfb-normal-invariant-comparison-data). -/
class NormalKernelPreserves [V : NormalInvariantFamily.{u}] where
  preserves : ∀ (A : Ring.{u}) (G L : ProfiniteGrp.{u}) (K : OpenNormalSubgroup G),
    (inflate (R := A.toMon) (normalKernelInclusion G K L)).PreservesKInjectiveComplexes

attribute [instance] NormalKernelPreserves.preserves

/-- Forgetting residual actions identifies RT with derived K-invariants by the canonical
exact-square comparison. It is the identity on the invariant complex of a resolution.
Source: Stacks 070I and 070Y
(blueprint: def-sfb-normal-invariant-comparison-data). -/
def normalBeta [V : NormalInvariantFamily.{u}] [NormalKernelPreserves.{u}] (A : Ring.{u})
    (G L : ProfiniteGrp.{u}) (K : OpenNormalSubgroup G)
    [T : NormalQuotient A G L K] (d : NormalDerivedComparison A G L K) :
    T.functor.rightDerivedFunctor ⋙
        (forgetAction (R := A.toMon) (P := (G ⧸ K.toSubgroup) × L)).mapDerivedCategory ≅
      (inflate (R := A.toMon) (normalKernelInclusion G K L)).mapDerivedCategory ⋙
        (V.invariants A (normalKernel G K)).functor.rightDerivedFunctor :=
  (Functor.rightDerivedFunctorCompMapDerivedCategoryIso T.functor forgetAction).symm ≪≫
    Functor.rightDerivedFunctorNatIso d.kernel ≪≫
    Functor.mapDerivedCategoryCompRightDerivedFunctorIso
      (inflate (R := A.toMon) (normalKernelInclusion G K L))
      (V.invariants A (normalKernel G K)).functor

/-- Derived inflation is the inverse composition comparison after the derived invariant
unit. The normalized composition construction fixes this as the derived adjunction arrow
attached to the invariant inclusion, including its degree-zero specialization.
Source: blueprint paragraph (3), Stacks 070I and 09T5
(blueprint: def-sfb-normal-invariant-comparison-data). -/
def normalInflation [V : NormalInvariantFamily.{u}] (A : Ring.{u})
    (G L : ProfiniteGrp.{u}) (K : OpenNormalSubgroup G)
    [T : NormalQuotient A G L K] (d : NormalDerivedComparison A G L K)
    (I : CochainComplex (ActionModule A.toMon (G × L)) ℤ) :
    (V.invariants A (normalProduct (normalQuotient G K) L)).functor.rightDerivedFunctor.obj
        (DerivedCategory.Q.obj ((T.functor.mapHomologicalComplex (.up ℤ)).obj I)) ⟶
      (V.invariants A (normalProduct G L)).functor.rightDerivedFunctor.obj
        (DerivedCategory.Q.obj I) :=
  (V.invariants A (normalProduct (normalQuotient G K) L)).functor.rightDerivedFunctor.map
      (normalResolutionUnit T.functor I) ≫
    (normalComparison A G L K d).inv.app (DerivedCategory.Q.obj I)

/-- A simultaneous choice of normalized quotient comparisons; every choice is pinned by
its inclusions and the canonical right-derived construction.
Source: blueprint paragraph (3)
(blueprint: def-sfb-normal-invariant-comparison-data). -/
class NormalSystem [V : NormalInvariantFamily.{u}] where
  quotient : ∀ (A : Ring.{u}) (G L : ProfiniteGrp.{u}) (K : OpenNormalSubgroup G),
    NormalQuotient A G L K
  comparisons : ∀ (A : Ring.{u}) (G L : ProfiniteGrp.{u}) (K : OpenNormalSubgroup G),
    @NormalDerivedComparison _ V A G L K (quotient A G L K)

attribute [instance_reducible] NormalSystem.quotient
attribute [instance] NormalSystem.quotient

/-- The unit equation for the actual inflation arrow, including its degree-zero case.
Source: blueprint paragraph (3), displayed inflation identity
(blueprint: def-sfb-normal-invariant-comparison-data). -/
def NormalInflationEquation [V : NormalInvariantFamily.{u}] [W : NormalSystem.{u}]
    (A : Ring.{u}) (G L : ProfiniteGrp.{u}) (K : OpenNormalSubgroup G) : Prop :=
  ∀ X : CochainComplex (ActionModule A.toMon (G × L)) ℤ,
    normalInflation A G L K (W.comparisons A G L K) X ≫
      (normalComparison A G L K (W.comparisons A G L K)).hom.app
        (DerivedCategory.Q.obj X) =
    (V.invariants A (normalProduct (normalQuotient G K) L)).functor.rightDerivedFunctor.map
      (normalResolutionUnit (W.quotient A G L K).functor X)

/-- Under the first comparison the underlying quotient-resolution unit is the usual
kernel-invariant resolution unit, with every exact-functor identification displayed.
Source: blueprint paragraph (3), proof step 6; Stacks 070I and 070Y
(blueprint: def-sfb-normal-invariant-comparison-data). -/
def NormalBetaUnit [V : NormalInvariantFamily.{u}] [W : NormalSystem.{u}]
    [NormalKernelPreserves.{u}] (A : Ring.{u}) (G L : ProfiniteGrp.{u})
    (K : OpenNormalSubgroup G) : Prop :=
  ∀ X : CochainComplex (ActionModule A.toMon (G × L)) ℤ,
    (forgetAction (R := A.toMon) (P := (G ⧸ K.toSubgroup) × L)).mapDerivedCategory.map
        (normalResolutionUnit (W.quotient A G L K).functor X) ≫
      (normalBeta A G L K (W.comparisons A G L K)).hom.app (DerivedCategory.Q.obj X) =
    (forgetAction (R := A.toMon) (P := (G ⧸ K.toSubgroup) × L)).mapDerivedCategoryFactors.hom.app
        (((W.quotient A G L K).functor.mapHomologicalComplex (.up ℤ)).obj X) ≫
      DerivedCategory.Q.map ((Functor.mapHomologicalComplexCompIso
        (F := (W.quotient A G L K).functor)
        (G := forgetAction (R := A.toMon) (P := (G ⧸ K.toSubgroup) × L))
        (Iso.refl _) (.up ℤ)).hom.app X) ≫
      DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex
        (W.comparisons A G L K).kernel.hom (.up ℤ)).app X) ≫
      DerivedCategory.Q.map ((Functor.mapHomologicalComplexCompIso
        (F := inflate (R := A.toMon) (normalKernelInclusion G K L))
        (G := (V.invariants A (normalKernel G K)).functor)
        (Iso.refl _) (.up ℤ)).inv.app X) ≫
      normalResolutionUnit (V.invariants A (normalKernel G K)).functor
        (((inflate (R := A.toMon) (normalKernelInclusion G K L)).mapHomologicalComplex
          (.up ℤ)).obj X) ≫
      (V.invariants A (normalKernel G K)).functor.rightDerivedFunctor.map
        ((inflate (R := A.toMon) (normalKernelInclusion G K L)).mapDerivedCategoryFactors.inv.app
          X)

/-- The resolution formula for inflation: b extends T(i) through a, and the invariant
inclusion transposes b. Equality is imposed only in the derived category, so all
homotopic choices of lift are covered.
Source: blueprint paragraph (3), proof steps 6 and 7; Stacks 070I
(blueprint: def-sfb-normal-invariant-comparison-data). -/
def NormalInflationResolution [V : NormalInvariantFamily.{u}] [W : NormalSystem.{u}]
    (A : Ring.{u}) (G L : ProfiniteGrp.{u}) (K : OpenNormalSubgroup G) : Prop :=
  ∀ (X I : CochainComplex (ActionModule A.toMon (G × L)) ℤ) [I.IsKInjective]
    (i : X ⟶ I) [QuasiIso i]
    (J : CochainComplex (ActionModule A.toMon ((G ⧸ K.toSubgroup) × L)) ℤ)
    [J.IsKInjective]
    (a : ((W.quotient A G L K).functor.mapHomologicalComplex (.up ℤ)).obj X ⟶ J)
    [QuasiIso a]
    (b : J ⟶ ((W.quotient A G L K).functor.mapHomologicalComplex (.up ℤ)).obj I),
    Nonempty (Homotopy (a ≫ b)
      (((W.quotient A G L K).functor.mapHomologicalComplex (.up ℤ)).map i)) →
    normalResolutionUnit
        (V.invariants A (normalProduct (normalQuotient G K) L)).functor J ≫
      (V.invariants A (normalProduct (normalQuotient G K) L)).functor.rightDerivedFunctor.map
        (inv (DerivedCategory.Q.map a)) ≫
      normalInflation A G L K (W.comparisons A G L K) X ≫
      (V.invariants A (normalProduct G L)).functor.rightDerivedFunctor.map
        (DerivedCategory.Q.map i) =
    DerivedCategory.Q.map
      (((V.invariants A (normalProduct (normalQuotient G K) L)).functor.mapHomologicalComplex
        (.up ℤ)).map b) ≫
      DerivedCategory.Q.map ((Functor.mapHomologicalComplexCompIso
        (Iso.refl ((W.quotient A G L K).functor ⋙
          (V.invariants A (normalProduct (normalQuotient G K) L)).functor)) (.up ℤ)).hom.app I) ≫
      DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex
        (W.comparisons A G L K).ordinary.inv (.up ℤ)).app I) ≫
      normalResolutionUnit (V.invariants A (normalProduct G L)).functor I

end Profinite.CondensedAction
