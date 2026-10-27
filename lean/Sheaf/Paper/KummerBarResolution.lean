/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Sheaf.Paper.KummerResolutionColumns
public import Sheaf.AlgebraicGeometry.CondensedHenselianLisseRigidity
public import Sheaf.Paper.ProfiniteCoefficientLinearization
public import WeilConjectures.CategoryTheory.Monoidal.Mod.Evaluation
import WeilConjectures.CategoryTheory.Monoidal.Mod.Transpose

/-! # Resolved internal bar columns on a stratum
Source: direct-image proof (3), coherent derived internal bar.
(blueprint: def-sfb-kummer-bar-resolution).
-/
@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory Limits Opposite MonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.CondensedRing
open CategoryTheory.CondensedBar
namespace KummerTensorComparison
universe v w
variable {C : Type w} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{v} C]
  [MonoidalCategory C] [MonoidalPreadditive C] [SymmetricCategory C] [MonoidalClosed C]
  {R : C} [MonObj R] [IsCommMonObj R]
open Mod MonObj
/-- The quotient map defining the relative tensor product is linear in its first factor. -/
private noncomputable def relativeTensorπ (M N : Mod C R) :
    (Mod.tensorRight R N.X).obj M ⟶ M ⊗ N :=
  homMk (M := (Mod.tensorRight R N.X).obj M) (N := M ⊗ N) (tensorObjπ M N) (by
    change ((α_ R M.X N.X).inv ≫ γ[R,M.X] ▷ N.X) ≫ tensorObjπ M N =
      R ◁ tensorObjπ M N ≫ γ[R,(M ⊗ N).X]
    simpa only [Category.assoc] using (whiskerLeft_tensorπ_smul M N).symm)

/-- The relative tensor product is a cofork of the two action maps on module objects. -/
private noncomputable def relativeTensorCofork (M N : Mod C R) :
    Cofork ((tensorRightMap R γ[R,N.X]).app M)
      ((tensorRightRightAct R N.X).app M) :=
  Cofork.ofπ (relativeTensorπ M N) (by
    apply Mod.hom_ext
    change M.X ◁ γ[R,N.X] ≫ tensorObjπ M N =
      ((α_ M.X R N.X).inv ≫ rightAct M ▷ N.X) ≫ tensorObjπ M N
    rw [Category.assoc, tensorObjπ_condition]
    simp only [Category.assoc, Iso.inv_hom_id_assoc])

/-- The tensor cofork is a coequalizer, as can be checked after forgetting the module action. -/
private noncomputable def isColimitRelativeTensorCofork (M N : Mod C R) :
    IsColimit (relativeTensorCofork M N) := by
  apply isColimitOfIsColimitCoforkMap (forget R)
  change IsColimit (Cofork.ofπ (tensorObjπ M N) _ :
    Cofork (M.X ◁ γ[R,N.X]) ((α_ M.X R N.X).inv ≫ rightAct M ▷ N.X))
  refine Cofork.IsColimit.mk _
    (fun s ↦ coequalizer.desc (f := rightAct M ▷ N.X)
      (g := (α_ M.X R N.X).hom ≫ M.X ◁ γ[R,N.X]) s.π ?_) ?_ ?_
  · have h := s.condition
    change M.X ◁ γ[R,N.X] ≫ s.π =
      ((α_ M.X R N.X).inv ≫ rightAct M ▷ N.X) ≫ s.π at h
    rw [← cancel_epi (α_ M.X R N.X).inv]
    simpa only [Category.assoc, Iso.inv_hom_id_assoc] using h.symm
  · intro s
    exact coequalizer.π_desc _ _
  · intro s m hm
    apply coequalizer.hom_ext (f := rightAct M ▷ N.X)
      (g := (α_ M.X R N.X).hom ≫ M.X ◁ γ[R,N.X])
    exact hm.trans (coequalizer.π_desc _ _).symm


private noncomputable def tensorComponent (M N : Mod C R) :
    (Mod.tensorLeft N).obj M ≅ M ⊗ N :=
  HasColimit.isoOfNatIso
    (diagramIsoParallelPair ((Mod.tensorLeftDiagram R N).flip.obj M)) ≪≫
      (colimit.isColimit _).coconePointUniqueUpToIso
        (isColimitRelativeTensorCofork M N)

omit [MonoidalPreadditive C] in
private lemma tensorComponent_π (M N : Mod C R) :
    Mod.tensorπ M N ≫ (tensorComponent M N).hom.hom = Mod.tensorObjπ M N := by
  have h := congrArg Mod.Hom.hom
    (show colimit.ι ((Mod.tensorLeftDiagram R N).flip.obj M) WalkingParallelPair.one ≫
        (tensorComponent M N).hom = relativeTensorπ M N by
      simp [tensorComponent, HasColimit.isoOfNatIso_ι_hom_assoc, relativeTensorCofork])
  exact h

private noncomputable def tensorIso (N : Mod C R) :
    Mod.tensorLeft N ≅ MonoidalCategory.tensorRight N :=
  NatIso.ofComponents (fun M ↦ tensorComponent M N) (by
    intro M M' f
    apply Mod.tensorLeft_obj_hom_ext
    simp only [Mod.comp_hom', Mod.tensorπ_map_assoc]
    rw [tensorComponent_π, ← Category.assoc, tensorComponent_π]
    exact (Mod.tensorObjπ_whiskerRight f).symm)

private noncomputable def homAdjunction (M : Mod C R) :
    Mod.tensorLeft M ⊣ CategoryTheory.ihom M :=
  (CategoryTheory.ihom.adjunction M).ofNatIsoLeft
    (tensorIso M ≪≫ (BraidedCategory.tensorLeftIsoTensorRight M).symm).symm

omit [MonoidalPreadditive C] in
private lemma homAdjunction_uncurry (M N P : Mod C R)
    (f : P ⟶ (CategoryTheory.ihom M).obj N) :
    Mod.tensorπ P M ≫ (((homAdjunction M).homEquiv P N).symm f).hom =
      f.hom ▷ M.X ≫ Mod.tensorObjπ ((CategoryTheory.ihom M).obj N) M ≫
        ((β_ ((CategoryTheory.ihom M).obj N) M).hom ≫
          (CategoryTheory.ihom.ev M).app N).hom := by
  rw [Adjunction.homEquiv_counit, Mod.comp_hom', Mod.tensorπ_map_assoc]
  congr 1
  simp only [homAdjunction, Adjunction.ofNatIsoLeft_counit, NatTrans.comp_app,
    Functor.whiskerLeft_app, Iso.symm_inv, Iso.trans_hom, NatTrans.comp_app,
    Mod.comp_hom', Category.assoc]
  change Mod.tensorπ ((CategoryTheory.ihom M).obj N) M ≫
      (tensorComponent ((CategoryTheory.ihom M).obj N) M).hom.hom ≫
        (β_ M ((CategoryTheory.ihom M).obj N)).inv.hom ≫
          ((CategoryTheory.ihom.ev M).app N).hom = _
  rw [← Category.assoc, tensorComponent_π]
  simp only [← SymmetricCategory.braiding_swap_eq_inv_braiding]

end KummerTensorComparison

/-- The two published internal-Hom interfaces are identified by their actual
underlying evaluation maps, using the quotient tensor and its braiding. This unique
normalization excludes an arbitrary automorphism of the internal function object.
Source: tensor-Hom adjunctions in direct-image proof (3)
(blueprint: def-sfb-kummer-bar-resolution).
Proof: both Hom functors are right adjoint to tensoring with the same parameter
module. Identify their tensor products by the unique comparison preserving the
coequalizer quotient. Transport along the symmetry, then apply uniqueness of right
adjoints. The counit equation is exactly the displayed evaluation identity and
also proves uniqueness of the natural isomorphism. -/
theorem kummerInternalHomComparison_existsUnique (A : Ring.{u}) (P : Profinite.{u}) :
    ∃! e : Mod.ihom (freeParameter A P) ≅ CategoryTheory.ihom (freeParameter A P),
      ∀ N : Modules A, Mod.evaluation (freeParameter A P) N =
        MonoidalCategory.whiskerRight (e.hom.app N).hom (freeParameter A P).X ≫
          Mod.tensorObjπ ((CategoryTheory.ihom (freeParameter A P)).obj N)
            (freeParameter A P) ≫
          ((β_ ((CategoryTheory.ihom (freeParameter A P)).obj N) (freeParameter A P)).hom ≫
            (CategoryTheory.ihom.ev (freeParameter A P)).app N).hom := by
  let M := freeParameter A P
  let adj := KummerTensorComparison.homAdjunction M
  let e := (Mod.ihomAdjunction M).rightAdjointUniq adj
  have he (N : Modules A) : Mod.evaluation M N =
      (e.hom.app N).hom ▷ M.X ≫
        Mod.tensorObjπ ((CategoryTheory.ihom M).obj N) M ≫
          ((β_ ((CategoryTheory.ihom M).obj N) M).hom ≫
            (CategoryTheory.ihom.ev M).app N).hom := by
    rw [← KummerTensorComparison.homAdjunction_uncurry]
    rw [Adjunction.homEquiv_symm_rightAdjointUniq_hom_app]
    rfl
  refine ⟨e, he, ?_⟩
  intro e' he'
  apply Iso.ext
  apply NatTrans.ext
  funext N
  apply (adj.homEquiv _ _).symm.injective
  apply Mod.tensorLeft_obj_hom_ext
  rw [KummerTensorComparison.homAdjunction_uncurry,
    KummerTensorComparison.homAdjunction_uncurry]
  exact (he' N).symm.trans (he N)

/-- The unique counit-preserving transport to the existing profinite-function
internal Hom, before deriving. Source: direct-image proof (3), term normalization
(blueprint: def-sfb-kummer-bar-resolution). -/
def kummerInternalHomComparison (A : Ring.{u}) (P : Profinite.{u}) :
    Mod.ihom (freeParameter A P) ≅ CategoryTheory.ihom (freeParameter A P) :=
  (kummerInternalHomComparison_existsUnique A P).choose

/-- Compute the fixed ordinary derived internal Hom by an injective resolution.
Source: direct-image proof (3), ordinary derived internal Hom
(blueprint: def-sfb-kummer-bar-resolution). -/
def kummerHomResolutionIso (A : Ring.{u}) (P : Profinite.{u}) {N : Modules A}
    (J : InjectiveResolution N) :
    (Mod.ihom (freeParameter A P)).rightDerivedFunctor.obj
        ((DerivedCategory.singleFunctor _ 0).obj N) ≅
      DerivedCategory.Q.obj
        (((Mod.ihom (freeParameter A P)).mapHomologicalComplex (.up ℤ)).obj
          J.cochainComplex) := by
  letI : J.cochainComplex.IsKInjective := by
    dsimp only [InjectiveResolution.cochainComplex]
    infer_instance
  exact (Mod.ihom (freeParameter A P)).rightDerivedFunctor.mapIso
      (asIso (DerivedCategory.Q.map J.ι')) ≪≫
    (Mod.ihom (freeParameter A P)).rightDerivedFunctorObjQIso J.cochainComplex

/-- Evaluate a resolved Mod.ihom column by the published profinite-function map,
after the unique evaluation-preserving internal-Hom comparison. This only changes
the resolution presentation of the source; the evaluation arrow is not redefined.
Source: direct-image proof (3), derived column evaluation
(blueprint: def-sfb-kummer-bar-resolution). -/
def kummerHomResolutionEvaluation (A : Ring.{u}) (S : Scheme.{u}) (P : Profinite.{u})
    {N : Modules A} (J : InjectiveResolution N) :
    (derivedFromCondensed A.X S).obj (DerivedCategory.Q.obj
      (((Mod.ihom (freeParameter A P)).mapHomologicalComplex (.up ℤ)).obj
        J.cochainComplex)) ⟶
    (moduleObjectDerivedPushforward A.X (coefficientParameterProjection S P)).obj
      ((derivedFromCondensed A.X (coefficientParameter S P)).obj
        ((DerivedCategory.singleFunctor _ 0).obj N)) :=
  (derivedFromCondensed A.X S).map
    ((kummerHomResolutionIso A P J).inv ≫
      (Functor.rightDerivedFunctorNatIso (kummerInternalHomComparison A P)).hom.app
        ((DerivedCategory.singleFunctor _ 0).obj N)) ≫
    ProfiniteFunctions.comparisonApp A.toMon S P ((DerivedCategory.singleFunctor _ 0).obj N)

variable (A : Ring.{u}) (G : Type u) [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
  [ActionAbelian A G] [IsGrothendieckAbelian.{u + 1} (Equivariant A G)]
  [HasDerivedCategory.{u + 2} (Equivariant A G)]
  [HasDerivedCategory.{u + 2} (Modules A)]

/-- The bar diagram on the explicit functor category. This retains the existing
internal-action bar object and all its maps, without a copied action definition.
Source: direct-image proof (3), compatible bar diagram
(blueprint: def-sfb-kummer-bar-resolution). -/
def kummerExplicitBar (B : Model A G) :
    Equivariant A G ⥤ (SimplexCategory ⥤ Modules A) where
  obj N := B.bar.diagram.obj N
  map f := B.bar.diagram.map f

/-- Additivity follows componentwise from the given bar model.
Source: direct-image proof (3) (blueprint: def-sfb-kummer-bar-resolution).
Proof: evaluate at simplex n and use B.bar.maps_additive; natural transformation
addition is componentwise. -/
theorem kummerExplicitBar_additive (B : Model A G) :
    (kummerExplicitBar A G B).Additive where
  map_add := by
    intro N P f h
    apply NatTrans.ext
    funext n
    exact B.bar.maps_additive f h n.len
attribute [instance] kummerExplicitBar_additive

/-- Exact point pullback of a compatible equivariant bar resolution, still as a
coherent diagram of complexes. Source: direct-image proof (3), whole-stratum model
(blueprint: def-sfb-kummer-bar-resolution). -/
def kummerBarDiagram (B : Model A G) (S : Scheme.{u})
    {N : Equivariant A G} (J : InjectiveResolution N) :
    CochainComplex (SimplexCategory ⥤ KummerModules A.X S) ℕ :=
  (((Functor.whiskeringRight SimplexCategory (Modules A) (KummerModules A.X S)).obj
      ((upperStarFromPoint S).mapMod A.X)).mapHomologicalComplex (.up ℕ)).obj
    (((kummerExplicitBar A G B).mapHomologicalComplex (.up ℕ)).obj J.cocomplex)

/-- Point pullback after the canonical localization transport from the bar model's
larger Hom universe to the published module-derived category.
Source: localization universal property, direct-image proof (3)
(blueprint: def-sfb-kummer-bar-resolution). -/
def kummerPointPullBig (S : Scheme.{u}) :
    DerivedCategory.{u + 2} (Modules A) ⥤ DerivedCategory (KummerModules A.X S) := by
  let bigQ : CochainComplex (Modules A) ℤ ⥤ DerivedCategory.{u + 2} (Modules A) :=
    DerivedCategory.Q
  letI : HasDerivedCategory.{u + 1} (Modules A) :=
    HasDerivedCategory.ofIsGrothendieckAbelian (Modules A)
  exact Localization.lift (DerivedCategory.Q.{u + 1} (C := Modules A))
      (Localization.inverts (DerivedCategory.Q.{u + 1} (C := Modules A))
        (HomologicalComplex.quasiIso (Modules A) (.up ℤ)))
      bigQ ⋙
    derivedFromCondensed A.X S

/-- Restriction of the large-universe point pullback uses the canonical localization
transport and the exact point-pullback comparison.
Source: localization universal property and direct-image proof (3)
(blueprint: def-sfb-kummer-bar-resolution). -/
def kummerPointPullBigPullbackIso {S S' : Scheme.{u}} (f : S' ⟶ S) :
    kummerPointPullBig A S ⋙ (upperStar A.X f).mapDerivedCategory ≅
      kummerPointPullBig A S' := by
  let bigQ : CochainComplex (Modules A) ℤ ⥤ DerivedCategory.{u + 2} (Modules A) :=
    DerivedCategory.Q
  letI : HasDerivedCategory.{u + 1} (Modules A) :=
    HasDerivedCategory.ofIsGrothendieckAbelian (Modules A)
  exact Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft
    (Localization.lift (DerivedCategory.Q.{u + 1} (C := Modules A))
      (Localization.inverts (DerivedCategory.Q.{u + 1} (C := Modules A))
        (HomologicalComplex.quasiIso (Modules A) (.up ℤ))) bigQ)
    (derivedFromCondensedPullbackIso A.X f)

/-- Localization transport preserves the actual complex, followed by exact point
pullback. Source: localization factorization, direct-image proof (3)
(blueprint: def-sfb-kummer-bar-resolution). -/
def kummerPointPullBigFactors (S : Scheme.{u}) :
    DerivedCategory.Q.{u + 2} (C := Modules A) ⋙ kummerPointPullBig A S ≅
      ((upperStarFromPoint S).mapMod A.X).mapHomologicalComplex (.up ℤ) ⋙
        DerivedCategory.Q := by
  let bigQ : CochainComplex (Modules A) ℤ ⥤ DerivedCategory.{u + 2} (Modules A) :=
    DerivedCategory.Q
  letI : HasDerivedCategory.{u + 1} (Modules A) :=
    HasDerivedCategory.ofIsGrothendieckAbelian (Modules A)
  exact Functor.isoWhiskerRight
      (Localization.fac (DerivedCategory.Q.{u + 1} (C := Modules A))
        (Localization.inverts (DerivedCategory.Q.{u + 1} (C := Modules A))
          (HomologicalComplex.quasiIso (Modules A) (.up ℤ))) bigQ)
      (derivedFromCondensed A.X S) ≪≫
    ((upperStarFromPoint S).mapMod A.X).mapDerivedCategoryFactors

/-- The bar resolution retains the actual underlying resolution, term isomorphisms,
and finite-total comparison. Every comparison is fixed on its actual components.
Source: direct-image proof (3), normalized internal bar
(blueprint: def-sfb-kummer-bar-resolution). -/
structure KummerBarResolutionData (B : Model A G) (S : Scheme.{u})
    {N : Equivariant A G} (J : InjectiveResolution N) where
  underlying : InjectiveResolution N.module
  underlyingIso : underlying.cocomplex ≅
    ((forgetAction (A := A) (G := G)).mapHomologicalComplex (.up ℕ)).obj J.cocomplex
  augmentation : (underlying.ι.f 0) ≫ underlyingIso.hom.f 0 = (J.ι.f 0).val
  column : ∀ n : ℕ,
    kummerDiagramColumn A.X S (kummerBarDiagram A G B S J) n ≅
      ((Mod.ihom (freeParameter A (power G n)) ⋙
        (upperStarFromPoint S).mapMod A.X).mapHomologicalComplex (.up ℕ)).obj underlying.cocomplex
  column_components : ∀ (n q : ℕ), (column n).hom.f q =
    ((upperStarFromPoint S).mapMod A.X).map
      ((B.bar.term (J.cocomplex.X q) n).hom ≫
        (B.functions.internalHom (power G n)).hom.app (J.cocomplex.X q).module ≫
        (Mod.ihom (freeParameter A (power G n))).map (underlyingIso.inv.f q))
  total : (kummerDiagramTotal A.X S).obj (kummerBarDiagram A G B S J) ≅
    (((upperStarFromPoint S).mapMod A.X).mapHomologicalComplex (.up ℕ)).obj
      ((totalCochains B.bar).obj J.cocomplex)
  total_components : ∀ (n q r : ℕ) (hnq : n + q = r),
    (HomologicalComplex₂.flip
      (((kummerAlternating A.X S).mapHomologicalComplex (.up ℕ)).obj
        (kummerBarDiagram A G B S J))).ιTotal (.up ℕ) n q r hnq ≫ total.hom.f r =
      ((upperStarFromPoint S).mapMod A.X).map
        ((doubleComplex B.bar J.cocomplex).ιTotal (.up ℕ) n q r hnq)

/-- The resolved bar-column map is the actual internal-Hom parameter evaluation.
All identifications use the recorded term components and the specified injective
resolution; this is a map of derived module sheaves on S.
Source: direct-image proof (3), full cosimplicial term calculation
(blueprint: def-sfb-kummer-bar-resolution). -/
def kummerBarColumnEvaluation (B : Model A G) (S : Scheme.{u})
    {N : Equivariant A G} (J : InjectiveResolution N)
    (d : KummerBarResolutionData A G B S J) (n : ℕ) :
    DerivedCategory.Q.obj
      ((kummerDiagramColumn A.X S (kummerBarDiagram A G B S J) n).extend
        ComplexShape.embeddingUpNat) ⟶
    (moduleObjectDerivedPushforward A.X (coefficientParameterProjection S (power G n))).obj
      ((derivedFromCondensed A.X (coefficientParameter S (power G n))).obj
        ((DerivedCategory.singleFunctor _ 0).obj N.module)) :=
  DerivedCategory.Q.map
      (HomologicalComplex.extendMap (d.column n).hom ComplexShape.embeddingUpNat) ≫
    (DerivedCategory.Q.mapIso
      (HomologicalComplex.mapExtendIso d.underlying.cocomplex ComplexShape.embeddingUpNat
        (Mod.ihom (freeParameter A (power G n)) ⋙
          (upperStarFromPoint S).mapMod A.X))).inv ≫
    (((upperStarFromPoint S).mapMod A.X).mapDerivedCategoryFactors.app
      (((Mod.ihom (freeParameter A (power G n))).mapHomologicalComplex (.up ℤ)).obj
        d.underlying.cochainComplex)).inv ≫
    kummerHomResolutionEvaluation A S (power G n) d.underlying

/-- The comparison from the actual resolved bar total to ordinary derived invariants.
Its invariant augmentation is the one normalized in the existing bar computation.
Source: direct-image proof (3), internal derived bar
(blueprint: def-sfb-kummer-bar-resolution). -/
def kummerBarTotalIso (B : Model A G) (S : Scheme.{u})
    {N : Equivariant A G} (J : InjectiveResolution N)
    (d : KummerBarResolutionData A G B S J) :
    DerivedCategory.Q.obj
        (((kummerDiagramTotal A.X S).obj (kummerBarDiagram A G B S J)).extend
          ComplexShape.embeddingUpNat) ≅
      (kummerPointPullBig A S).obj
        (B.invariants.functor.rightDerivedFunctor.{u + 2, u + 2,
          u + 1, u + 1, u + 2, u + 2}.obj
            ((DerivedCategory.singleFunctor.{u + 2} _ 0).obj N)) :=
  DerivedCategory.Q.mapIso
      ((ComplexShape.embeddingUpNat.extendFunctor _).mapIso d.total) ≪≫
    (DerivedCategory.Q.mapIso
      (HomologicalComplex.mapExtendIso ((totalCochains B.bar).obj J.cocomplex)
        ComplexShape.embeddingUpNat ((upperStarFromPoint S).mapMod A.X))).symm ≪≫
    ((kummerPointPullBigFactors A S).app _).symm ≪≫
    (kummerPointPullBig A S).mapIso (B.computation.iso J).symm

end AlgebraicGeometry.ProEtale.CondensedRing
