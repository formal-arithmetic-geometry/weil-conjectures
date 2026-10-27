module

public import Sheaf.CategoryTheory.CondensedDerivedRestrictionCalculus
public import Sheaf.CategoryTheory.CondensedInflationActionSiteData
public import Sheaf.CategoryTheory.ActionToposGeometricRestriction
public import Sheaf.Algebra.Homology.RingedDerivedClosedSymmetricMonoidal
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Braided

/-! # Native action-site presentation of condensed inflation

Source: blueprint direct-image stability, paragraph (3), internal-action infrastructure;
Stacks 00YV, 06YN, 07A4, 0FPT.
(blueprint: def-sfb-condensed-inflation-native-site-data).

This specification identifies the original internal action category, its tensor and its
ordinary inflation with the independently specified small action-site models.
It introduces no chosen equivalence, derived tensor or pullback.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CondensedBar CategoryTheory.CondensedDerivedRestriction
open Profinite.CondensedAction (trivial)
namespace CategoryTheory.CondensedInflationNormalization
variable (A : CondensedBar.Ring.{u}) (G : Type u) [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G]

/-- The total-complex comparison is identity on every generalized pure-tensor summand.
Source: Stacks 06YN (blueprint: def-sfb-condensed-inflation-native-site-data). -/
def SiteTensorPure (P : ActionSitePresentation A G)
    (comp : ∀ X Y : CochainComplex (Equivariant A G) ℤ,
      (P.actions.functor.mapHomologicalComplex (.up ℤ)).obj (X ⊗ Y) ≅
        siteTotalTensor A G P X Y) : Prop :=
  ∀ (X Y : CochainComplex (Equivariant A G) ℤ) (p q k : ℤ) (h : p + q = k)
      (U : Profinite.CondensedAction.CoherentPresentation.Base.{u})
      (x : CondensedBar.sections A (X.X p).module
        (Profinite.CondensedAction.CoherentPresentation.parameter U))
      (y : CondensedBar.sections A (Y.X q).module
        (Profinite.CondensedAction.CoherentPresentation.parameter U)),
      ((comp X Y).hom.f k).val.app _
          ((P.sections ((X ⊗ Y).X k) U).symm
            (actionTensorGenerator A G X Y p q k h
              (Profinite.CondensedAction.CoherentPresentation.parameter U) x y)) =
        WeilConjectures.coefficientTensorGenerator _ (inflatedRing G P.ring)
          ((P.actions.functor.mapHomologicalComplex (.up ℤ)).obj X)
          ((P.actions.functor.mapHomologicalComplex (.up ℤ)).obj Y) p q k h _
          ((P.sections (X.X p) U).symm x) ((P.sections (Y.X q) U).symm y)

/-- Representative normalization of the site tensor comparison. Each summand is the
identity on the original generalized pure tensors. The derived equation compares the
native ringed tensor with the original action tensor through localization.
Source: Stacks 06YN, 0FPT (blueprint: def-sfb-condensed-inflation-native-site-data). -/
def SiteTensorModel (P : ActionSitePresentation A G)
    [HasDerivedCategory.{u + 1} (siteModules A G P)]
    (S : WeilConjectures.CoefficientClosedStructure
      (CategoryTheory.derivedInternalHomOfUniverses _ (inflatedRing G P.ring)))
    (T : WeilConjectures.CoefficientTensorModels _ (inflatedRing G P.ring) S)
    (b : @SymmetricCategory (DerivedCategory.{u + 1} (siteModules A G P)) _ S.monoidal)
    (c : RingedDerivedTensorCoherence _ (inflatedRing G P.ring) S T b)
    (core : @Functor.CoreMonoidal
      (DerivedCategory.{u + 1} (Equivariant A G)) _ _
      (DerivedCategory.{u + 1} (siteModules A G P)) _ S.monoidal
      P.actions.functor.mapDerivedCategory) : Prop :=
  ∃ comp : ∀ X Y : CochainComplex (Equivariant A G) ℤ,
      (P.actions.functor.mapHomologicalComplex (.up ℤ)).obj (X ⊗ Y) ≅
        siteTotalTensor A G P X Y,
    SiteTensorPure A G P comp ∧
    ∀ (X Y : CochainComplex (Equivariant A G) ℤ),
      (HomologicalComplex.quasiIso (Equivariant A G) (.up ℤ)).kFlat X →
      ∃ h : CochainComplex.IsKFlatIndependentCoefficients
          ((P.actions.functor.mapHomologicalComplex (.up ℤ)).obj X),
        P.actions.functor.mapDerivedCategory.map
            (Functor.LaxMonoidal.μ (DerivedCategory.Q (C := Equivariant A G)) X Y) ≫
            P.actions.functor.mapDerivedCategoryFactors.hom.app (X ⊗ Y) ≫
            DerivedCategory.Q.map (comp X Y).hom ≫
            (c.tensorIso _ _ (Or.inl h)).hom =
          (@Functor.CoreMonoidal.μIso _ _ _ _ _ S.monoidal _ core
            (DerivedCategory.Q.obj X) (DerivedCategory.Q.obj Y)).inv ≫
            (@MonoidalCategory.tensorHom _ _ S.monoidal.toMonoidalCategoryStruct _ _ _ _
              (P.actions.functor.mapDerivedCategoryFactors.hom.app X)
              (P.actions.functor.mapDerivedCategoryFactors.hom.app Y))

/-- Native ringed-site tensor, symmetry and unit agree with the internal action tensor.
The target monoidal structure is required to carry the representative characterizations
of the recorded ringed-derived theorem. In particular it cannot be a monoidal structure
transported from the internal action category merely to force the desired conclusion.
Source: Stacks 0FPT, blueprint paragraph (3)
(blueprint: def-sfb-condensed-inflation-native-site-data). -/
def NativeTensorIdentification (P : ActionSitePresentation A G)
    [HasDerivedCategory.{u + 1} (siteModules A G P)] : Prop :=
  ∃ S : WeilConjectures.CoefficientClosedStructure
      (CategoryTheory.derivedInternalHomOfUniverses
        (InternalActionSite.topology
          (Profinite.CondensedAction.CoherentPresentation.groupPresheaf G)
          Profinite.CondensedAction.CoherentPresentation.baseCoverage) (inflatedRing G P.ring)),
    ∃ T : WeilConjectures.CoefficientTensorModels _ (inflatedRing G P.ring) S,
      ∃ b : @SymmetricCategory (DerivedCategory.{u + 1} (siteModules A G P)) _ S.monoidal,
        ∃ c : RingedDerivedTensorCoherence _ (inflatedRing G P.ring) S T b,
          ∃ core : @Functor.CoreMonoidal
            (DerivedCategory.{u + 1} (Equivariant A G)) _ _
            (DerivedCategory.{u + 1} (siteModules A G P)) _ S.monoidal
            P.actions.functor.mapDerivedCategory,
            SiteTensorModel A G P S T b c core ∧
            (∀ M N : DerivedCategory.{u + 1} (Equivariant A G),
              (@Functor.CoreMonoidal.μIso _ _ _ _ _ S.monoidal _ core M N).inv ≫
                  (b.toBraidedCategory.braiding
                    (P.actions.functor.mapDerivedCategory.obj M)
                    (P.actions.functor.mapDerivedCategory.obj N)).hom =
                P.actions.functor.mapDerivedCategory.map
                    (((DerivedCategory.braidedCategory' (Equivariant A G)).braiding M N).hom) ≫
                  (@Functor.CoreMonoidal.μIso _ _ _ _ _ S.monoidal _ core N M).inv) ∧
            (∃ e : P.actions.functor.mapDerivedCategory.obj (coefficient A G) ≅
                DerivedCategory.Q.obj (ringedTensorUnitComplex _ (inflatedRing G P.ring)),
              (@Functor.CoreMonoidal.εIso _ _ _ _ _ S.monoidal _ core).hom ≫
                  P.actions.functor.mapDerivedCategory.map (actionUnitIso A G).hom ≫ e.hom =
                c.unitIso.hom)

end CategoryTheory.CondensedInflationNormalization
