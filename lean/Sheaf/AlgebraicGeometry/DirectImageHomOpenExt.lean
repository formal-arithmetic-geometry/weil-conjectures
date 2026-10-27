/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q128
-/
module
public import Sheaf.AlgebraicGeometry.DirectImageHomComparisonData
import WeilConjectures.AlgebraicGeometry.SingleComplexOpenCounitCompatibility
import WeilConjectures.AlgebraicGeometry.SingleComplexOpenDirectImageUnit
public import WeilConjectures.Topology.OpenModuleDerivedSections
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.ShortExactPullback
public import Sheaf.Algebra.Homology.OrdinaryModuleDerivedInternalHom
import WeilConjectures.Algebra.Homology.HomComplexSectionsCanonicalComparison
public import WeilConjectures.Algebra.Homology.HomComplexComponents
public import Mathlib.AlgebraicGeometry.Scheme
public import WeilConjectures.AlgebraicGeometry.DerivedCategory
public import WeilConjectures.AlgebraicGeometry.SchemeDerivedDirectImage
public import WeilConjectures.AlgebraicGeometry.DerivedDirectImageInternalHom
public import WeilConjectures.AlgebraicGeometry.CanonicalDerivedTensorHom
public import WeilConjectures.AlgebraicGeometry.DerivedOpenRestrictionMaps
public import WeilConjectures.AlgebraicGeometry.SingleComplexOpenRestrictionData
public import WeilConjectures.AlgebraicGeometry.SingleComplexOpenBaseChangeComparisons
import Sheaf.AlgebraicGeometry.RingedSpaceDerivedAdjunctionGeneral
import WeilConjectures.AlgebraicGeometry.DerivedPullbackMonoidalModel
import WeilConjectures.AlgebraicGeometry.DerivedDirectImageOpenRestriction
import WeilConjectures.AlgebraicGeometry.DerivedInternalHomRestrictOpen
import WeilConjectures.AlgebraicGeometry.OpenRestrictionClosedMonoidal
import Sheaf.AlgebraicGeometry.UnboundedDirectImageSectionPresheaf
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.Algebra.Homology.KInjectiveHomComplex
import WeilConjectures.AlgebraicGeometry.GlobalSectionsDirectImageKInjectiveAcyclic
import WeilConjectures.AlgebraicGeometry.TensorPullbackAdjunction
import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.DerivedInternalHomShiftRight
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import Mathlib.Algebra.Homology.DerivedCategory.KInjective
import Mathlib.CategoryTheory.Functor.Derived.Adjunction

/-! # Direct image of internal Hom on open Ext groups

Source: Stacks Project, cohomology.tex, Tags 0B69, 08DK, 08DL, 08FE and 0D5W.
(blueprint: lem-sfb-direct-image-hom-open-ext).

The comparison is reused from the definition interface; open restriction is its evaluation mate.
The open Ext identification is pinned on cycles of the actual sheaf Hom complex. Its
normalization uses the published localization factorization and the right-derived unit,
including when that Hom complex is only sections-acyclic rather than K-injective.
The final theorem includes the derived Leray isomorphism, its unit normalization,
and the all-degree Ext formula. The localization universe for abelian groups is independent.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w wA
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite TopologicalSpace
namespace AlgebraicGeometry
variable [∀ Z : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
variable [HasDerivedCategory.{wA} AddCommGrpCat.{u}]
/-- Abbreviation for the recorded derived internal Hom on the site of opens; no new Hom functor is
chosen.
Source: Stacks Project, cohomology.tex, Tags 0B69, 08DK, 08DL, 08FE and 0D5W.
(blueprint: lem-sfb-direct-image-hom-open-ext). -/
abbrev sfbRHom (X : Scheme.{u}) :=
  derivedInternalHom (Opens.grothendieckTopology X) X.sheaf
/-- Cohomology in integer degree q of the recorded unbounded derived sections functor.
Source: Stacks Project, cohomology.tex, Tags 0B69, 08DK, 08DL, 08FE and 0D5W.
(blueprint: lem-sfb-direct-image-hom-open-ext). -/
abbrev sfbOpenCohomology (X : Scheme.{u}) (V : X.Opens) (q : ℤ) :=
  RingedSpace.openModuleDerivedSections X.toRingedSpace V ⋙
    DerivedCategory.homologyFunctor AddCommGrpCat.{u} q

/-- Canonical internal-Hom restriction map, expressed by pulling back evaluation along the open
immersion and identifying derived pullback with exact restriction. This is the evaluation
transpose of the sectionwise comparison in Tag 08DL.
Source: Stacks Project, cohomology.tex, Tags 0B69, 08DK, 08DL, 08FE and 0D5W.
(blueprint: lem-sfb-direct-image-hom-open-ext). -/
def sfbOpenHomComparison (X : Scheme.{u}) (V : X.Opens)
    (E N : schemeDerivedCategory X) :
    (schemeOpenRestriction X V).mapDerivedCategory.obj ((sfbRHom X).obj (op E, N)) ⟶
      (sfbRHom V.toScheme).obj
        (op ((schemeOpenRestriction X V).mapDerivedCategory.obj E),
          (schemeOpenRestriction X V).mapDerivedCategory.obj N) :=
  (schemeDerivedTensorHomEquiv V.toScheme _ _ _).symm
    (((singleComplexOpenPullbackIso X V).inv.app ((sfbRHom X).obj (op E, N)) ⊗ₘ
        (singleComplexOpenPullbackIso X V).inv.app E) ≫
      (mixedHomTensorPullbackIso V.ι).inv.app ((sfbRHom X).obj (op E, N), E) ≫
      (derivedPullback V.ι).map (schemeDerivedTensorHomEquiv X _ E N (𝟙 _)) ≫
      (singleComplexOpenPullbackIso X V).hom.app N)

/-- Derive the actual section restriction natural transformation between two open evaluations, using
the published total right-derived functor construction.
Source: Stacks Project, cohomology.tex, Tags 0B69, 08DK, 08DL, 08FE and 0D5W.
(blueprint: lem-sfb-direct-image-hom-open-ext). -/
def sfbDerivedSectionsRestriction (X : Scheme.{u}) {W V : X.Opens} (i : W ⟶ V) :
    RingedSpace.openModuleDerivedSections X.toRingedSpace V ⟶
      RingedSpace.openModuleDerivedSections X.toRingedSpace W :=
  Functor.rightDerivedFunctorNatTrans
    (Functor.whiskerLeft (SheafOfModules.forget (moduleRings X.toRingedSpace) ⋙
      PresheafOfModules.toPresheaf (moduleRings X.toRingedSpace).obj)
      ((evaluation (Opens X)ᵒᵖ AddCommGrpCat.{u}).map i.op))

/-- Apply homology to derived section restriction; this is restriction on local hypercohomology.
Source: Stacks Project, cohomology.tex, Tags 0B69, 08DK, 08DL, 08FE and 0D5W.
(blueprint: lem-sfb-direct-image-hom-open-ext). -/
def sfbOpenCohomologyRestriction (X : Scheme.{u}) {W V : X.Opens} (i : W ⟶ V)
    (q : ℤ) : sfbOpenCohomology X V q ⟶ sfbOpenCohomology X W q :=
  Functor.whiskerRight (sfbDerivedSectionsRestriction X i)
    (DerivedCategory.homologyFunctor AddCommGrpCat.{u} q)

/-- Apply exact restriction to a local shifted morphism, then the canonical restriction-composition
and shift comparisons. This is the scheme-open presentation of the existing derived open Hom
restriction.
Source: Stacks Project, cohomology.tex, Tags 0B69, 08DK, 08DL, 08FE and 0D5W.
(blueprint: lem-sfb-direct-image-hom-open-ext). -/
def sfbOpenExtRestriction (X : Scheme.{u}) {W V : X.Opens} (i : W ⟶ V)
    (E N : schemeDerivedCategory X) (q : ℤ)
    (a : (schemeOpenRestriction X V).mapDerivedCategory.obj E ⟶
      ((schemeOpenRestriction X V).mapDerivedCategory.obj N)⟦q⟧) :
    (schemeOpenRestriction X W).mapDerivedCategory.obj E ⟶
      ((schemeOpenRestriction X W).mapDerivedCategory.obj N)⟦q⟧ :=
  (schemeDerivedOpenRestrictionCompIso X i).inv.app E ≫
    (schemeOpenOverlapRestriction X i).mapDerivedCategory.map a ≫
    ((schemeOpenOverlapRestriction X i).mapDerivedCategory.commShiftIso q).hom.app
      ((schemeOpenRestriction X V).mapDerivedCategory.obj N) ≫
    ((schemeDerivedOpenRestrictionCompIso X i).hom.app N)⟦q⟧'

/-- The canonical Leray arrow from derived sections on the inverse image to sections after derived
direct image. Descend the identity of the underived composite using its two right-derived units.
Its inverse, when proved invertible, is the Leray identification of Tag 0D5W.
Source: Stacks Project, cohomology.tex, Tags 0B69, 08DK, 08DL, 08FE and 0D5W.
(blueprint: lem-sfb-direct-image-hom-open-ext). -/
def sfbOpenLerayComparison {X Y : Scheme.{u}} (f : X ⟶ Y) (V : Y.Opens) :
    RingedSpace.openModuleDerivedSections X.toRingedSpace (f ⁻¹ᵁ V) ⟶
      schemeDerivedDirectImage f ⋙ RingedSpace.openModuleDerivedSections Y.toRingedSpace V :=
  Functor.rightDerivedNatTrans _ _
    (RingedSpace.openModuleSections X.toRingedSpace (f ⁻¹ᵁ V)).rightDerivedFunctorUnit
    (Functor.rightDerivedFunctorCompUnit
      (RingedSpace.moduleDirectImage f.toLRSHom.toShHom)
      (RingedSpace.openModuleSections Y.toRingedSpace V))
    (HomotopyCategory.quasiIso _ (.up ℤ)) (𝟙 _)

/-- Abbreviation for the existing functorial K-injective resolution used by derivedInternalHom.
Source: Stacks Project, cohomology.tex, Tags 0B69, 08DK, 08DL, 08FE and 0D5W.
(blueprint: lem-sfb-direct-image-hom-open-ext). -/
abbrev sfbResolution (X : Scheme.{u}) :=
  CochainComplex.kInjectiveResolutionFunctor.{u}
    (SheafOfModules.{u} (moduleRings X.toRingedSpace))

/-- The actual localization factorization of derivedInternalHom at the published functorial
K-injective resolution. No unrelated representative isomorphism is selected.
Source: Stacks Project, cohomology.tex, Tags 0B69, 08DK, 08DL, 08FE and 0D5W.
(blueprint: lem-sfb-direct-image-hom-open-ext). -/
def sfbRHomResolutionIso (X : Scheme.{u})
    (L M : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ) :
    (sfbRHom X).obj (op (DerivedCategory.Q.obj L), DerivedCategory.Q.obj M) ≅
      DerivedCategory.Q.obj (homComplex (R := X.sheaf) L ((sfbResolution X).obj M)) :=
  (Localization.fac _ (derivedInternalHom_inverts _ _ (sfbResolution X)
    (CochainComplex.toKInjectiveResolution.{u} _)
    (fun K ↦ ⟨(CochainComplex.monoQuasiIso_toKInjectiveResolution_app.{u} _ K).2,
      CochainComplex.isKInjective_kInjectiveResolutionFunctor_obj.{u} _ K⟩))
    (DerivedCategory.Q.op.prod DerivedCategory.Q)).app (op L, M)

/-- Termwise sections of Hom(L,I(M)), using the same resolution as the recorded derived Hom.
Source: Stacks Project, cohomology.tex, Tags 0B69, 08DK, 08DL, 08FE and 0D5W.
(blueprint: lem-sfb-direct-image-hom-open-ext). -/
abbrev sfbHomSectionComplex (X : Scheme.{u}) (V : X.Opens)
    (L M : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ) :=
  (RingedSpace.openModuleSections X.toRingedSpace V).mapHomologicalComplex (.up ℤ) |>.obj
    (homComplex (R := X.sheaf) L ((sfbResolution X).obj M))

/-- Send ordinary cohomology of the section complex to hypercohomology by the actual right-derived
unit and localization factorization. This arrow is defined for arbitrary L; its use does not
assume that Hom(L,I(M)) is K-injective.
Source: Stacks Project, cohomology.tex, Tags 0B69, 08DK, 08DL, 08FE and 0D5W.
(blueprint: lem-sfb-direct-image-hom-open-ext). -/
def sfbHomSectionClass (X : Scheme.{u}) (V : X.Opens)
    (L M : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ) (q : ℤ) :
    (sfbHomSectionComplex X V L M).homology q ⟶
      (sfbOpenCohomology X V q).obj
        ((sfbRHom X).obj (op (DerivedCategory.Q.obj L), DerivedCategory.Q.obj M)) :=
  (DerivedCategory.homologyFunctorFactors AddCommGrpCat.{u} q).inv.app _ ≫
    (DerivedCategory.homologyFunctor AddCommGrpCat.{u} q).map
      ((RingedSpace.openModuleSections X.toRingedSpace V).rightDerivedFunctorUnitQ _ ≫
        (RingedSpace.openModuleDerivedSections X.toRingedSpace V).map
          (sfbRHomResolutionIso X L M).inv)

/-- The existing exact restriction on complexes to the slice over an open, used only to specify
cocycle representatives.
Source: Stacks Project, cohomology.tex, Tags 0B69, 08DK, 08DL, 08FE and 0D5W.
(blueprint: lem-sfb-direct-image-hom-open-ext). -/
abbrev sfbSliceComplexRestriction (X : Scheme.{u}) (V : X.Opens) :=
  (SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) V).mapHomologicalComplex
    (.up ℤ)

/-- Localize a cocycle map to the shifted K-injective target, transport through the over-site
equivalence, and invert the localized resolution augmentation. The resulting map has the scheme-
open derived restriction endpoints.
Source: Stacks Project, cohomology.tex, Tags 0B69, 08DK, 08DL, 08FE and 0D5W.
(blueprint: lem-sfb-direct-image-hom-open-ext). -/
def sfbOpenRepresentativeHom (X : Scheme.{u}) (V : X.Opens)
    (L M : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ) (q : ℤ)
    (k : (sfbSliceComplexRestriction X V).obj L ⟶
      ((sfbSliceComplexRestriction X V).obj ((sfbResolution X).obj M))⟦q⟧) :
    (schemeOpenRestriction X V).mapDerivedCategory.obj (DerivedCategory.Q.obj L) ⟶
      ((schemeOpenRestriction X V).mapDerivedCategory.obj (DerivedCategory.Q.obj M))⟦q⟧ :=
  letI : QuasiIso ((CochainComplex.toKInjectiveResolution.{u} _).app M) :=
    (CochainComplex.monoQuasiIso_toKInjectiveResolution_app.{u} _ M).2
  letI : (Equivalence.functor
      (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over V))
      (D := SheafOfModules.{u} (moduleRings V.toScheme.toRingedSpace))
      (Scheme.Modules.overEquiv V)).Additive := Functor.additive_of_preserves_binary_products _
  (schemeOpenRestriction X V).mapDerivedCategoryFactors.hom.app L ≫
    DerivedCategory.Q.map
      (((Equivalence.functor
        (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over V))
        (D := SheafOfModules.{u} (moduleRings V.toScheme.toRingedSpace))
        (Scheme.Modules.overEquiv V)).mapHomologicalComplex (.up ℤ)).map k ≫
      (((Equivalence.functor
        (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over V))
        (D := SheafOfModules.{u} (moduleRings V.toScheme.toRingedSpace))
        (Scheme.Modules.overEquiv V)).mapHomologicalComplex (.up ℤ)).commShiftIso q).hom.app
          ((sfbSliceComplexRestriction X V).obj ((sfbResolution X).obj M))) ≫
    (DerivedCategory.Q.commShiftIso q).hom.app _ ≫
    ((schemeOpenRestriction X V).mapDerivedCategoryFactors.inv.app ((sfbResolution X).obj M))⟦q⟧' ≫
    ((schemeOpenRestriction X V).mapDerivedCategory.map
      (inv (DerivedCategory.Q.map ((CochainComplex.toKInjectiveResolution.{u} _).app M))))⟦q⟧'

/-- Representative normalization of the open Ext identification in Tag 08DK. A cycle z corresponds
to the chain map k precisely when every actual Hom-complex projection is the corresponding
component of k under equivHomShift. Require that its image is exactly the localization of k. The
comparison to hypercohomology is the actual right-derived unit, not an arbitrary additive
equivalence.
Source: Stacks Project, cohomology.tex, Tags 0B69, 08DK, 08DL, 08FE and 0D5W.
(blueprint: lem-sfb-direct-image-hom-open-ext). -/
def sfbIsCanonicalOpenExt (X : Scheme.{u})
    (α : ∀ (E N : schemeDerivedCategory X) (V : X.Opens) (q : ℤ),
      (sfbOpenCohomology X V q).obj ((sfbRHom X).obj (op E, N)) ≃+
        ((schemeOpenRestriction X V).mapDerivedCategory.obj E ⟶
          ((schemeOpenRestriction X V).mapDerivedCategory.obj N)⟦q⟧)) : Prop :=
  ∀ (L M : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    (V : X.Opens) (q : ℤ) (z : (sfbHomSectionComplex X V L M).cycles q)
    (k : (sfbSliceComplexRestriction X V).obj L ⟶
      ((sfbSliceComplexRestriction X V).obj ((sfbResolution X).obj M))⟦q⟧),
    (∀ (p r : ℤ) (h : p + q = r) (W : (Over V)ᵒᵖ),
      (((CochainComplex.HomComplex.Cocycle.equivHomShift k).val.v p r h).val.app W) =
        (((homComplexπ (R := X.sheaf) L ((sfbResolution X).obj M) q p r h).val.app
          (op V)) ((sfbHomSectionComplex X V L M).iCycles q z)).app W) →
    α (DerivedCategory.Q.obj L) (DerivedCategory.Q.obj M) V q
      (sfbHomSectionClass X V L M q ((sfbHomSectionComplex X V L M).homologyπ q z)) =
        sfbOpenRepresentativeHom X V L M q k

/-- Send u to Rg-star(u), then the canonical commShiftIso at its target, for the induced morphism g
on the inverse-image open. This defines the integer-degree pushforward on local derived Hom.
Source: Stacks Project, cohomology.tex, Tags 0B69, 08DK, 08DL, 08FE and 0D5W.
(blueprint: lem-sfb-direct-image-hom-open-ext). -/
def sfbPushforwardOpenExt {X Y : Scheme.{u}} (f : X ⟶ Y) (V : Y.Opens)
    (E N : schemeDerivedCategory X) (q : ℤ)
    (a : (schemeOpenRestriction X (f ⁻¹ᵁ V)).mapDerivedCategory.obj E ⟶
      ((schemeOpenRestriction X (f ⁻¹ᵁ V)).mapDerivedCategory.obj N)⟦q⟧) :
    (schemeDerivedDirectImage (f ∣_ V)).obj
        ((schemeOpenRestriction X (f ⁻¹ᵁ V)).mapDerivedCategory.obj E) ⟶
      ((schemeDerivedDirectImage (f ∣_ V)).obj
        ((schemeOpenRestriction X (f ⁻¹ᵁ V)).mapDerivedCategory.obj N))⟦q⟧ :=
  (schemeDerivedDirectImage (f ∣_ V)).map a ≫
    ((schemeDerivedDirectImage (f ∣_ V)).commShiftIso q).hom.app _

/-- Conjugate a shifted local morphism by the published canonical direct-image open restriction
isomorphisms, shifting the target isomorphism as well. The inverse conjugates by their inverses;
the inverse and additive laws are the category and preadditive laws.
Source: Stacks Project, cohomology.tex, Tags 0B69, 08DK, 08DL, 08FE and 0D5W.
(blueprint: lem-sfb-direct-image-hom-open-ext). -/
def sfbTargetOpenExtEquiv {X Y : Scheme.{u}} (f : X ⟶ Y) (V : Y.Opens)
    (E N : schemeDerivedCategory X) (q : ℤ) :
    (((schemeOpenRestriction Y V).mapDerivedCategory.obj
        ((schemeDerivedDirectImage f).obj E)) ⟶
      ((schemeOpenRestriction Y V).mapDerivedCategory.obj
        ((schemeDerivedDirectImage f).obj N))⟦q⟧) ≃+
    ((schemeDerivedDirectImage (f ∣_ V)).obj
        ((schemeOpenRestriction X (f ⁻¹ᵁ V)).mapDerivedCategory.obj E) ⟶
      ((schemeDerivedDirectImage (f ∣_ V)).obj
        ((schemeOpenRestriction X (f ⁻¹ᵁ V)).mapDerivedCategory.obj N))⟦q⟧) where
  toFun a := (singleComplexOpenDirectImageIso f V).inv.app E ≫ a ≫
    ((singleComplexOpenDirectImageIso f V).hom.app N)⟦q⟧'
  invFun a := (singleComplexOpenDirectImageIso f V).hom.app E ≫ a ≫
    ((singleComplexOpenDirectImageIso f V).inv.app N)⟦q⟧'
  left_inv a := by simp
  right_inv a := by simp
  map_add' a b := by simp [Preadditive.add_comp, Preadditive.comp_add]

/-- The evaluation-mate direct-image comparison restricts canonically to every open and
acts on all integer-degree open Ext groups by derived pushforward with its shift comparison.
The existential comparisons are fixed by their actual localization and derived-unit formulas;
they are not arbitrary isomorphisms. The equations for α and ell include two-variable
naturality and restriction to every smaller open, including successive and empty restrictions.

Source: Stacks Project, cohomology.tex, Tags 0B69, 08DK, 08DL, 08FE and 0D5W.
(blueprint: lem-sfb-direct-image-hom-open-ext).

Proof (the eight steps of the DAG):
1. Write $F=Lf^*$, $G=Rf_*$, $H_T(A,B)=R\mathcal Hom_T(A,B)$, and $e_T$ for the canonical
uncurrying bijection. Let $\varepsilon:FG\to1$ be the pullback/direct-image counit and
$t:F(A\otimes B)\cong FA\otimes FB$ the canonical monoidal comparison. The cited comparison is
characterized as follows: for $a:A\to GH_X(E,N)$ its composite with $c_{E,N}$ uncurries on $Y$ to
the adjoint of $$F(A\otimes GE)\xrightarrow{t}FA\otimes
FGE\xrightarrow{1\otimes\varepsilon_E}FA\otimes
E\xrightarrow{e_X(\operatorname{adj}^{-1}(a))}N.$$ Indeed its evaluation transpose is relative
cup product followed by $G$ of evaluation, as in Tag 0B69. Applying the adjunction formula to
relative cup product gives exactly these three arrows. Thus this formula specifies the already
given canonical comparison, rather than a new choice of it. The monoidal model also supplies the
unit isomorphism $l:F1_Y\cong1_X$ and its unit laws. Uses: lem-pc-sheaf-rhom-projection-formula,
lem-pc-ringed-spaces-derived-adjoint-general, def-pc-canonical-derived-tensor-hom-bijection,
def-pc-derived-pullback-monoidal-model.

2. Let $r_X,r_Y$ be restriction to $U,V$, respectively, and $F_0=Lg^*$, $G_0=Rg_*$. Use the
direct-image restriction isomorphism $r_YG\cong G_0r_X$ and the internal-Hom restriction
isomorphisms. Restrict the three-arrow formula of Step 1. Uncurrying commutes with restriction by
the closed-monoidal restriction statement. For the canonical comparisons here, its equation is
also read directly from the defining componentwise uncurrying: restriction sends $a\otimes
v\mapsto\phi(a)(v)$ to the same formula on the smaller open; the unit map is likewise unchanged.
This pins the comparison to the canonical internal-Hom restriction isomorphism, rather than to
unspecified witnesses. For the middle arrow the cited counit equation is exactly
$$F_0(b_K);\varepsilon_{0,r_XK}=d_{GK};r_X(\varepsilon_K),$$ where $b:r_YG\cong G_0r_X$ and
$d:F_0r_Y\cong r_XF$ are the canonical open comparisons (semicolon means composition in order).
The first arrow also agrees: the monoidal model defines it on every K-flat tensor summand by the
ordinary pullback tensor map, and restricting that map simply restricts both entries and their
coefficients. The last arrow agrees by preservation of uncurrying. Substituting the counit
equation therefore turns the restricted formula into precisely Step 1 for $g,E_U,N_U$.
Injectivity of the adjunction and uncurrying bijections proves $r_Y(c_{E,N})=c^g_{E_U,N_U}$ with
the stated source and target comparisons. Uses: lem-pc-restrict-derived-direct-image-open,
lem-sc-derived-internal-hom-restrict-open, lem-pc-open-restriction-closed-monoidal,
lem-pc-t2-open-counit-compatibility, def-pc-derived-pullback-monoidal-model,
def-pc-canonical-derived-tensor-hom-bijection.

3. The natural Leray isomorphism of abelian presheaves gives $$H^q(V,GH_X(E,N))\cong
H^q(U,H_X(E,N)).$$ Apply the open Ext comparison to the right hand side to get
$\operatorname{Hom}(E_U,N_U[q])$. Apply the same Ext comparison on $Y$ to $(GE,GN)$ to get
$\operatorname{Hom}((GE)_V,(GN)_V[q])$, and then the direct-image restriction isomorphisms to
identify this with $\operatorname{Hom}(G_0E_U,G_0N_U[q])$. These are exactly the two isomorphisms
in the statement; the cited presheaf statements already include all integer degrees, naturality
and smaller-open restriction compatibility. It remains to compute the map under them. Uses:
lem-trf-unbounded-direct-image-section-presheaf, lem-trf-open-ext-hypercohomology-comparison,
lem-pc-restrict-derived-direct-image-open.

4. Fix the canonical degree-zero section convention. For any scheme $T$ and $B\in D(\mathcal
O_T)$, a cycle $s\in\Gamma(T,I(B)^0)$ gives the chain map $1_T[0]\to I(B)$ taking $1$ to $s$.
Boundaries give homotopies, and the K-injective localization bijection identifies its class with
a unique arrow $\gamma_T(B)([s]):1_T\to B$. This defines the canonical section-to-unit-Hom
identification. For its compatibility with open Ext, choose a K-flat representative $P$ of $E$
using the resolution theorem, and a K-injective representative $J$ of $N$. The cited Hom theorem
says $C=\mathcal Hom^\bullet(P,J)$ is K-injective; by the definition it represents $H_T(E,N)$.
Thus a class $x\in H^0(T,H_T(E,N))$ is a global degree-zero cycle $\phi$ of $C$, namely a chain
map $P\to J$. The canonical Ext comparison of Tag 08DK sends $x$ to $u=Q\phi$. Meanwhile
$\gamma_T(H_T(E,N))(x)$ is represented by the map $1_T[0]\to C$ taking $1$ to $\phi$. The
defining componentwise uncurrying equation sends this map on the summand $1_T^0\otimes P^p$ to
$a\otimes v\mapsto a\phi^p(v)$. Consequently $$e_T(\gamma_T(H_T(E,N))(x))=u\circ\lambda_E.$$ All
representatives have the hypotheses required by the cited statements. This computation fixes the
canonical conventions; existence of abstract additive equivalences alone would not fix them.
Uses: def-pc-open-module-derived-sections, lem-weil-pbc-kinjective-hom-derived,
lem-pc-kflat-resolution, lem-pur-hom-kflat-into-kinjective, def-pur-derived-internal-hom,
lem-trf-open-ext-hypercohomology-comparison, def-pc-canonical-derived-tensor-hom-bijection.

5. We spell out the normalization needed in degree zero. For $B\in D(\mathcal O_X)$, let $x\in
H^0(Y,GB)$ correspond by Leray to $y\in H^0(X,B)$. Under the canonical section-to-unit-Hom
identifications, write $a:1_Y\to GB$ and $b:1_X\to B$. Then $$\operatorname{adj}^{-1}(a)=b\circ
l,\qquad a=G(b)\circ\operatorname{adj}(l).$$ Here is a representative check, avoiding any
assertion that $f_*$ preserves K-injectives. Choose a K-injective representative $J$ of $B$. The
cited sections-acyclicity theorem makes $\Gamma(Y,f_*J)=\Gamma(X,J)$ compute both sides of Leray.
A degree-zero cycle $s$ defines the map $1_X[0]\to J$ taking $1$ to $s$; the same cycle on $Y$
defines $1_Y[0]\to f_*J$. Under the ordinary module pullback adjunction the latter transposes to
the former composed with $f^*1_Y\cong1_X$. Localization yields the displayed equation for the
derived adjunction: the unit sheaf in degree zero is K-flat (tensoring with it is the identity),
and the target is K-injective, so the derived adjunction uses this same ordinary chain map.
Boundaries are chain homotopies; the K-injective localization bijection identifies their classes.
Thus this is the canonical Leray comparison, not merely some additive bijection. The
section-to-Hom convention is the explicit canonical one fixed in Step 4. Uses:
def-pc-ringed-spaces-derived-direct-image,
lem-pc-global-sections-direct-image-kinjective-acyclic, lem-weil-pbc-kinjective-hom-derived,
lem-pc-ringed-spaces-derived-adjoint-general, def-pc-derived-pullback-monoidal-model,
def-pc-open-module-derived-sections, lem-pc-module-pullback-adjunction,
lem-sc-derived-adjunction-from-underived, def-pc-kflat-complex.

6. First work over the whole spaces and with $q=0$. Put $B=H_X(E,N)$ and let the class
corresponding to $u:E\to N$ give $b:1_X\to B$ and $a:1_Y\to GB$. By the canonical unit
calculation of Step 4, $$e_X(b)=u\circ\lambda_E,$$ where $\lambda_E:1_X\otimes E\cong E$.
Substitute $\operatorname{adj}^{-1}(a)=b\circ l$ from Step 5 into Step 1. Naturality of
uncurrying and the strong monoidal unit law reduce the adjoint's argument to $$F(1_Y\otimes
GE)\xrightarrow{F\lambda_{GE}}FGE\xrightarrow{\varepsilon_E}E\xrightarrow{u}N.$$ Counit
naturality says $u\circ\varepsilon_E=\varepsilon_N\circ FG(u)$. Since
$\operatorname{adj}(v)=G(v)\circ\eta$ and $G(\varepsilon_E)\circ\eta_{GE}=1_{GE}$, the adjoint of
this composite is $G(u)\circ\lambda_{GE}$. Uncurrying and the canonical unit calculation on $Y$
therefore identify the output with $G(u)$. This calculation uses only the
pullback-left/direct-image-right adjunction; no right adjoint of $G$ occurs. Uses:
def-pc-canonical-derived-tensor-hom-bijection, lem-pc-ringed-spaces-derived-adjoint-general,
def-pc-derived-pullback-monoidal-model.

7. For arbitrary $q\in\mathbf Z$, use $H_X(E,N)[q]\cong H_X(E,N[q])$ and the analogous
isomorphism on $Y$, and $G(N[q])\cong(GN)[q]$. The cited unbounded right-derived functor theorem
supplies the last shift comparison; it applies both to direct image and to derived sections. The
comparison $c$ respects these identifications: in its three-arrow defining formula, shift the
target $N$; evaluation becomes evaluation into $N[q]$, the counit becomes its shifted counit, and
the tensor comparison has unchanged source factors. Equivalently, on the Hom-complex model the
degree-$q$ cocycle is the chain map to the shifted target, so this is the right-shift
internal-Hom comparison. Thus the degree-$q$ map is the degree-zero calculation of Step 6 with
target $N[q]$, followed by $G(N[q])\cong(GN)[q]$. It sends $u:E\to N[q]$ to $G(u)$ with exactly
that shift comparison. Apply this calculation to $g$ and use Steps 2–3 to obtain the claimed
formula over every $V$. Uses: lem-pur-derived-internal-hom-shift-right,
lem-pc-right-derived-functor-triangulated, def-pc-canonical-derived-tensor-hom-bijection,
def-pur-derived-internal-hom, lem-pc-ringed-spaces-derived-adjoint-general.

8. For $t:E'\to E$, $s:N\to N'$ the represented Ext morphism is $s[q]\circ u\circ t$.
Functoriality gives $G_0(s)[q]\circ G_0(u)\circ G_0(t)$ after the natural shift comparison. This
proves the asserted two-variable naturality. For $W\subseteq V$, the presheaf Leray and Ext
comparisons commute with restriction. The direct-image restriction isomorphism is natural in the
arrow $u$, so under those comparisons restricting $Rg_*u$ is exactly
$R(g|_{f^{-1}W})_*(u|_{f^{-1}W})$. For successive restrictions the sectionwise identities
$f^{-1}W\subseteq f^{-1}V$ compose; restriction of a section twice is its direct restriction. The
corresponding canonical derived comparisons are induced by these same identities, hence their
intermediate inverse factors cancel. This gives compatibility with every smaller open, including
identity and empty restrictions. Uses: lem-trf-open-ext-hypercohomology-comparison,
lem-trf-unbounded-direct-image-section-presheaf, lem-pc-restrict-derived-direct-image-open,
def-pc-ringed-spaces-derived-direct-image.
-/
theorem directImageHom_openExt :
    ∃ α : ∀ (X : Scheme.{u}) (E N : schemeDerivedCategory X) (V : X.Opens) (q : ℤ),
      (sfbOpenCohomology X V q).obj ((sfbRHom X).obj (op E, N)) ≃+
        ((schemeOpenRestriction X V).mapDerivedCategory.obj E ⟶
          ((schemeOpenRestriction X V).mapDerivedCategory.obj N)⟦q⟧),
      (∀ X : Scheme.{u}, sfbIsCanonicalOpenExt X (α X)) ∧
      (∀ (X : Scheme.{u}) (E E' N N' : schemeDerivedCategory X)
        (t : E' ⟶ E) (s : N ⟶ N') (V : X.Opens) (q : ℤ)
        (x : (sfbOpenCohomology X V q).obj ((sfbRHom X).obj (op E, N))),
        α X E' N' V q
          ((sfbOpenCohomology X V q).map ((sfbRHom X).map (t.op, s)) x) =
        (schemeOpenRestriction X V).mapDerivedCategory.map t ≫ α X E N V q x ≫
          ((schemeOpenRestriction X V).mapDerivedCategory.map s)⟦q⟧') ∧
      (∀ (X : Scheme.{u}) (E N : schemeDerivedCategory X) {W V : X.Opens}
        (i : W ⟶ V) (q : ℤ)
        (x : (sfbOpenCohomology X V q).obj ((sfbRHom X).obj (op E, N))),
        α X E N W q ((sfbOpenCohomologyRestriction X i q).app _ x) =
          sfbOpenExtRestriction X i E N q (α X E N V q x)) ∧
      ∀ {X Y : Scheme.{u}} (f : X ⟶ Y),
        ∃ ell : ∀ V : Y.Opens,
          RingedSpace.openModuleDerivedSections X.toRingedSpace (f ⁻¹ᵁ V) ≅
            schemeDerivedDirectImage f ⋙
              RingedSpace.openModuleDerivedSections Y.toRingedSpace V,
          (∀ V : Y.Opens, (ell V).hom = sfbOpenLerayComparison f V) ∧
          (∀ {W V : Y.Opens} (i : W ⟶ V) (B : schemeDerivedCategory X),
            (ell V).hom.app B ≫
                (sfbDerivedSectionsRestriction Y i).app ((schemeDerivedDirectImage f).obj B) =
              (sfbDerivedSectionsRestriction X ((Opens.map f.base).map i)).app B ≫
                (ell W).hom.app B) ∧
          (∀ (E N : schemeDerivedCategory X) (V : Y.Opens),
            IsIso (sfbOpenHomComparison X (f ⁻¹ᵁ V) E N) ∧
            IsIso (sfbOpenHomComparison Y V
              ((schemeDerivedDirectImage f).obj E) ((schemeDerivedDirectImage f).obj N)) ∧
            (schemeOpenRestriction Y V).mapDerivedCategory.map
                (sfbDirectImageHomComparison f E N) ≫
                sfbOpenHomComparison Y V
                  ((schemeDerivedDirectImage f).obj E) ((schemeDerivedDirectImage f).obj N) ≫
                (sfbRHom V.toScheme).map
                  (X := (op ((schemeOpenRestriction Y V).mapDerivedCategory.obj
                    ((schemeDerivedDirectImage f).obj E)),
                    (schemeOpenRestriction Y V).mapDerivedCategory.obj
                      ((schemeDerivedDirectImage f).obj N)))
                  (Y := (op ((schemeDerivedDirectImage (f ∣_ V)).obj
                    ((schemeOpenRestriction X (f ⁻¹ᵁ V)).mapDerivedCategory.obj E)),
                    (schemeDerivedDirectImage (f ∣_ V)).obj
                      ((schemeOpenRestriction X (f ⁻¹ᵁ V)).mapDerivedCategory.obj N)))
                  (((singleComplexOpenDirectImageIso f V).inv.app E).op,
                    (singleComplexOpenDirectImageIso f V).hom.app N) =
              (singleComplexOpenDirectImageIso f V).hom.app ((sfbRHom X).obj (op E, N)) ≫
                (schemeDerivedDirectImage (f ∣_ V)).map
                  (sfbOpenHomComparison X (f ⁻¹ᵁ V) E N) ≫
                sfbDirectImageHomComparison (f ∣_ V)
                  ((schemeOpenRestriction X (f ⁻¹ᵁ V)).mapDerivedCategory.obj E)
                  ((schemeOpenRestriction X (f ⁻¹ᵁ V)).mapDerivedCategory.obj N)) ∧
          (∀ (E E' N N' : schemeDerivedCategory X) (t : E' ⟶ E) (s : N ⟶ N'),
            (schemeDerivedDirectImage f).map ((sfbRHom X).map (t.op, s)) ≫
                sfbDirectImageHomComparison f E' N' =
              sfbDirectImageHomComparison f E N ≫
                (sfbRHom Y).map
                  (((schemeDerivedDirectImage f).map t).op, (schemeDerivedDirectImage f).map s)) ∧
          ∀ (E N : schemeDerivedCategory X) (V : Y.Opens) (q : ℤ)
            (x : (sfbOpenCohomology Y V q).obj
              ((schemeDerivedDirectImage f).obj ((sfbRHom X).obj (op E, N)))),
            sfbTargetOpenExtEquiv f V E N q
                (α Y ((schemeDerivedDirectImage f).obj E) ((schemeDerivedDirectImage f).obj N)
                  V q ((sfbOpenCohomology Y V q).map (sfbDirectImageHomComparison f E N) x)) =
              sfbPushforwardOpenExt f V E N q
                (α X E N (f ⁻¹ᵁ V) q
                  ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} q).map
                    ((ell V).inv.app ((sfbRHom X).obj (op E, N))) x)) := by
  sorry
end AlgebraicGeometry
