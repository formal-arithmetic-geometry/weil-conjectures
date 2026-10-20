/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N1
-/
module

public import Sheaf.Paper.AdicHeartIntrinsicFibres
public import Sheaf.AlgebraicGeometry.ProEtaleSiteComparison
public import Sheaf.AlgebraicGeometry.PointedEtaleStalk
public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful

public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Sheaf.Paper.CompletedIntegralConstantMapOfUniverses
public import Sheaf.Paper.IntegralTStructure
public import Sheaf.Paper.IntegralUniformCoefficient
public import Sheaf.Paper.PbcRationalCategory
public import Sheaf.AlgebraicGeometry.FiniteLocallyClosedStratification
public import Sheaf.CategoryTheory.RingedSiteModules
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.Finiteness.Defs
import Sheaf.Paper.PurIntegralTwistLineInverseImage
import Sheaf.AlgebraicGeometry.FiniteTypeFibreDimensionBound
import Sheaf.Paper.IntegralStratifiedPerfectCharacterization
import Sheaf.AlgebraicGeometry.ProEtaleImmersionLimitPreservation
import Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import Sheaf.Paper.CompletedConstantSheafReduction
import Sheaf.Paper.ConstantModuleSectionProperties
import Sheaf.NumberTheory.Padics.ExtensionIntegersDvr
import Sheaf.Paper.FiniteRingConstructibleSheafOrigin
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import Sheaf.AlgebraicGeometry.ProEtaleSiteComparisonFiniteLevel
import Sheaf.AlgebraicGeometry.SupportComparisonPullbackCoherence
import Sheaf.AlgebraicGeometry.ProEtaleFiniteLocalSystemsTwist
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Stalk
import WeilConjectures.AlgebraicGeometry.ConstantSheafGeometricStalk
import Sheaf.NumberTheory.Padics.AdicLimitFiniteModules
import Sheaf.AlgebraicGeometry.ProEtaleComparisonStalk
import Sheaf.CategoryTheory.SiteCoveringAxioms
import Sheaf.AlgebraicGeometry.ProEtaleInverseImageStalk
import Sheaf.AlgebraicGeometry.ProEtaleConstantSheafStalk
import Sheaf.Paper.ContinuousRationalDerivedRealization
import Mathlib.Topology.Algebra.Valued.LocallyCompact
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import WeilConjectures.AlgebraicGeometry.Sites.StrictHenselization

/-! # Ordinary integral constructible quotients and their adic fibres

Source: Bhatt--Scholze, Definition 6.8.10, Proposition 6.8.11(3), Lemmas 5.1.2,
5.1.4 and 6.8.2, Propositions 6.8.4(1) and 6.8.14(2)
(blueprint: lem-a1-integral-constructible-reduction-fibres).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Scheme.A1Integral

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (T : Scheme.{u})

/-- Degree-zero sheaves whose single complex belongs to the recorded integral category.
Source: BS 6.8.10--6.8.11 (blueprint: lem-a1-integral-constructible-reduction-fibres).
This is the sheaf presentation of the standard integral heart. -/
abbrev Heart := ObjectProperty.FullSubcategory
  (fun M : pbcModules T (pbcAdicCompletion T (pbcIntegralDatum l E)) =>
    PbcIsBoundedConstructibleComplete T (pbcIntegralDatum l E)
      ((DerivedCategory.singleFunctor _ 0).obj M))

/-- Place a heart sheaf in degree zero, retaining all compatible-origin conditions.
Source: BS 6.8.11(3) (blueprint: lem-a1-integral-constructible-reduction-fibres). -/
def toIntegral : Heart l E T ⥤ PbcBoundedConstructibleComplete T (pbcIntegralDatum l E) where
  obj M := ⟨(DerivedCategory.singleFunctor _ 0).obj M.obj, M.property⟩
  map f := ObjectProperty.homMk ((DerivedCategory.singleFunctor _ 0).map f.hom)

/-- The sheaf underlying an integral heart object.
Source: BS 6.8.10 (blueprint: lem-a1-integral-constructible-reduction-fibres). -/
abbrev underlying := ObjectProperty.ι
  (fun M : pbcModules T (pbcAdicCompletion T (pbcIntegralDatum l E)) =>
    PbcIsBoundedConstructibleComplete T (pbcIntegralDatum l E)
      ((DerivedCategory.singleFunctor _ 0).obj M))

/-- Scalar restriction along the actual compatible constant sections.
Source: BS 6.8.2 (blueprint: lem-a1-integral-constructible-reduction-fibres). -/
def scalarData (M : pbcModules T (pbcAdicCompletion T (pbcIntegralDatum l E))) :=
  (PresheafOfModules.restrictScalars
    (adicLisseConstantUnit T (PbcIntegralRing l E) ≫
      Functor.whiskerRight (pbcCompletedScalar T (pbcIntegralDatum l E)).hom
        (forget₂ CommRingCat RingCat))).obj M.val

/-- Identity law for the constant-scalar presentation.
Source: BS 6.8.2 (blueprint: lem-a1-integral-constructible-reduction-fibres).
Proof: evaluate the identity law of the restricted presheaf on each section;
the constant ring restriction is the identity. -/
theorem scalarData_map_id
    (M : pbcModules T (pbcAdicCompletion T (pbcIntegralDatum l E))) (U : T.ProEtᵒᵖ) :
    ((scalarData l E T M).map (𝟙 U) :
      (scalarData l E T M).obj U ⟶ (scalarData l E T M).obj U) = 𝟙 _ := by
  sorry

/-- Composition law for the constant-scalar presentation.
Source: BS 6.8.2 (blueprint: lem-a1-integral-constructible-reduction-fibres).
Proof: evaluate the presheaf composition law on each section; restrictions of
constant scalars are identities, so the scalar-restriction comparisons disappear. -/
theorem scalarData_map_comp
    (M : pbcModules T (pbcAdicCompletion T (pbcIntegralDatum l E)))
    {U V W : T.ProEtᵒᵖ} (f : U ⟶ V) (g : V ⟶ W) :
    ((scalarData l E T M).map (f ≫ g) :
      (scalarData l E T M).obj U ⟶ (scalarData l E T M).obj W) =
        (scalarData l E T M).map f ≫ (scalarData l E T M).map g := by
  sorry

/-- Ordinary sections and restrictions with their fixed constant-scalar action.
Source: BS 6.8.2 (blueprint: lem-a1-integral-constructible-reduction-fibres). -/
def scalarPresheaf (M : pbcModules T (pbcAdicCompletion T (pbcIntegralDatum l E))) :
    T.ProEtᵒᵖ ⥤ ModuleCat.{u + 1} (PbcIntegralRing l E) where
  obj := (scalarData l E T M).obj
  map := fun f ↦ (scalarData l E T M).map f
  map_id := scalarData_map_id l E T M
  map_comp := scalarData_map_comp l E T M

/-- Naturality of the same section maps after constant scalar restriction.
Source: BS 6.8.2 (blueprint: lem-a1-integral-constructible-reduction-fibres).
Proof: evaluate naturality of the original module morphism on a section. Restriction
of scalars retains its underlying map and the original restriction maps. -/
theorem scalarMap_naturality
    {M N : pbcModules T (pbcAdicCompletion T (pbcIntegralDatum l E))} (f : M ⟶ N)
    {U V : T.ProEtᵒᵖ} (g : U ⟶ V) :
    (scalarPresheaf l E T M).map g ≫
        (ModuleCat.restrictScalars
          (pbcCompletedSection T (pbcIntegralDatum l E) V)).map (f.val.app V) =
      (ModuleCat.restrictScalars
          (pbcCompletedSection T (pbcIntegralDatum l E) U)).map (f.val.app U) ≫
        (scalarPresheaf l E T N).map g := by
  sorry

/-- Ordinary coefficient restriction, retaining the original sections and maps.
Source: BS 6.8.2 (blueprint: lem-a1-integral-constructible-reduction-fibres). -/
def scalars : pbcModules T (pbcAdicCompletion T (pbcIntegralDatum l E)) ⥤
    Sheaf (ProEt.topology T) (ModuleCat.{u + 1} (PbcIntegralRing l E)) where
  obj M := ⟨scalarPresheaf l E T M,
    Presheaf.isSheaf_of_isSheaf_comp _ _
      (forget₂ (ModuleCat.{u + 1} (PbcIntegralRing l E)) AddCommGrpCat.{u + 1}) M.isSheaf⟩
  map f := { hom :=
    { app := fun U ↦ (ModuleCat.restrictScalars
        (pbcCompletedSection T (pbcIntegralDatum l E) U)).map (f.val.app U)
      naturality := fun _ _ g ↦ scalarMap_naturality l E T f g } }

/-- The ordinary quotient functor, computed in completed-coefficient module sheaves.
It is the cokernel of multiplication, without a derived tensor product.
Source: BS 6.8.10 (blueprint: lem-a1-integral-constructible-reduction-fibres). -/
def quotient (n : ℕ) : pbcModules T (pbcAdicCompletion T (pbcIntegralDatum l E)) ⥤
    pbcModules T (pbcAdicCompletion T (pbcIntegralDatum l E)) :=
  cokernel ((pbcUniformizer l E) ^ (n + 1) • 𝟙
    (𝟭 (pbcModules T (pbcAdicCompletion T (pbcIntegralDatum l E)))))

/-- The actual cokernel projection, natural in every sheaf map.
Source: BS 6.8.10 (blueprint: lem-a1-integral-constructible-reduction-fibres). -/
def quotientProjection (n : ℕ) :
    𝟭 (pbcModules T (pbcAdicCompletion T (pbcIntegralDatum l E))) ⟶ quotient l E T n :=
  cokernel.π _

/-- The higher scalar power vanishes under the lower cokernel projection.
Source: BS 6.8.10 (blueprint: lem-a1-integral-constructible-reduction-fibres).
Proof: factor the higher power as the uniformizer times the lower power, use
bilinearity of composition, and apply the defining cokernel equation. -/
theorem quotientTransition_condition (n : ℕ) :
    ((pbcUniformizer l E) ^ (n + 1 + 1) •
      𝟙 (𝟭 (pbcModules T (pbcAdicCompletion T (pbcIntegralDatum l E))))) ≫
        quotientProjection l E T n = 0 := by
  sorry

/-- Consecutive ordinary quotient maps, fixed by their cokernel projections.
Source: BS 6.8.10 (blueprint: lem-a1-integral-constructible-reduction-fibres). -/
def quotientTransition (n : ℕ) : quotient l E T (n + 1) ⟶ quotient l E T n :=
  cokernel.desc _ (quotientProjection l E T n) (quotientTransition_condition l E T n)

/-- The strict ordinary quotient tower; index n means exponent n+1.
Source: BS 6.8.4(1), 6.8.10
(blueprint: lem-a1-integral-constructible-reduction-fibres). -/
def quotientTower := (Functor.ofOpSequence (quotientTransition l E T)).flip

/-- The canonical etale representative is direct image of the ordinary quotient tower.
Source: BS 5.1.2, 5.1.4 (blueprint: lem-a1-integral-constructible-reduction-fibres). -/
def etaleTower : pbcModules T (pbcAdicCompletion T (pbcIntegralDatum l E)) ⥤
    ℕᵒᵖ ⥤ Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} (PbcIntegralRing l E)) :=
  quotientTower l E T ⋙ (Functor.whiskeringRight _ _ _).obj
    (scalars l E T ⋙ ProEtale.comparisonLowerStar
      (ModuleCat.{u + 1} (PbcIntegralRing l E)) T)

variable {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ T)

/-- The tower of etale geometric stalks, the pointed-neighbourhood colimits.
Source: BS 6.8.4(1) (blueprint: lem-a1-integral-constructible-reduction-fibres). -/
def stalkTower := etaleTower l E T ⋙ (Functor.whiskeringRight _ _ _).obj
  ((pointSmallEtale x).sheafFiber (A := ModuleCat.{u + 1} (PbcIntegralRing l E)))

/-- The ordinary inverse-limit module, with its canonical projections.
Source: BS 6.8.4(1) (blueprint: lem-a1-integral-constructible-reduction-fibres). -/
def limitFiber := stalkTower l E T x ⋙ lim

/-- The recorded completed-pullback normalization of the fibre, applied to single sheaves.
On Heart this is exactly the fibre of its raw rationalization (PerAdic.fiber).
Source: BS 6.8.14(2) (blueprint: lem-a1-integral-constructible-reduction-fibres). -/
def sheafFiber := DerivedCategory.singleFunctor _ 0 ⋙
  pbcActualCompletedPull x (pbcIntegralDatum l E) ⋙
  DerivedCategory.homologyFunctor _ 0 ⋙ PerAdic.pointSections l E Ω ⋙
  ModuleCat.extendScalars (PerAdic.integerToField l E)

/-- The raw rational fibre agrees with its prescribed integral section formula.
Source: BS 6.8.14 (blueprint: lem-a1-integral-constructible-reduction-fibres).
Proof: substitute the defining equality of PerAdic.fiber_existsUnique and expand
integralFiber. The single-sheaf embedding gives exactly sheafFiber. -/
theorem rawFiberComparison_eq :
    toIntegral l E T ⋙ pbcRationalization T (pbcIntegralDatum l E) (pbcUniformizer l E) ⋙
      PerAdic.fiber l E T x = underlying l E T ⋙ sheafFiber l E T x := by
  sorry

/-- The sheaf formula is the recorded fibre of raw rationalization, with the exact
section normalization imposed in PerAdic.fiber_existsUnique. This changes only the
presentation of a degree-zero heart object.
Source: BS 6.8.14 (blueprint: lem-a1-integral-constructible-reduction-fibres). -/
def rawFiberComparison :
    toIntegral l E T ⋙ pbcRationalization T (pbcIntegralDatum l E) (pbcUniformizer l E) ⋙
      PerAdic.fiber l E T x ≅ underlying l E T ⋙ sheafFiber l E T x :=
  eqToIso (rawFiberComparison_eq l E T x)

/-- The normalized degree-zero counit of ordinary derived inverse image.
Source: BS 6.8.2, 6.8.14 (blueprint: lem-a1-integral-constructible-reduction-fibres). -/
def singlePullCounit
    (M : pbcModules T (pbcAdicCompletion T (pbcIntegralDatum l E))) :=
  pbcActualPullComplexCounit x (pbcIntegralDatum l E)
      ((CochainComplex.singleFunctor _ 0).obj M) ≫
    DerivedCategory.Q.map
      (((pbcActualModulePull x (pbcIntegralDatum l E)).mapCochainComplexSingleFunctor 0).hom.app M)

/-- The regular completed coefficient module.
Source: BS 6.8.2 (blueprint: lem-a1-integral-constructible-reduction-fibres). -/
abbrev coefficientUnit := SheafOfModules.unit
  ((adicLisseForget T).obj (pbcAdicCompletion T (pbcIntegralDatum l E)))

/-- The derived counit is invertible on the regular coefficient module.
Source: BS 6.8.2, 6.8.14 (blueprint: lem-a1-integral-constructible-reduction-fibres).
Proof: the regular module is flat. Its single complex is a bounded flat-term K-flat
complex, so the resolving normalization of pbcActualPullComplexCounit is invertible.
The final single-complex comparison is already an isomorphism. This lemma supplies
only the proof needed to define the actual coefficient vector 1 in the fibre. -/
@[instance] theorem regularCounit_isIso :
    IsIso (singlePullCounit l E T x (coefficientUnit l E T)) := by
  sorry

/-- The final point object maps canonically to the pullback of the final base object.
Source: BS 6.8.14 (blueprint: lem-a1-integral-constructible-reduction-fibres). -/
def pointFinalArrow : ProEt.mk (𝟙 (Spec (.of Ω))) ⟶
    (proEtaleBaseChange x).obj (ProEt.mk (𝟙 T)) :=
  MorphismProperty.Over.homMk
    (A := ProEt.mk (𝟙 (Spec (.of Ω))))
    (B := (proEtaleBaseChange x).obj (ProEt.mk (𝟙 T)))
    (pullback.lift (f := 𝟙 T) (g := x) x (𝟙 (Spec (.of Ω)))
      ((Category.comp_id x).trans (Category.id_comp x).symm))
    (pullback.lift_snd _ _ _)

/-- The canonical coefficient vector before rationalization: pull back the section 1,
use the inverse resolving counit, and apply the specified completion unit.
Source: BS 6.8.2, 6.8.14 (blueprint: lem-a1-integral-constructible-reduction-fibres). -/
def integralOne :
    ((PerAdic.pointSections l E Ω).obj
      ((DerivedCategory.homologyFunctor _ 0).obj
        ((pbcActualCompletedPull x (pbcIntegralDatum l E)).obj
          ((DerivedCategory.singleFunctor _ 0).obj (coefficientUnit l E T))))) := by
  unfold PerAdic.pointSections
  exact ((DerivedCategory.singleFunctorCompHomologyFunctorIso _ 0).inv.app
      ((pbcActualModulePull x (pbcIntegralDatum l E)).obj (coefficientUnit l E T)) ≫
    (DerivedCategory.homologyFunctor _ 0).map
      (inv (singlePullCounit l E T x (coefficientUnit l E T))) ≫
    (DerivedCategory.homologyFunctor _ 0).map
      ((pbcActualCompletedPullUnit x (pbcIntegralDatum l E)).app
        ((DerivedCategory.singleFunctor _ 0).obj (coefficientUnit l E T)))).val.app
      (op (ProEt.mk (𝟙 (Spec (.of Ω)))))
    (((pbcActualModulePull x (pbcIntegralDatum l E)).obj (coefficientUnit l E T)).val.map
      (pointFinalArrow T x).op
      (pbcActualModuleUnitSection x (pbcIntegralDatum l E) (coefficientUnit l E T)
        (ProEt.mk (𝟙 T))
          (1 : (pbcAdicCompletion T (pbcIntegralDatum l E)).obj.obj
            (op (ProEt.mk (𝟙 T))))))

open scoped ChangeOfRings

/-- The actual vector 1 in the normalized rational coefficient fibre.
Source: BS 6.8.14 (blueprint: lem-a1-integral-constructible-reduction-fibres). -/
def coefficientOne : (sheafFiber l E T x).obj (coefficientUnit l E T) :=
  (1 : E) ⊗ₜ[PbcIntegralRing l E, PerAdic.integerToField l E] integralOne l E T x

/-- The germ at x of the ordinary quotient section u(1).
Source: BS 5.1.2, 6.8.4 (blueprint: lem-a1-integral-constructible-reduction-fibres). -/
def sectionResidue
    (M : pbcModules T (pbcAdicCompletion T (pbcIntegralDatum l E)))
    (a : coefficientUnit l E T ⟶ M) (n : ℕ) :
    ((stalkTower l E T x).obj M).obj (op n) :=
  (pointedEtaleGerm (((etaleTower l E T).obj M).obj (op n)) x
    (Etale.mk (𝟙 T)) (Over.homMk x (Category.comp_id x))).hom
      (((quotientProjection l E T n).app M).val.app (op (ProEt.mk (𝟙 T)))
        (a.val.app (op (ProEt.mk (𝟙 T)))
          (1 : (pbcAdicCompletion T (pbcIntegralDatum l E)).obj.obj
            (op (ProEt.mk (𝟙 T))))))

variable {k : Type u} [Field k] [hl : Fact (IsUnit (l : k))]
include hl

/-- Ordinary quotients of integral constructible heart sheaves have compatible etale
origins on one finite stratification. Their inverse-limit stalks are finite A-modules,
recover their finite reductions, and rationalize naturally to the normalized adic fibres.
The last formula fixes this comparison on actual sections of the coefficient unit.
Finite quotient modules are represented as A-modules killed by the indicated ideal,
so their quotient-ring module structure is uniquely determined. Torsion is retained.

Source: BS Definition 6.8.10, Proposition 6.8.11(3), Lemmas 5.1.2, 5.1.4 and 6.8.2,
Propositions 6.8.4(1) and 6.8.14(2)
(blueprint: lem-a1-integral-constructible-reduction-fibres).

Proof:
1. Finite type over the field gives Noetherianity and finite dimension by
lem-weil-pbc-finite-type-over-noetherian and lem-fin-finite-type-fibre-dimension-bound.
The unit l stays a unit in local rings. The integral t-structure identifies Heart
with degree-zero cohomology sheaves. Condition (iii) of
lem-weil-pbc-integral-stratified-perfect-characterization gives one finite partition
and local models B tensor_A N with N finitely presented, without requiring N free.
2. By lem-weil-pbc-proetale-immersion-limit-preservation and
lem-weil-proetale-weakly-etale-localization restriction identifies completed coefficients
on strata and their charts. Ordinary cokernels commute with this restriction by
lem-weil-pbc-module-sheaves-colimits-forgetful. Completed-constant-sheaf reduction
identifies B/p^n with the finite constant ring and makes B flat over constant A.
3. Balanced tensor relations identify the local quotient with constant N/p^n N.
The constant-module-section-properties lemma preserves this calculation.
The DVR and finite-quotient lemmas make these finite modules. The same partition
therefore works for every n, including torsion local models.
4. Finite-ring-constructible-sheaf-origin and site-comparison-finite-level identify
G_n = nu_* F_n with its canonical origin through the comparison counit.
Comparison-pullback and finite-local-systems-twist give finite local models for G_n
on exactly the same strata. No inverse image of an infinite limit is asserted.
5. Quotient maps commute with projections by their cokernel definition. Full
faithfulness lifts the maps uniquely. The iterated ordinary quotient has kernel
p^n F, hence gives G_(n+1)/p^n = G_n and every transition cocycle.
6. Geometric stalks are exact. Restrict to the stratum using openclosed-stalk-upperstar
and constant-sheaf-geometric-stalk to see finite stalk modules. Apply
lem-pod-adic-limit-finite-modules to get the finite inverse limit and its surjective
projections with kernel p^n times the limit. Thus the quotient isomorphisms are
projection-induced, including all torsion cases.
7. On a local model use proetale-comparison-stalk, proetale-inverse-image-stalk and
proetale-constant-sheaf-stalk to identify the whole tower with N/p^n N. Its limit is N
by adic-limit-finite-modules. Continuous-rational-derived-realization identifies QF
with E tensor_A N. Choose a finite presentation of N. The normalized adic-heart fibre
sends its coefficient matrix to the same matrix over E. Exactness and tensor-right-
exactness identify its cokernel with E tensor_A N. Each generator goes to its compatible
residues, so changing the presentation or chart gives the same comparison.
8. Ordinary quotients, direct image, stalks, limits and tensor are functorial in every
integral sheaf map; the comparison is therefore a natural isomorphism. For the regular
coefficient sheaf the tower is A/p^n and its limit is A. The resolving counit and
completion unit used in coefficientOne preserve 1 at every finite level. Consequently
the values of u(1) give the unique compatible limit element a, and its fibre is 1 tensor a.
All these quotients are ordinary; derived reductions may have negative cohomology. -/
theorem integralConstructibleReductionFibres (W : PerAdic.Base k) :
    (∀ (M : Heart l E W.scheme) (n : ℕ),
      IsIso ((ProEtale.comparisonAdjunction
        (ModuleCat.{u + 1} (PbcIntegralRing l E)) W.scheme).counit.app
          ((scalars l E W.scheme).obj ((quotient l E W.scheme n).obj M.obj))) ∧
      (∀ U : W.scheme.Etale,
        (Ideal.span {pbcUniformizer l E}) ^ (n + 1) •
          (⊤ : Submodule (PbcIntegralRing l E)
            ((((etaleTower l E W.scheme).obj M.obj).obj (op n)).obj.obj (op U))) = ⊥)) ∧
    (∀ (M : Heart l E W.scheme) (n : ℕ),
      ∃ h : ((pbcUniformizer l E) ^ (n + 1) •
          𝟙 (((etaleTower l E W.scheme).obj M.obj).obj (op (n + 1)))) ≫
          ((etaleTower l E W.scheme).obj M.obj).map (homOfLE (Nat.le_succ n)).op = 0,
        Nonempty (IsColimit (CokernelCofork.ofπ
          (((etaleTower l E W.scheme).obj M.obj).map (homOfLE (Nat.le_succ n)).op) h))) ∧
    (∀ M : Heart l E W.scheme,
      ∃ S : FiniteLocallyClosedStratification W.scheme,
        (∀ (i : Fin S.n) (n : ℕ),
          ∃ C : (S.domain i).Cover.{u} proetalePrecoverage,
            ∀ j : C.I₀, ∃ N : ModuleCat.{u + 1} (PbcIntegralRing l E), Finite N ∧
              Nonempty ((ProEtale.upperStar (ModuleCat.{u + 1} (PbcIntegralRing l E))
                (C.f j ≫ S.immersion i)).obj
                  ((scalars l E W.scheme).obj ((quotient l E W.scheme n).obj M.obj)) ≅
                (constantSheaf (ProEt.topology (C.X j))
                  (ModuleCat.{u + 1} (PbcIntegralRing l E))).obj N)) ∧
        (∀ (i : Fin S.n) (n : ℕ),
          ∃ C : (S.domain i).Cover.{u} etalePrecoverage,
            ∀ j : C.I₀, ∃ N : ModuleCat.{u + 1} (PbcIntegralRing l E), Finite N ∧
              Nonempty ((Etale.upperStar (ModuleCat.{u + 1} (PbcIntegralRing l E))
                (C.f j ≫ S.immersion i)).obj
                  (((etaleTower l E W.scheme).obj M.obj).obj (op n)) ≅
                (constantSheaf (C.X j).smallEtaleTopology
                  (ModuleCat.{u + 1} (PbcIntegralRing l E))).obj N))) ∧
    (∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ W.scheme)
      (M : Heart l E W.scheme),
      Module.Finite (PbcIntegralRing l E) ((limitFiber l E W.scheme x).obj M.obj) ∧
        ∀ n : ℕ,
          Function.Surjective (limit.π ((stalkTower l E W.scheme x).obj M.obj) (op n)).hom ∧
          LinearMap.ker (limit.π ((stalkTower l E W.scheme x).obj M.obj) (op n)).hom =
            (Ideal.span {pbcUniformizer l E}) ^ (n + 1) •
              (⊤ : Submodule (PbcIntegralRing l E)
                ((limitFiber l E W.scheme x).obj M.obj))) ∧
    ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ W.scheme),
      ∃ c : toIntegral l E W.scheme ⋙
          pbcRationalization W.scheme (pbcIntegralDatum l E) (pbcUniformizer l E) ⋙
            PerAdic.fiber l E W.scheme x ≅
          underlying l E W.scheme ⋙ limitFiber l E W.scheme x ⋙
            ModuleCat.extendScalars (PerAdic.integerToField l E),
        ∀ (M : Heart l E W.scheme) (a : coefficientUnit l E W.scheme ⟶ M.obj),
          ∃ b : (limitFiber l E W.scheme x).obj M.obj,
            (∀ n : ℕ,
              (limit.π ((stalkTower l E W.scheme x).obj M.obj) (op n)).hom b =
                sectionResidue l E W.scheme x M.obj a n) ∧
            (c.hom.app M).hom ((rawFiberComparison l E W.scheme x).inv.app M
              ((sheafFiber l E W.scheme x).map a (coefficientOne l E W.scheme x))) =
                (1 : E) ⊗ₜ[PbcIntegralRing l E, PerAdic.integerToField l E] b := by
  sorry

end AlgebraicGeometry.Scheme.A1Integral
