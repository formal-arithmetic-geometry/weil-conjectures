module

public import Sheaf.CategoryTheory.SiteCoveringAxioms
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.Algebra.Homology.RingedSiteZerothHypercohomologyOfUniverses
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Sheaf.CategoryTheory.RingedToposMorphism
public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Flat
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.CategoryTheory.Preadditive.Yoneda.Limits
public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.HomologyZero
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.ShortExactPullback
public import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
public import Sheaf.Algebra.Homology.LocallyFreeDerivedHom
public import Sheaf.CategoryTheory.RingedDerivedRestrictionGeneral
import Sheaf.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import Mathlib.Algebra.Homology.DerivedCategory.DerivabilityStructureInjectives
import Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions
import WeilConjectures.Algebra.Homology.KInjectiveRestrictLocalized
import Sheaf.Paper.ProjectionMateExact
import Sheaf.CategoryTheory.ModulePullbackPushforwardAdjunction
import Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition

/-! # Connective hypercohomology on a ringed site

Source: Stacks Project, sites-cohomology.tex, Tags 071J and 07A5; quot.tex,
Tag 08JX, opening sentence of the proof
(blueprint: lem-sfb-ringed-site-connective-hypercohomology).

## Main statements

* `connective_hypercohomology`: the canonical natural comparison, negative vanishing,
  and the nonnegative-complex kernel formula.
* `connective_hypercohomology_localization`: the slice comparison and restriction square.
* `connective_hypercohomology_pullback`: compatibility with the derived adjunction unit.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048

universe u w

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory.RingedSiteConnective

/-- The recorded module category, with no new category structure.
Source: Stacks 07A5 (blueprint: lem-sfb-ringed-site-connective-hypercohomology). -/
abbrev modules {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{u}) :=
  ringedSiteModules.{u, u, u, u}
    ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)

/-- The rank-one module used in the recorded definition of global sections.
Source: Stacks 071J (blueprint: lem-sfb-ringed-site-connective-hypercohomology). -/
abbrev ringModule {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{u}) : modules R :=
  SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)

/-- Global sections are the existing additive Hom functor from the rank-one module.
Source: Stacks 071J (blueprint: lem-sfb-ringed-site-connective-hypercohomology). -/
abbrev sections {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{u}) : modules R ⥤ AddCommGrpCat.{u} :=
  preadditiveCoyoneda.obj (op (ringModule R))

/-- The standard localization of complexes of abelian groups, as in the recorded H⁰.
Source: Stacks 07A5 (blueprint: lem-sfb-ringed-site-connective-hypercohomology). -/
abbrev abDerived :=
  @DerivedCategory AddCommGrpCat.{u} _ _ (HasDerivedCategory.standard AddCommGrpCat.{u})

/-- Cohomology on that same standard localization.
Source: Stacks 07A5 (blueprint: lem-sfb-ringed-site-connective-hypercohomology). -/
def abHomology (n : ℤ) : abDerived.{u} ⥤ AddCommGrpCat.{u} :=
  letI := HasDerivedCategory.standard AddCommGrpCat.{u}
  DerivedCategory.homologyFunctor AddCommGrpCat.{u} n

/-- Unbounded derived sections, using exactly the functor and instances in the recorded H⁰.
Source: Stacks 07A5 (blueprint: lem-sfb-ringed-site-connective-hypercohomology). -/
def derivedSections {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{u}) [HasDerivedCategory.{w} (modules R)] :
    DerivedCategory (modules R) ⥤ abDerived.{u} :=
  letI : IsGrothendieckAbelian.{u} (modules R) :=
    (SheafOfModules.grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses
      J R).1
  letI := HasDerivedCategory.standard AddCommGrpCat.{u}
  (sections R).rightDerivedFunctor

/-- Degree i of unbounded derived sections; degree zero is the recorded hypercohomology.
Source: Stacks 07A5 (blueprint: lem-sfb-ringed-site-connective-hypercohomology). -/
abbrev hypercohomology {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{u}) [HasDerivedCategory.{w} (modules R)] (i : ℤ) :=
  derivedSections R ⋙ abHomology i

/-- The full subcategory on complexes with no negative cohomology sheaves.
Source: Stacks 071J (blueprint: lem-sfb-ringed-site-connective-hypercohomology). -/
abbrev connective {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{u}) [HasDerivedCategory.{w} (modules R)] :
    ObjectProperty (DerivedCategory (modules R)) :=
  fun E ↦ ∀ i : ℤ, i < 0 → IsZero ((DerivedCategory.homologyFunctor (modules R) i).obj E)

/-- The existing representative-to-derived comparison in degree zero.
Source: Stacks 071J and 07A5
(blueprint: lem-sfb-ringed-site-connective-hypercohomology). -/
def complexComparison {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{u}) [HasDerivedCategory.{w} (modules R)] :
    (sections R).mapHomologicalComplex (.up ℤ) ⋙
        HomologicalComplex.homologyFunctor AddCommGrpCat.{u} (.up ℤ) 0 ⟶
      DerivedCategory.Q ⋙ hypercohomology R 0 :=
  letI : IsGrothendieckAbelian.{u} (modules R) :=
    (SheafOfModules.grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses
      J R).1
  letI := HasDerivedCategory.standard AddCommGrpCat.{u}
  locallyFreeDerivedComparison (sections R)

/-- The cohomology-sheaf sections functor on the connective full subcategory.
Source: Stacks 071J (blueprint: lem-sfb-ringed-site-connective-hypercohomology). -/
abbrev ordinaryOnConnective {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{u}) [HasDerivedCategory.{w} (modules R)] :=
  (connective R).ι ⋙ DerivedCategory.homologyFunctor (modules R) 0 ⋙ sections R

/-- The recorded zeroth hypercohomology restricted to the connective full subcategory.
Source: Stacks 07A5 (blueprint: lem-sfb-ringed-site-connective-hypercohomology). -/
abbrev derivedOnConnective {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{u}) [HasDerivedCategory.{w} (modules R)] :=
  (connective R).ι ⋙ ringedSiteZerothHypercohomologyOfUniverses.{u, u, u, w} J R

/-- The existing degree-zero comparison on a sheaf placed in degree zero.
Source: Stacks 071J (blueprint: lem-sfb-ringed-site-connective-hypercohomology). -/
def sheafComparison {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{u}) [HasDerivedCategory.{w} (modules R)] :
    sections R ≅ DerivedCategory.singleFunctor (modules R) 0 ⋙ hypercohomology R 0 :=
  letI : IsGrothendieckAbelian.{u} (modules R) :=
    (SheafOfModules.grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses
      J R).1
  letI := HasDerivedCategory.standard AddCommGrpCat.{u}
  letI : EnoughInjectives (modules R) :=
    @IsGrothendieckAbelian.enoughInjectives _ _ _
      (SheafOfModules.grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses
        J R).1
  (sections R).singleFunctorCompRightDerivedFunctorCompHomologyFunctorZeroIso.symm

/-- Abelian evaluation as a functor contravariant in the site object.
Source: Stacks 071J (blueprint: lem-sfb-ringed-site-connective-hypercohomology). -/
abbrev evaluation {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{u}) : Cᵒᵖ ⥤ modules R ⥤ AddCommGrpCat.{u} :=
  (SheafOfModules.toSheaf
    ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R) ⋙
      sheafToPresheaf J AddCommGrpCat.{u}).flip

/-- Additivity of actual evaluation, inherited from module evaluation.
Source: Stacks 071J (blueprint: lem-sfb-ringed-site-connective-hypercohomology). -/
instance evaluation_additive {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{u}) (U : C) :
    ((evaluation R).obj (op U)).Additive :=
  ⟨rfl⟩

/-- Unbounded derived evaluation in degree i, with the same K-injective convention.
Source: Stacks 07A5 (blueprint: lem-sfb-ringed-site-connective-hypercohomology). -/
def evaluationHypercohomology {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{u}) [HasDerivedCategory.{w} (modules R)] (U : C) (i : ℤ) :
    DerivedCategory (modules R) ⥤ AddCommGrpCat.{u} :=
  letI : IsGrothendieckAbelian.{u} (modules R) :=
    (SheafOfModules.grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses
      J R).1
  letI := HasDerivedCategory.standard AddCommGrpCat.{u}
  ((evaluation R).obj (op U)).rightDerivedFunctor ⋙ abHomology i

/-- Restriction on derived evaluation is the derived actual section restriction.
Source: Stacks 071J and 07A5
(blueprint: lem-sfb-ringed-site-connective-hypercohomology). -/
def evaluationRestriction {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{u}) [HasDerivedCategory.{w} (modules R)]
    {U V : C} (a : V ⟶ U) (i : ℤ) :
    evaluationHypercohomology R U i ⟶ evaluationHypercohomology R V i :=
  letI : IsGrothendieckAbelian.{u} (modules R) :=
    (SheafOfModules.grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses
      J R).1
  letI := HasDerivedCategory.standard AddCommGrpCat.{u}
  Functor.whiskerRight
    (Functor.rightDerivedFunctorNatTrans ((evaluation R).map a.op)) (abHomology i)

/-- The canonical derived representative comparison for evaluation.
Source: Stacks 07A5 (blueprint: lem-sfb-ringed-site-connective-hypercohomology). -/
def evaluationComplexComparison
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{u}) [HasDerivedCategory.{w} (modules R)] (U : C) :
    ((evaluation R).obj (op U)).mapHomologicalComplex (.up ℤ) ⋙
        HomologicalComplex.homologyFunctor AddCommGrpCat.{u} (.up ℤ) 0 ⟶
      DerivedCategory.Q ⋙ evaluationHypercohomology R U 0 :=
  letI : IsGrothendieckAbelian.{u} (modules R) :=
    (SheafOfModules.grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses
      J R).1
  letI := HasDerivedCategory.standard AddCommGrpCat.{u}
  locallyFreeDerivedComparison ((evaluation R).obj (op U))

/-- The ordinary-to-derived comparison on an evaluated sheaf in degree zero.
Source: Stacks 071J (blueprint: lem-sfb-ringed-site-connective-hypercohomology). -/
def evaluationSheafComparison
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{u}) [HasDerivedCategory.{w} (modules R)] (U : C) :
    (evaluation R).obj (op U) ≅
      DerivedCategory.singleFunctor (modules R) 0 ⋙ evaluationHypercohomology R U 0 :=
  letI : IsGrothendieckAbelian.{u} (modules R) :=
    (SheafOfModules.grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses
      J R).1
  letI : EnoughInjectives (modules R) :=
    @IsGrothendieckAbelian.enoughInjectives _ _ _
      (SheafOfModules.grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses
        J R).1
  letI := HasDerivedCategory.standard AddCommGrpCat.{u}
  letI : PreservesFiniteLimits ((evaluation R).obj (op U)) :=
    inferInstanceAs (PreservesFiniteLimits
      (SheafOfModules.evaluation
        ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R) (op U) ⋙
        forget₂ (ModuleCat.{u} (R.obj.obj (op U))) AddCommGrpCat.{u}))
  ((evaluation R).obj (op U)).singleFunctorCompRightDerivedFunctorCompHomologyFunctorZeroIso.symm

/-- The actual exact module restriction, descended through localization.
Source: Stacks 03DH and 08FI
(blueprint: lem-sfb-ringed-site-connective-hypercohomology). -/
abbrev restriction {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{u}) (U : C)
    [HasDerivedCategory.{w} (modules R)]
    [HasDerivedCategory.{w} (modules (R.over U))] :
    DerivedCategory (modules R) ⥤ DerivedCategory (modules (R.over U)) :=
  letI : HasDerivedCategory.{w} (SheafOfModules.{u}
      (((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).over U)) :=
    inferInstanceAs (HasDerivedCategory.{w} (modules (R.over U)))
  ringedDerivedRestrictionGeneral
    ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R) U

/-- Cohomology commutes with the actual exact restriction functor.
Source: Stacks 03DH and 08FI
(blueprint: lem-sfb-ringed-site-connective-hypercohomology). -/
def restrictionHomology {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{u}) (U : C)
    [HasDerivedCategory.{w} (modules R)]
    [HasDerivedCategory.{w} (modules (R.over U))] (i : ℤ) :
    DerivedCategory.homologyFunctor (modules R) i ⋙
        SheafOfModules.overFunctor.{u}
          ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R) U ≅
      restriction R U ⋙ DerivedCategory.homologyFunctor (modules (R.over U)) i :=
  letI : HasDerivedCategory.{w} (SheafOfModules.{u}
      (((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).over U)) :=
    inferInstanceAs (HasDerivedCategory.{w} (modules (R.over U)))
  letI := (ringedOverFunctor_exactGeneral
    ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R) U).1
  letI := (ringedOverFunctor_exactGeneral
    ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R) U).2.1
  letI := (ringedOverFunctor_exactGeneral
    ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R) U).2.2
  (SheafOfModules.overFunctor.{u}
    ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R) U).mapDerivedCategoryHomologyFunctorIso i

/-- The actual underlying sheaf of sets of a module sheaf.
Source: Stacks 03DA (blueprint: lem-sfb-ringed-site-connective-hypercohomology). -/
abbrev underlyingSets {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{u}) : modules R ⥤ Sheaf J (Type u) :=
  SheafOfModules.toSheaf _ ⋙ sheafCompose J (forget AddCommGrpCat.{u})

/-- The global element attached to a map from the rank-one module: evaluation at one.
Source: Stacks 071J (blueprint: lem-sfb-ringed-site-connective-hypercohomology). -/
def globalElement {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{u}) (M : modules R) (a : ringModule R ⟶ M) :
    ⊤_ (Sheaf J (Type u)) ⟶ (underlyingSets R).obj M where
  hom :=
    { app := fun U ↦ ↾fun _ ↦ (M.unitHomEquiv a).val U
      naturality := fun U V f ↦ by
        ext x
        exact ((M.unitHomEquiv a).property f).symm }

/-- Total right derivation of an additive functor between the recorded module categories.
Source: Stacks 07A5 (blueprint: lem-sfb-ringed-site-connective-hypercohomology). -/
def derive {C D : Type u} [SmallCategory C] [SmallCategory D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    (A : Sheaf J CommRingCat.{u}) (B : Sheaf K CommRingCat.{u})
    [HasDerivedCategory.{w} (modules A)] [HasDerivedCategory.{w} (modules B)]
    (F : modules A ⥤ modules B) [F.Additive] :
    DerivedCategory (modules A) ⥤ DerivedCategory (modules B) :=
  letI : IsGrothendieckAbelian.{u} (modules A) :=
    (SheafOfModules.grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses
      J A).1
  F.rightDerivedFunctor

/-- The total-right-derived unit on the homotopy category, fixing the chosen derived functor.
Source: Stacks 07A5 (blueprint: lem-sfb-ringed-site-connective-hypercohomology). -/
def deriveUnit {C D : Type u} [SmallCategory C] [SmallCategory D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    (A : Sheaf J CommRingCat.{u}) (B : Sheaf K CommRingCat.{u})
    [HasDerivedCategory.{w} (modules A)] [HasDerivedCategory.{w} (modules B)]
    (F : modules A ⥤ modules B) [F.Additive] :
    F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ derive A B F :=
  letI : IsGrothendieckAbelian.{u} (modules A) :=
    (SheafOfModules.grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses
      J A).1
  F.rightDerivedFunctorUnit

/-- The ordinary degree-zero normalization for the right derived module direct image.
Source: Stacks 071J and 07A5
(blueprint: lem-sfb-ringed-site-connective-hypercohomology). -/
def deriveSheafComparison {C D : Type u} [SmallCategory C] [SmallCategory D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    (A : Sheaf J CommRingCat.{u}) (B : Sheaf K CommRingCat.{u})
    [HasDerivedCategory.{w} (modules A)] [HasDerivedCategory.{w} (modules B)]
    (F : modules A ⥤ modules B) [F.Additive] [PreservesFiniteLimits F] :
    DerivedCategory.singleFunctor (modules A) 0 ⋙ derive A B F ⋙
      DerivedCategory.homologyFunctor (modules B) 0 ≅ F :=
  letI : IsGrothendieckAbelian.{u} (modules A) :=
    (SheafOfModules.grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses
      J A).1
  letI : EnoughInjectives (modules A) :=
    @IsGrothendieckAbelian.enoughInjectives _ _ _
      (SheafOfModules.grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses
        J A).1
  F.singleFunctorCompRightDerivedFunctorCompHomologyFunctorZeroIso

/-- The section of the zeroth cohomology sheaf represented by an actual section cycle.
Source: Stacks 071J and quot.tex 08JX
(blueprint: lem-sfb-ringed-site-connective-hypercohomology). -/
def cycleToSheaf {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{u}) [HasDerivedCategory.{w} (modules R)]
    (P : CochainComplex (modules R) ℤ) (a : ringModule R ⟶ P.X 0)
    (ha : a ≫ P.d 0 1 = 0) :
    ringModule R ⟶ (DerivedCategory.homologyFunctor (modules R) 0).obj
      (DerivedCategory.Q.obj P) :=
  P.liftCycles a 1 (by simp) ha ≫ P.homologyπ 0 ≫
    (DerivedCategory.homologyFunctorFactors (modules R) 0).inv.app P

/-- Connective degree-zero hypercohomology, with its canonical map, negative vanishing,
nonnegative-complex kernel formula and normalization by the derived unit.
Source: Stacks 071J, 07A5 and quot.tex 08JX
(blueprint: lem-sfb-ringed-site-connective-hypercohomology).

Proof:
1. Module sheaves are Grothendieck abelian by lem-weil-pbc-ring-sheaves-grothendieck;
   lem-sp-grothendieck-enough-injectives gives enough injectives. Connectiveness puts E
   in D+ (def-weil-pbc-bounded-derived-subcategories). Apply
   lem-weil-pbc-dplus-injective-representative at zero to get a nonnegative injective
   representative I. It is K-injective. Resolutions also exist on the full unbounded
   category by prop-pur-kinjective-resolutions-exist, so def-sfb-right-derived-functor
   computes derived sections on I termwise, without an upper bound.
2. Since the degree -1 term of I vanishes, H0(I)=ker(d0). Sections preserve this kernel,
   so its sections equal H0 of the section complex. Negative terms of that complex vanish.
   This proves
   invertibility and negative vanishing, using def-weil-derived-cohomology-sheaves and
   def-pur-ringed-site-zeroth-hypercohomology.
3. The standard truncation def-sbc-standard-tstructure-derived-category is the inclusion
   of these zero cycles. Its H0 is the identity, which uniquely characterizes the map
   from H0(E)[0] into E. Naturality of the derived unit identifies the displayed map
   with the isomorphism of step 2, including the ordinary sheaf-in-degree-zero comparison.
4. By lem-weil-pbc-kinjective-hom-derived a derived map is represented on I by a chain
   map, unique up to homotopy. It sends a cycle to its degree-zero image. Homotopies
   vanish on zero cycles since the target has no term in degree -1. This proves
   naturality of the isomorphism and independence of the representative.
5. For any nonnegative P, H0(P)=ker(d0) as well. Sections preserve the kernel, giving
   the stated kernel isomorphism. Unit naturality says that an ordinary section cycle
   maps to its own class. This is the last equation; it asserts no higher-cohomology
   computation by ordinary sections of P.
-/
theorem connective_hypercohomology
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{u}) [HasDerivedCategory.{w} (modules R)] :
    ∃ e : ordinaryOnConnective R ≅ derivedOnConnective R,
      (∀ E : (connective R).FullSubcategory,
        ∃! t : (DerivedCategory.singleFunctor (modules R) 0).obj
            ((DerivedCategory.homologyFunctor (modules R) 0).obj E.obj) ⟶ E.obj,
          (DerivedCategory.singleFunctorCompHomologyFunctorIso (modules R) 0).inv.app
              ((DerivedCategory.homologyFunctor (modules R) 0).obj E.obj) ≫
            (DerivedCategory.homologyFunctor (modules R) 0).map t = 𝟙 _ ∧
          e.hom.app E =
            (sheafComparison R).hom.app
                ((DerivedCategory.homologyFunctor (modules R) 0).obj E.obj) ≫
              (hypercohomology R 0).map t) ∧
      (∀ (E : DerivedCategory (modules R)), connective R E →
        ∀ i : ℤ, i < 0 → IsZero ((hypercohomology R i).obj E)) ∧
      ∀ (P : CochainComplex (modules R) ℤ),
        (∀ n : ℤ, n < 0 → IsZero (P.X n)) →
        ∃ hP : connective R (DerivedCategory.Q.obj P),
          ∃ k : kernel ((sections R).map (P.d 0 1)) ≅
              (ringedSiteZerothHypercohomologyOfUniverses.{u, u, u, w} J R).obj
                (DerivedCategory.Q.obj P),
            (∀ (x : ↥(kernel ((sections R).map (P.d 0 1)) : AddCommGrpCat.{u}))
              (a : ringModule R ⟶ P.X 0) (ha : a ≫ P.d 0 1 = 0),
              (kernel.ι ((sections R).map (P.d 0 1))) x = a →
                k.hom x = e.hom.app ⟨DerivedCategory.Q.obj P, hP⟩ (cycleToSheaf R P a ha)) ∧
            ∀ (a : ringModule R ⟶ P.X 0) (ha : a ≫ P.d 0 1 = 0)
              (c : (((sections R).mapHomologicalComplex (.up ℤ)).obj P).cycles 0),
              ((((sections R).mapHomologicalComplex (.up ℤ)).obj P).iCycles 0) c = a →
              (complexComparison R).app P
                  (((((sections R).mapHomologicalComplex (.up ℤ)).obj P).homologyπ 0) c) =
                e.hom.app ⟨DerivedCategory.Q.obj P, hP⟩ (cycleToSheaf R P a ha) := by
  sorry

/-- The identifications on every localized site and their actual restriction maps.
Source: Stacks 071J, 07A5, 08FI, and Modules on Sites 04IX
(blueprint: lem-sfb-ringed-site-connective-hypercohomology).

Proof:
Use the nonnegative K-injective model from steps 1--4 of the node. Restriction is
exact by def-weil-pbc-ringed-derived-restriction and preserves K-injectivity by
lem-pur-kinjective-restrict-localized. On the slice, evaluation at id_U gives I(U).
Thus the same kernel calculation gives the localized isomorphism. For V→U the actual
restriction chain map sends a cycle to its restriction; the derived-unit equation of
def-sfb-right-derived-functor gives that same map on hypercohomology. Both sides of the
square therefore send a cycle to its restriction. This also handles iterated slices.
The comparison b is normalized on every K-injective representative by that evaluation
identity, so is independent of a representative and natural in the derived argument.
-/
theorem connective_hypercohomology_localization
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{u}) [HasDerivedCategory.{w} (modules R)]
    [∀ U : C, HasDerivedCategory.{w} (modules (R.over U))] :
    ∃ e : ∀ U : C,
        (connective R).ι ⋙ DerivedCategory.homologyFunctor (modules R) 0 ⋙
            (evaluation R).obj (op U) ≅
          (connective R).ι ⋙ evaluationHypercohomology R U 0,
      (∀ (U : C) (E : (connective R).FullSubcategory)
        (t : (DerivedCategory.singleFunctor (modules R) 0).obj
          ((DerivedCategory.homologyFunctor (modules R) 0).obj E.obj) ⟶ E.obj),
        (DerivedCategory.singleFunctorCompHomologyFunctorIso (modules R) 0).inv.app _ ≫
          (DerivedCategory.homologyFunctor (modules R) 0).map t = 𝟙 _ →
        (e U).hom.app E = (evaluationSheafComparison R U).hom.app _ ≫
          (evaluationHypercohomology R U 0).map t) ∧
      (∀ (U V : C) (a : V ⟶ U) (E : (connective R).FullSubcategory),
        ((evaluation R).map a.op).app
              ((DerivedCategory.homologyFunctor (modules R) 0).obj E.obj) ≫
            (e V).hom.app E =
          (e U).hom.app E ≫ (evaluationRestriction R a 0).app E.obj) ∧
      (∀ (U : C) (E : DerivedCategory (modules R)), connective R E →
        ∀ i : ℤ, i < 0 → IsZero ((evaluationHypercohomology R U i).obj E)) ∧
      (∀ (U : C) (E : DerivedCategory (modules R)), connective R E →
        connective (R.over U) ((restriction R U).obj E)) ∧
      (∀ (U : C) (E : DerivedCategory (modules R)), connective R E →
        ∀ i : ℤ, i < 0 →
          IsZero ((hypercohomology (R.over U) i).obj ((restriction R U).obj E))) ∧
      ∃ b : ∀ U : C,
          (connective R).ι ⋙ evaluationHypercohomology R U 0 ≅
            (connective R).ι ⋙ restriction R U ⋙ hypercohomology (R.over U) 0,
        ∀ (U : C) (E : (connective R).FullSubcategory),
          ∃ hU : connective (R.over U) ((restriction R U).obj E.obj),
            ∃ (eU : ordinaryOnConnective (R.over U) ≅ derivedOnConnective (R.over U))
              (sU : ((evaluation R).obj (op U)).obj
                  ((DerivedCategory.homologyFunctor (modules R) 0).obj E.obj) ≅
                (sections (R.over U)).obj
                  ((DerivedCategory.homologyFunctor (modules (R.over U)) 0).obj
                    ((restriction R U).obj E.obj))),
              (∀ (t : (DerivedCategory.singleFunctor (modules (R.over U)) 0).obj
                  ((DerivedCategory.homologyFunctor (modules (R.over U)) 0).obj
                    ((restriction R U).obj E.obj)) ⟶ (restriction R U).obj E.obj),
                (DerivedCategory.singleFunctorCompHomologyFunctorIso
                    (modules (R.over U)) 0).inv.app _ ≫
                    (DerivedCategory.homologyFunctor (modules (R.over U)) 0).map t = 𝟙 _ →
                  eU.hom.app ⟨(restriction R U).obj E.obj, hU⟩ =
                    (sheafComparison (R.over U)).hom.app _ ≫
                      (hypercohomology (R.over U) 0).map t) ∧
              (∀ x : ((evaluation R).obj (op U)).obj
                  ((DerivedCategory.homologyFunctor (modules R) 0).obj E.obj),
                (sU.hom x).val.app (op (Over.mk (𝟙 U)))
                    (1 : R.obj.obj (op U)) =
                  ((restrictionHomology R U 0).hom.app E.obj).val.app
                    (op (Over.mk (𝟙 U))) x) ∧
              (e U).hom.app E ≫ (b U).hom.app E =
                sU.hom ≫ eU.hom.app ⟨(restriction R U).obj E.obj, hU⟩ := by
  sorry

/-- The derived-global-sections unit on any representative.
Source: Stacks 07A5 (blueprint: lem-sfb-ringed-site-connective-hypercohomology). -/
def sectionsUnit {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{u}) [HasDerivedCategory.{w} (modules R)]
    (P : CochainComplex (modules R) ℤ) :
    (@DerivedCategory.Q AddCommGrpCat.{u} _ _ (HasDerivedCategory.standard _)).obj
        (((sections R).mapHomologicalComplex (.up ℤ)).obj P) ⟶ (derivedSections R).obj
      (DerivedCategory.Q.obj P) :=
  letI : IsGrothendieckAbelian.{u} (modules R) :=
    (SheafOfModules.grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses
      J R).1
  letI := HasDerivedCategory.standard AddCommGrpCat.{u}
  (sections R).rightDerivedFunctorUnitQ P

/-- The module right-derived unit on any representative.
Source: Stacks 07A5 (blueprint: lem-sfb-ringed-site-connective-hypercohomology). -/
def moduleUnit {C D : Type u} [SmallCategory C] [SmallCategory D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    (A : Sheaf J CommRingCat.{u}) (B : Sheaf K CommRingCat.{u})
    [HasDerivedCategory.{w} (modules A)] [HasDerivedCategory.{w} (modules B)]
    (F : modules A ⥤ modules B) [F.Additive] (P : CochainComplex (modules A) ℤ) :
    DerivedCategory.Q.obj ((F.mapHomologicalComplex (.up ℤ)).obj P) ⟶
      (derive A B F).obj (DerivedCategory.Q.obj P) :=
  letI : IsGrothendieckAbelian.{u} (modules A) :=
    (SheafOfModules.grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses
      J A).1
  F.rightDerivedFunctorUnitQ P

/-- The canonical normalization of the connective comparison by H0(E)[0]→E.
Source: Stacks 071J (blueprint: lem-sfb-ringed-site-connective-hypercohomology). -/
def IsCanonicalComparison {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{u}) [HasDerivedCategory.{w} (modules R)]
    (e : ordinaryOnConnective R ≅ derivedOnConnective R) : Prop :=
  ∀ (E : (connective R).FullSubcategory)
    (t : (DerivedCategory.singleFunctor (modules R) 0).obj
        ((DerivedCategory.homologyFunctor (modules R) 0).obj E.obj) ⟶ E.obj),
    (DerivedCategory.singleFunctorCompHomologyFunctorIso (modules R) 0).inv.app _ ≫
        (DerivedCategory.homologyFunctor (modules R) 0).map t = 𝟙 _ →
      e.hom.app E = (sheafComparison R).hom.app _ ≫ (hypercohomology R 0).map t

/-- The canonical normalization of H0(Rf_*T) ≅ f_*H0(T) on connective objects.
Source: Stacks 071J and 07A5
(blueprint: lem-sfb-ringed-site-connective-hypercohomology). -/
def IsDirectImageCanonicalComparison
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    (A : Sheaf J CommRingCat.{u}) (B : Sheaf K CommRingCat.{u})
    [HasDerivedCategory.{w} (modules A)] [HasDerivedCategory.{w} (modules B)]
    (G : modules A ⥤ modules B) [G.Additive] [PreservesFiniteLimits G]
    (d : (connective A).ι ⋙ derive A B G ⋙
          DerivedCategory.homologyFunctor (modules B) 0 ≅
        (connective A).ι ⋙ DerivedCategory.homologyFunctor (modules A) 0 ⋙ G) : Prop :=
  ∀ (T : (connective A).FullSubcategory)
    (a : (DerivedCategory.singleFunctor (modules A) 0).obj
        ((DerivedCategory.homologyFunctor (modules A) 0).obj T.obj) ⟶ T.obj),
    (DerivedCategory.singleFunctorCompHomologyFunctorIso (modules A) 0).inv.app _ ≫
      (DerivedCategory.homologyFunctor (modules A) 0).map a = 𝟙 _ →
    d.inv.app T = (deriveSheafComparison A B G).inv.app _ ≫
      (DerivedCategory.homologyFunctor (modules B) 0).map ((derive A B G).map a)

/-- The unit equation characterizing the derived pullback adjunction on representatives.
Source: Stacks 07A6 and derived.tex 0FND
(blueprint: lem-sfb-ringed-site-connective-hypercohomology). -/
def IsPullbackUnitNormalized
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    (A : Sheaf J CommRingCat.{u}) (B : Sheaf K CommRingCat.{u})
    [HasDerivedCategory.{w} (modules A)] [HasDerivedCategory.{w} (modules B)]
    (f : RingedToposMorphism
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj A)
      ((sheafCompose K (forget₂ CommRingCat RingCat)).obj B))
    (F : modules B ⥤ modules A) [F.Additive] (adj : F ⊣ f.modules)
    (L : DerivedCategory (modules B) ⥤ DerivedCategory (modules A))
    (eps : DerivedCategory.Qh ⋙ L ⟶ F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    (ad : L ⊣ derive A B f.modules) : Prop :=
  ∀ P : CochainComplex (modules B) ℤ,
    ad.unit.app (DerivedCategory.Qh.obj
        ((HomotopyCategory.quotient _ (.up ℤ)).obj P)) ≫
        (derive A B f.modules).map
          (eps.app ((HomotopyCategory.quotient _ (.up ℤ)).obj P)) =
      DerivedCategory.Qh.map ((adj.mapHomotopyCategory (.up ℤ)).unit.app
          ((HomotopyCategory.quotient _ (.up ℤ)).obj P)) ≫
        (deriveUnit A B f.modules).app
          ((F.mapHomotopyCategory (.up ℤ)).obj
            ((HomotopyCategory.quotient _ (.up ℤ)).obj P))

/-- The ordinary sections comparison fixed by the geometric adjunction on global elements.
Source: Stacks 071J and 07A6
(blueprint: lem-sfb-ringed-site-connective-hypercohomology). -/
def IsOrdinarySectionsComparisonNormalized
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    (A : Sheaf J CommRingCat.{u}) (B : Sheaf K CommRingCat.{u})
    [HasDerivedCategory.{w} (modules A)] [HasDerivedCategory.{w} (modules B)]
    (f : RingedToposMorphism
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj A)
      ((sheafCompose K (forget₂ CommRingCat RingCat)).obj B))
    (t : f.modules ⋙ sections B ≅ sections A) : Prop :=
  ∀ (M : modules A) (x : (sections B).obj (f.modules.obj M)),
    (f.adj.homEquiv _ _)
      (terminal.from (f.inverse.obj (⊤_ (Sheaf K (Type u)))) ≫
        globalElement A M (t.hom.app M x)) =
      globalElement B (f.modules.obj M) x ≫ f.underlying.hom.app M

/-- The canonical derived-composition comparison fixed by its derived-unit equation.
Source: Stacks 0D6E
(blueprint: lem-sfb-ringed-site-connective-hypercohomology). -/
def IsSectionsCompositionNormalized
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    (A : Sheaf J CommRingCat.{u}) (B : Sheaf K CommRingCat.{u})
    [HasDerivedCategory.{w} (modules A)] [HasDerivedCategory.{w} (modules B)]
    (f : RingedToposMorphism
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj A)
      ((sheafCompose K (forget₂ CommRingCat RingCat)).obj B))
    (t : f.modules ⋙ sections B ≅ sections A)
    (kappa : derive A B f.modules ⋙ derivedSections B ≅ derivedSections A) : Prop :=
  ∀ P : CochainComplex (modules A) ℤ,
    sectionsUnit B ((f.modules.mapHomologicalComplex (.up ℤ)).obj P) ≫
        (derivedSections B).map (moduleUnit A B f.modules P) ≫
        kappa.hom.app (DerivedCategory.Q.obj P) =
      (@DerivedCategory.Q AddCommGrpCat.{u} _ _ (HasDerivedCategory.standard _)).map
          ((NatTrans.mapHomologicalComplex t.hom (.up ℤ)).app P) ≫ sectionsUnit A P

/-- Pullback compatibility, using the derived adjunction unit and the canonical Leray
comparison, with both comparisons normalized on representatives.
Source: Stacks 07A5, 07A6 and 0D6E; quot.tex 08JX
(blueprint: lem-sfb-ringed-site-connective-hypercohomology).

Proof:
1. Use lem-weil-pbc-ringed-topoi-module-adjunction for the ordinary tensor pullback
   adjunction, and def-pc-kflat-complex to compute its total left derived functor
   on flat K-flat representatives. The canonical adjunction from
   lem-weil-pbc-ringed-projection-mate-exact has precisely the unit equation below.
2. Apply lem-weil-pbc-ringed-topoi-derived-pushforward-composition also to the
   global-section morphism to the point. Its resolution normalization gives kappa,
   whose equation below is exactly the composite-derived-unit equation. The ordinary
   comparison t is uniquely fixed on global elements by the geometric adjunction.
3. For connective F choose a nonnegative K-injective J by
   lem-weil-pbc-dplus-injective-representative. The right-adjoint f_* preserves kernels,
   so H0(Rf_*F)=ker(f_*d0)=f_*H0(F), and Rf_*F is connective. This gives d, normalized
   by applying Rf_* to the canonical truncation arrow. Natural chain maps prove its
   naturality, by lem-weil-pbc-kinjective-hom-derived.
4. Apply the canonical connective comparison to the derived unit E→Rf_*Lf*E.
   The naturality square identifies H0RGamma of that unit with sections of H0 of
   the unit, followed by d. The kappa unit equation in step 2 identifies the result
   with pullback on hypercohomology. Both degree-zero comparisons send each zero
   cycle to the same cycle, proving the final equation. There is no upper bound,
   and the assumption that Lf*E is connective is used exactly at this last step.
-/
theorem connective_hypercohomology_pullback
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    (A : Sheaf J CommRingCat.{u}) (B : Sheaf K CommRingCat.{u})
    [HasDerivedCategory.{w} (modules A)] [HasDerivedCategory.{w} (modules B)]
    (f : RingedToposMorphism
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj A)
      ((sheafCompose K (forget₂ CommRingCat RingCat)).obj B)) :
    ∃ (F : modules B ⥤ modules A) (hF : F.Additive) (adj : F ⊣ f.modules)
      (hlim : PreservesFiniteLimits f.modules)
      (L : DerivedCategory (modules B) ⥤ DerivedCategory (modules A))
      (eps : DerivedCategory.Qh ⋙ L ⟶
        F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
      (ad : L ⊣ derive A B f.modules)
      (t : f.modules ⋙ sections B ≅ sections A)
      (kappa : derive A B f.modules ⋙ derivedSections B ≅ derivedSections A),
      L.IsLeftDerivedFunctor eps (HomotopyCategory.quasiIso (modules B) (.up ℤ)) ∧
      (∀ P : CochainComplex (modules B) ℤ,
        CochainComplex.IsKFlatIndependentCoefficients (R := B) P →
        (∀ n : ℤ, SheafOfModules.IsFlat (P.X n)) →
        IsIso (eps.app ((HomotopyCategory.quotient _ (.up ℤ)).obj P))) ∧
      IsPullbackUnitNormalized A B f F adj L eps ad ∧
      IsOrdinarySectionsComparisonNormalized A B f t ∧
      IsSectionsCompositionNormalized A B f t kappa ∧
      ∃ (eA : ordinaryOnConnective A ≅ derivedOnConnective A)
        (eB : ordinaryOnConnective B ≅ derivedOnConnective B),
        IsCanonicalComparison A eA ∧ IsCanonicalComparison B eB ∧
        ∃ d : (connective A).ι ⋙ derive A B f.modules ⋙
              DerivedCategory.homologyFunctor (modules B) 0 ≅
            (connective A).ι ⋙ DerivedCategory.homologyFunctor (modules A) 0 ⋙ f.modules,
          (∀ (T : (connective A).FullSubcategory),
            connective B ((derive A B f.modules).obj T.obj)) ∧
          IsDirectImageCanonicalComparison A B f.modules d ∧
          ∀ (E : DerivedCategory (modules B)) (hE : connective B E)
            (hLE : connective A (L.obj E)),
            eB.hom.app ⟨E, hE⟩ ≫ (hypercohomology B 0).map (ad.unit.app E) ≫
                (abHomology 0).map (kappa.hom.app (L.obj E)) =
              (sections B).map
                  ((DerivedCategory.homologyFunctor (modules B) 0).map (ad.unit.app E) ≫
                    d.hom.app ⟨L.obj E, hLE⟩) ≫
                t.hom.app ((DerivedCategory.homologyFunctor (modules A) 0).obj (L.obj E)) ≫
                  eA.hom.app ⟨L.obj E, hLE⟩ := by
  sorry

end CategoryTheory.RingedSiteConnective
