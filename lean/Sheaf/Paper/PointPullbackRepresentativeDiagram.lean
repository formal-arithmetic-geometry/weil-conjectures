module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
public import Sheaf.Paper.PointProEtaleSectionsExactOfUniverses
public import Sheaf.Paper.CompletedIntegralConstantMapOfUniverses
public import Sheaf.Paper.IntegralDerivedOperationsOnSlices
public import Sheaf.Paper.DerivedPullbackTensorHom
public import Sheaf.Paper.DerivedScalarExtensionRestrictionAdjunction
public import Sheaf.CategoryTheory.StrictRoosModel
public import Sheaf.AlgebraicGeometry.ProEtaleCoefficientPullbackExact
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
import all Sheaf.Paper.PodReindexingRoosComparison
import all Sheaf.Paper.IntegralOperationsWellDefined
import WeilConjectures.CategoryTheory.Triangulated.DerivedLimitProducts
import Mathlib.Algebra.Homology.DerivedCategory.Fractions
import Sheaf.Paper.IntegralReductionTowerWellDefinedUnrestricted

/-! # Point sections on every completed-pullback representative

Source: blueprint main-20261015, sec-trace-formula/sk-d-weil,
prop-trf-rational-frobenius-integral-model.proof.md, clause (3); Stacks 06YS,
06YY and 0941 (blueprint: lem-trf-point-pullback-representative-diagram).

All complexes are unbounded. Index n denotes the positive exponent n+1. The strict
quotient tower and its diagonal Roos maps are the recorded constructions. Section
scalars use the constant-to-completion map, never an arbitrary ring identification.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types true
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology
attribute [-instance] WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective
attribute [local instance 3000] WeilConjectures.integralOperationsAbSheafify
  WeilConjectures.integralOperationsAbLocallyBijective
  WeilConjectures.integralTowerHasDerivedCategory
universe t u a b c d
attribute [local irreducible] CategoryTheory.Limits.limit
  WeilConjectures.completedIntegralCoefficientSheafUnrestricted
  HasDerivedCategory.standard WeilConjectures.unrestrictedIntegralReductionExistence
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale
namespace WeilConjectures.PointPullbackRepresentative

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (k : Type t) [Field k]

/-- Integral scalars enter final-object sections through all their finite quotients.
Source: Stacks 03CW, 0941 (blueprint: lem-trf-point-pullback-representative-diagram). -/
def scalarMap : ULift.{t + 1} (Padic.coefficientExtensionIntegers l E) →+*
    (completedIntegralCommRingSheafUnrestricted l E (Spec (.of k))).obj.obj
      (op (ProEt.mk (𝟙 (Spec (.of k))))) :=
  (((integralConstantToCompletionOfUniverses l E (Spec (.of k))).hom.app
      (op (ProEt.mk (𝟙 (Spec (.of k)))))).hom).comp
    (((forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)}).map
      ((toSheafify (ProEt.topology (Spec (.of k)))
        ((Functor.const (Scheme.ProEt (Spec (.of k)))ᵒᵖ).obj
          (CommRingCat.of (ULift.{t + 1} (Padic.coefficientExtensionIntegers l E))))).app
            (op (ProEt.mk (𝟙 (Spec (.of k))))))).hom)

attribute [local irreducible] scalarMap

/-- Exact final-object sections with their canonical integral scalar action.
Source: Stacks 03CW (blueprint: lem-trf-point-pullback-representative-diagram). -/
def sections : integralTowerModules.{t, u} l E (Spec (.of k)) ⥤
    ModuleCat.{max u (t + 1)} (ULift.{t + 1} (Padic.coefficientExtensionIntegers l E)) :=
  pointModuleSectionsOfUniverses.{t, u} k
      (completedIntegralCommRingSheafUnrestricted l E (Spec (.of k))) ⋙
    ModuleCat.restrictScalars.{max u (t + 1), max u (t + 1), max u (t + 1)}
      (scalarMap l E k)

/-- The additive structure comes from evaluation and restriction of scalars.
Source: Stacks 03CW (blueprint: lem-trf-point-pullback-representative-diagram). -/
instance sectionsAdditive : (sections l E k).Additive :=
  inferInstanceAs ((pointModuleSectionsOfUniverses.{t, u} k
      (completedIntegralCommRingSheafUnrestricted l E (Spec (.of k))) ⋙
    ModuleCat.restrictScalars.{max u (t + 1), max u (t + 1), max u (t + 1)}
      (scalarMap l E k)).Additive)

variable [IsAlgClosed k]

/-- Exact point evaluation preserves finite limits; scalar restriction does too.
Source: Stacks 0946 (blueprint: lem-trf-point-pullback-representative-diagram). -/
instance sectionsLimits : PreservesFiniteLimits (sections l E k) :=
  @comp_preservesFiniteLimits _ _ _ _ _ _
    (pointModuleSectionsOfUniverses.{t, u} k
      (completedIntegralCommRingSheafUnrestricted l E (Spec (.of k))))
    (ModuleCat.restrictScalars.{max u (t + 1)} (scalarMap l E k))
    (((point_proEtale_sections_exact_of_universes.{t, u, 0, 0} k).2
      (completedIntegralCommRingSheafUnrestricted l E (Spec (.of k)))).1)
    (inferInstanceAs (PreservesFiniteLimits
      (ModuleCat.restrictScalars.{max u (t + 1), max u (t + 1), max u (t + 1)}
        (scalarMap l E k))))

/-- Exact point evaluation preserves finite colimits, as does scalar restriction.
Source: Stacks 0946 (blueprint: lem-trf-point-pullback-representative-diagram). -/
instance sectionsColimits : PreservesFiniteColimits (sections l E k) :=
  @comp_preservesFiniteColimits _ _ _ _ _ _
    (pointModuleSectionsOfUniverses.{t, u} k
      (completedIntegralCommRingSheafUnrestricted l E (Spec (.of k))))
    (ModuleCat.restrictScalars.{max u (t + 1)} (scalarMap l E k))
    (((point_proEtale_sections_exact_of_universes.{t, u, 0, 0} k).2
      (completedIntegralCommRingSheafUnrestricted l E (Spec (.of k)))).2.1)
    (inferInstanceAs (PreservesFiniteColimits
      (ModuleCat.restrictScalars.{max u (t + 1), max u (t + 1), max u (t + 1)}
        (scalarMap l E k))))

/-- Termwise sections, with no truncation.
Source: Stacks 0941 (blueprint: lem-trf-point-pullback-representative-diagram). -/
abbrev sectionsComplex := (sections l E k).mapHomologicalComplex (.up ℤ)

/-- Standard localization of modules with the same coefficient size as the site.
Source: Stacks 05RU (blueprint: lem-trf-point-pullback-representative-diagram). -/
instance moduleHasDerived : HasDerivedCategory
    (ModuleCat.{max u (t + 1)} (ULift.{t + 1} (Padic.coefficientExtensionIntegers l E))) :=
  HasDerivedCategory.standard _

/-- The standard unbounded localization on integral module complexes.
Source: Stacks 05RU (blueprint: lem-trf-point-pullback-representative-diagram). -/
abbrev moduleQ := @DerivedCategory.Q
  (ModuleCat.{max u (t + 1)} (ULift.{t + 1} (Padic.coefficientExtensionIntegers l E)))
  _ _ (HasDerivedCategory.standard _)

/-- Exact sections on the ambient derived category, with the same standard localization.
Source: Stacks 015F (blueprint: lem-trf-point-pullback-representative-diagram). -/
def derivedSections := @Functor.mapDerivedCategory _ _ _
  (integralTowerHasDerivedCategory l E (Spec (.of k)))
  _ _ _ (moduleHasDerived l E) (sections l E k) _ _ _

/-- The canonical localization comparison for exact sections.
Source: Stacks 015F (blueprint: lem-trf-point-pullback-representative-diagram). -/
def sectionsFactors : DerivedCategory.Q ⋙ derivedSections l E k ≅
    sectionsComplex l E k ⋙ moduleQ l E :=
  @Functor.mapDerivedCategoryFactors _ _ _
    (integralTowerHasDerivedCategory l E (Spec (.of k)))
    _ _ _ (moduleHasDerived l E) (sections l E k) _ _ _

/-- The actual quotient tower followed by finite inverse image and scalar restriction.
Source: Stacks 06YY (blueprint: lem-trf-point-pullback-representative-diagram). -/
abbrev pullbackTower {Y : Scheme.{t}} (f : Spec (.of k) ⟶ Y) :=
  integralOperationsPullbackTowerFunctor.{t, u} l E f

/-- The entire evaluated tower B_f(P), including its actual transition maps.
Source: Stacks 0941 (blueprint: lem-trf-point-pullback-representative-diagram). -/
def sectionTower {Y : Scheme.{t}} (f : Spec (.of k) ⟶ Y) :=
  pullbackTower l E k f ⋙
    (Functor.whiskeringRight ℕᵒᵖ _ _).obj (sectionsComplex l E k)

/-- The chain functor P ↦ H(B_f(P)); maps are diagonal product maps.
Source: Stacks 0941 (blueprint: lem-trf-point-pullback-representative-diagram). -/
def sectionRoos {Y : Scheme.{t}} (f : Spec (.of k) ⟶ Y) :=
  sectionTower l E k f ⋙ integralOperationsRoosFunctor

/-- The two projection identities fixing the product comparison on both cone summands.
Here fst is the unshifted summand a, and snd is the shifted summand b.
Source: Stacks 0941 (blueprint: lem-trf-point-pullback-representative-diagram). -/
def RoosCoordinates {A : Type a} {B : Type b} [Category.{c} A] [Category.{d} B]
    [Abelian A] [Abelian B] [HasCountableProducts A] [HasCountableProducts B]
    (F : A ⥤ B) [F.Additive] (T : ℕᵒᵖ ⥤ CochainComplex A ℤ)
    (e : (F.mapHomologicalComplex (.up ℤ)).obj (integralOperationsRoos T) ≅
      integralOperationsRoos (T ⋙ F.mapHomologicalComplex (.up ℤ))) : Prop :=
  (∀ (n : ℕ) (i : ℤ), e.hom.f i ≫
      (CochainComplex.mappingCocone.fst
        (towerTransitionEndomorphism
          (K := fun m : ℕ ↦ (T ⋙ F.mapHomologicalComplex (.up ℤ)).obj (op m))
          (integralOperationsTowerStep (T ⋙ F.mapHomologicalComplex (.up ℤ))))).f i ≫
      (Pi.π (fun m : ℕ ↦ (T ⋙ F.mapHomologicalComplex (.up ℤ)).obj (op m)) n).f i =
    F.map ((CochainComplex.mappingCocone.fst
      (towerTransitionEndomorphism (K := fun m : ℕ ↦ T.obj (op m))
        (integralOperationsTowerStep T))).f i ≫
      (Pi.π (fun m : ℕ ↦ T.obj (op m)) n).f i)) ∧
  (∀ (n : ℕ) (i : ℤ), e.hom.f i ≫
      (CochainComplex.mappingCocone.snd
        (towerTransitionEndomorphism
          (K := fun m : ℕ ↦ (T ⋙ F.mapHomologicalComplex (.up ℤ)).obj (op m))
          (integralOperationsTowerStep (T ⋙ F.mapHomologicalComplex (.up ℤ))))).v
            i (i + -1) rfl ≫
      (Pi.π (fun m : ℕ ↦ (T ⋙ F.mapHomologicalComplex (.up ℤ)).obj (op m)) n).f
        (i + -1) =
    F.map ((CochainComplex.mappingCocone.snd
      (towerTransitionEndomorphism (K := fun m : ℕ ↦ T.obj (op m))
        (integralOperationsTowerStep T))).v i (i + -1) rfl ≫
      (Pi.π (fun m : ℕ ↦ T.obj (op m)) n).f (i + -1)))

/-- Strict naturality of a specified family of two-coordinate Roos comparisons.
Source: Stacks 0941 (blueprint: lem-trf-point-pullback-representative-diagram). -/
def RoosNaturality {A : Type a} {B : Type b} [Category.{c} A] [Category.{d} B]
    [Abelian A] [Abelian B] [HasCountableProducts A] [HasCountableProducts B]
    (F : A ⥤ B) [F.Additive]
    (comparison : ∀ T : ℕᵒᵖ ⥤ CochainComplex A ℤ,
      (F.mapHomologicalComplex (.up ℤ)).obj (integralOperationsRoos T) ≅
        integralOperationsRoos (T ⋙ F.mapHomologicalComplex (.up ℤ))) : Prop :=
  ∀ (T U : ℕᵒᵖ ⥤ CochainComplex A ℤ) (w : T ⟶ U),
    (F.mapHomologicalComplex (.up ℤ)).map (integralOperationsRoosMap w) ≫
        (comparison U).hom =
      (comparison T).hom ≫ integralOperationsRoosMap
        (((Functor.whiskeringRight ℕᵒᵖ _ _).obj
          (F.mapHomologicalComplex (.up ℤ))).map w)

/-- The canonical two-coordinate condition specialized to exact point sections.
Source: Stacks 0941 (blueprint: lem-trf-point-pullback-representative-diagram). -/
abbrev Coordinates
    (T : ℕᵒᵖ ⥤ CochainComplex (integralTowerModules.{t, u} l E (Spec (.of k))) ℤ)
    (e : (sectionsComplex l E k).obj (integralOperationsRoos T) ≅
      integralOperationsRoos (T ⋙ sectionsComplex l E k)) : Prop :=
  RoosCoordinates (sections l E k) T e

private theorem roosCoordinates_hom_eq
    {A : Type a} {B : Type b} [Category.{c} A] [Category.{d} B]
    [Abelian A] [Abelian B] [HasCountableProducts A] [HasCountableProducts B]
    (F : A ⥤ B) [F.Additive] (T : ℕᵒᵖ ⥤ CochainComplex A ℤ)
    (e : (F.mapHomologicalComplex (.up ℤ)).obj (integralOperationsRoos T) ≅
      integralOperationsRoos (T ⋙ F.mapHomologicalComplex (.up ℤ)))
    (he : RoosCoordinates F T e) : e.hom = scalarRoosMap F T := by
  refine (scalarRoosMap_existsUnique F T).unique ?_
    (scalarRoosMap_existsUnique F T).exists.choose_spec
  constructor
  · intro n
    apply HomologicalComplex.hom_ext
    intro i
    exact he.1 n i
  · intro i j hij n
    subst j
    exact he.2 n i

private theorem roosCoordinates_naturality
    {A : Type a} {B : Type b} [Category.{c} A] [Category.{d} B]
    [Abelian A] [Abelian B] [HasCountableProducts A] [HasCountableProducts B]
    (F : A ⥤ B) [F.Additive]
    (e : ∀ T : ℕᵒᵖ ⥤ CochainComplex A ℤ,
      (F.mapHomologicalComplex (.up ℤ)).obj (integralOperationsRoos T) ≅
        integralOperationsRoos (T ⋙ F.mapHomologicalComplex (.up ℤ)))
    (he : ∀ T, RoosCoordinates F T (e T)) : RoosNaturality F e := by
  intro T U w
  rw [roosCoordinates_hom_eq F T (e T) (he T),
    roosCoordinates_hom_eq F U (e U) (he U)]
  exact podReindexingRoosNaturality F w

private def roosNaturalityIso
    {A : Type a} {B : Type b} [Category.{c} A] [Category.{d} B]
    [Abelian A] [Abelian B] [HasCountableProducts A] [HasCountableProducts B]
    (F : A ⥤ B) [F.Additive]
    (e : ∀ T : ℕᵒᵖ ⥤ CochainComplex A ℤ,
      (F.mapHomologicalComplex (.up ℤ)).obj (integralOperationsRoos T) ≅
        integralOperationsRoos (T ⋙ F.mapHomologicalComplex (.up ℤ)))
    (he : RoosNaturality F e) :
    integralOperationsRoosFunctor ⋙ F.mapHomologicalComplex (.up ℤ) ≅
      (Functor.whiskeringRight ℕᵒᵖ _ _).obj (F.mapHomologicalComplex (.up ℤ)) ⋙
        integralOperationsRoosFunctor :=
  NatIso.ofComponents e (fun w ↦ he _ _ w)

open CochainComplex in
/-- The coordinate proof of `podReindexingRoosComparison` only needs products preserved. -/
private theorem roosComparison_isIso {A : Type a} {B : Type b} [Category.{c} A] [Category.{d} B]
    [Abelian A] [Abelian B] [HasCountableProducts A] [HasCountableProducts B]
    (F : A ⥤ B) [F.Additive] [PreservesLimitsOfShape (Discrete ℕ) F]
    (C : ℕᵒᵖ ⥤ CochainComplex A ℤ) : IsIso (scalarRoosMap F C) := by
  let G := F.mapHomologicalComplex (.up ℤ)
  let pc : G.obj (∏ᶜ fun n : ℕ ↦ C.obj (op n)) ⟶
      ∏ᶜ fun n : ℕ ↦ G.obj (C.obj (op n)) :=
    piComparison G (fun n : ℕ ↦ C.obj (op n))
  have hpc : IsIso pc := by dsimp only [pc]; infer_instance
  obtain ⟨hf, hs⟩ := podReindexingRoosCoordinates F C
  let : PreservesBinaryBiproducts F :=
    preservesBinaryBiproducts_of_preservesBiproducts F
  have hpcf (i : ℤ) : IsIso (pc.f i) := inferInstance
  have hi (i : ℤ) : IsIso ((scalarRoosMap F C).f i) := by
    let eY := coconeCoordinates (scalarRoosBoundary C) i
    let eX := coconeCoordinates (scalarRoosBoundary (C ⋙ G)) i
    have he : F.map eY.hom ≫
        (F.mapBiprod ((∏ᶜ fun n : ℕ ↦ C.obj (op n)).X i)
          ((∏ᶜ fun n : ℕ ↦ C.obj (op n)).X (i - 1))).hom =
        biprod.lift (F.map ((mappingCocone.fst (scalarRoosBoundary C)).f i))
          (F.map ((mappingCocone.snd (scalarRoosBoundary C)).v
            i (i - 1) (by omega))) :=
      biprod.map_lift_mapBiprod F _ _ _ _
    have hm : (scalarRoosMap F C).f i ≫ eX.hom =
        F.map eY.hom ≫ (F.mapBiprod ((∏ᶜ fun n : ℕ ↦ C.obj (op n)).X i)
            ((∏ᶜ fun n : ℕ ↦ C.obj (op n)).X (i - 1))).hom ≫
          biprod.map (pc.f i) (pc.f (i - 1)) := by
      rw [← Category.assoc, he]
      apply biprod.hom_ext
      · dsimp only [eX, coconeCoordinates]
        simp only [Category.assoc]
        erw [biprod.lift_fst, biprod.map_fst, biprod.lift_fst_assoc]
        exact congrArg (fun f ↦ f.f i) hf
      · dsimp only [eX, coconeCoordinates]
        simp only [Category.assoc]
        erw [biprod.lift_snd, biprod.map_snd, biprod.lift_snd_assoc]
        exact hs i
    have : IsIso ((scalarRoosMap F C).f i ≫ eX.hom) := by
      rw [hm]
      change IsIso (((F.mapIso eY) ≪≫
        F.mapBiprod ((∏ᶜ fun n : ℕ ↦ C.obj (op n)).X i)
          ((∏ᶜ fun n : ℕ ↦ C.obj (op n)).X (i - 1)) ≪≫
        biprod.mapIso (asIso (pc.f i)) (asIso (pc.f (i - 1)))).hom)
      infer_instance
    exact IsIso.of_isIso_comp_right _ eX.hom
  exact HomologicalComplex.Hom.isIso_of_components _

set_option linter.unusedSectionVars false in
/-- The sectionwise product comparison is a chain isomorphism, uniquely fixed on both
coordinates. This is the c_Z of the node, not a filler of a derived triangle.
Source: Stacks 0941 (blueprint: lem-trf-point-pullback-representative-diagram).
Proof (DAG step 2): products and finite sums of module sheaves are sectionwise.
The product comparison intertwines s, as its nth projection is Gamma(t_n)pr_(n+1).
On the two coordinates use that same comparison. It commutes with
(-db-(1-s)a,da), and the inverse product comparisons give its inverse.
Both projections determine a map out of the biproduct, proving uniqueness. -/
theorem sectionRoosComparison_existsUnique
    (T : ℕᵒᵖ ⥤ CochainComplex (integralTowerModules.{t, u} l E (Spec (.of k))) ℤ) :
    ∃! c : (sectionsComplex l E k).obj (integralOperationsRoos T) ≅
        integralOperationsRoos (T ⋙ sectionsComplex l E k), Coordinates l E k T c := by
  let F := sections l E k
  have : PreservesLimitsOfShape (Discrete ℕ) F := by
    dsimp only [F, sections, pointModuleSectionsOfUniverses]
    infer_instance
  have hi : IsIso (scalarRoosMap F T) := roosComparison_isIso F T
  let e := asIso (scalarRoosMap F T)
  have hc : Coordinates l E k T e := by
    constructor
    · intro n i
      exact congrArg (fun z ↦ z.f i)
        ((scalarRoosMap_existsUnique F T).exists.choose_spec.1 n)
    · intro n i
      exact (scalarRoosMap_existsUnique F T).exists.choose_spec.2 i (i + -1) rfl n
  refine ⟨e, hc, ?_⟩
  intro c hc'
  apply Iso.ext
  exact (roosCoordinates_hom_eq F T c hc').trans (roosCoordinates_hom_eq F T e hc).symm

/-- The unique isomorphism given by the canonical product comparison on both coordinates.
Source: Stacks 0941 (blueprint: lem-trf-point-pullback-representative-diagram). -/
def sectionRoosComparison
    (T : ℕᵒᵖ ⥤ CochainComplex (integralTowerModules.{t, u} l E (Spec (.of k))) ℤ) :=
  (sectionRoosComparison_existsUnique l E k T).exists.choose

/-- Completed pullback followed by exact sections on all derived objects.
Source: Stacks 06YY, 0941 (blueprint: lem-trf-point-pullback-representative-diagram). -/
def completedSections {Y : Scheme.{t}} (f : Spec (.of k) ⟶ Y) :=
  integralDerivedPullback.{t, u} l E f ⋙ derivedSections l E k

/-- The specified representative comparison v: apply Gamma to jmath, then c.
The arbitrary representative isomorphism q is used contravariantly first.
Source: Stacks 06YY, 0941 (blueprint: lem-trf-point-pullback-representative-diagram). -/
def representative {Y : Scheme.{t}} (f : Spec (.of k) ⟶ Y)
    (K : DerivedCategory (integralTowerModules.{t, u} l E Y))
    (P : (integralOperationsGoodComplex.{t, u} l E Y).FullSubcategory)
    (q : DerivedCategory.Q.obj P.obj ≅ K) :
    (completedSections l E k f).obj K ≅
      (moduleQ l E).obj ((sectionRoos l E k f).obj P.obj) :=
  (completedSections l E k f).mapIso q.symm ≪≫
    (derivedSections l E k).mapIso ((integralDerivedPullbackComparison.{t, u} l E f).app P) ≪≫
    (sectionsFactors l E k).app
      ((integralOperationsPullbackComplexFunctor.{t, u} l E f).obj P.obj) ≪≫
    (moduleQ l E).mapIso
      (sectionRoosComparison l E k ((pullbackTower l E k f).obj P.obj))

/-- The canonical counit of derived reduction, as supplied with ordinary scalar extension.
The normalized scalar API selects the same universal witness and counit.
Source: Stacks 06YY (blueprint: lem-trf-point-pullback-representative-diagram). -/
def reductionCounit (Y : Scheme.{t}) (n : ℕ) :=
  scalarReductionCounit l E Y n

/-- The canonical derived-reduction counit is invertible on this complex.
This predicate retains the specified counit, not an arbitrary level isomorphism.
Source: Stacks 06YY (blueprint: lem-trf-point-pullback-representative-diagram). -/
def ReductionComputedBy (Y : Scheme.{t}) (n : ℕ)
    (P : CochainComplex (integralTowerModules.{t, u} l E Y) ℤ) : Prop :=
  IsIso ((reductionCounit l E Y n).app
    ((HomotopyCategory.quotient (integralTowerModules.{t, u} l E Y) (.up ℤ)).obj P))

/-- Finite inverse image is exact in the actual independent coefficient universe.
Source: Stacks 03D2 (blueprint: lem-trf-point-pullback-representative-diagram). -/
instance finitePullbackLimits {Y : Scheme.{t}} (f : Spec (.of k) ⟶ Y) (n : ℕ) :
    PreservesFiniteLimits (integralOperationsLevelPullback l E f n) :=
  (coefficientProEtaleModulePullback_exact.{t, u} f
    (CommRingCat.of (ULift.{t + 1} (Padic.coefficientExtensionRing l E (n + 1))))).1

/-- Finite inverse image preserves finite colimits as well as finite limits.
Source: Stacks 03D2 (blueprint: lem-trf-point-pullback-representative-diagram). -/
instance finitePullbackColimits {Y : Scheme.{t}} (f : Spec (.of k) ⟶ Y) (n : ℕ) :
    PreservesFiniteColimits (integralOperationsLevelPullback l E f n) :=
  (coefficientProEtaleModulePullback_exact.{t, u} f
    (CommRingCat.of (ULift.{t + 1} (Padic.coefficientExtensionRing l E (n + 1))))).2

/-- Derived products of ordinary integral modules, using exact termwise products.
Source: Stacks 07KC (blueprint: lem-trf-point-pullback-representative-diagram). -/
instance moduleDerivedProducts : HasCountableProducts
    (@DerivedCategory
      (ModuleCat.{max u (t + 1)} (ULift.{t + 1} (Padic.coefficientExtensionIntegers l E)))
      _ _ (HasDerivedCategory.standard _)) :=
  (derivedCategory_countableProducts_core.{0}
    (ModuleCat.{max u (t + 1)} (ULift.{t + 1} (Padic.coefficientExtensionIntegers l E)))).choose

attribute [local irreducible] integralOperationsPullbackTowerFunctor
  integralOperationsRoosFunctor integralDerivedPullback sections derivedSections DerivedCategory.Q

attribute [local irreducible] CategoryTheory.constantSheaf SheafOfModules.changeOfRings

/-- The whole-tower point-section diagram on every good representative, including all
roof morphisms and the derived-limit assertion. A derived representative q is an
isomorphism Q(P) ≅ K; thus every quasi-isomorphism P → K gives one after localization.
There is no boundedness, constructibility, completeness or isomorphism assumption on f.

Source: blueprint main-20261015, sec-trace-formula/sk-d-weil,
prop-trf-rational-frobenius-integral-model.proof.md, clause (3); Stacks 06YS, 06YY,
0941 (blueprint: lem-trf-point-pullback-representative-diagram).

Proof, in the five DAG steps:
1. Apply the K-flat computation supplied with the canonical derived-reduction witness
   to its specified counit. The quotient tower, exact finite inverse image, and scalar
   restriction are the recorded constructions and retain their actual transitions.
2. Normalize the section comparison by scalarRoosMap. Evaluation and scalar restriction
   preserve products; in each degree its matrix on the two mapping-cocone coordinates
   is the pair of product comparisons, hence invertible. Coordinate uniqueness fixes
   the chosen comparison, and the strict naturality of scalarRoosMap proves its
   naturality on every tower map.
3. Compose the specified completed-pullback comparison, the exact-sections
   factorization, and this natural Roos comparison to obtain a natural isomorphism e
   on all good representatives. By definition, representative at q is the image of
   q inverse followed by e. Naturality of e gives the chain-map square. If u is a
   quasi-isomorphism, its image under completedSections is invertible; the same
   naturality square implies that moduleQ(sectionRoos(u)) is invertible. Localization
   reflects quasi-isomorphisms, giving the asserted invariance and descent.
4. For the roof formula, apply the chain-map square to both legs from (W,identity).
   Precompose by completedSections(Q(a) q), substitute the given expression for h,
   and cancel the two invertible left legs. Mathlib's right fraction theorem gives
   a chain roof for every derived arrow. Resolve its middle by a flat-term K-flat
   complex, convert tensor-flatness by the canonical site-tensor comparison, and
   compose both legs with that resolution. Its localization cancels in the fraction.
5. Apply the generic localized Roos triangle to the entire section tower. Exact
   countable products give the comparison of its localized products with derived
   products, retaining every projection. These projections identify the middle map
   with 1-s for the actual localized transitions. Transporting the localized
   distinguished mapping-cocone triangle yields exactly IsDerivedLimit. -/
theorem pointPullbackRepresentativeDiagram
    (_hl : IsUnit (l : k)) {Y : Scheme.{t}} (f : Spec (.of k) ⟶ Y)
    (_hY : ∀ y : Y, IsUnit (l : Y.residueField y)) :
    (∀ (P : (integralOperationsGoodComplex.{t, u} l E Y).FullSubcategory) (n : ℕ),
      ReductionComputedBy l E Y n P.obj) ∧
    (∀ T : ℕᵒᵖ ⥤ CochainComplex (integralTowerModules.{t, u} l E (Spec (.of k))) ℤ,
      Coordinates l E k T (sectionRoosComparison l E k T)) ∧
    RoosNaturality (sections l E k) (sectionRoosComparison l E k) ∧
    ∃ hInv : ∀ (P P' : (integralOperationsGoodComplex.{t, u} l E Y).FullSubcategory)
        (u : P.obj ⟶ P'.obj), QuasiIso u →
          QuasiIso ((sectionRoos l E k f).map u),
      (∃ e : integralOperationsGoodLocalization.{t, u} l E Y ⋙ completedSections l E k f ≅
          (integralOperationsGoodComplex.{t, u} l E Y).ι ⋙ sectionRoos l E k f ⋙ moduleQ l E,
        ∀ P : (integralOperationsGoodComplex.{t, u} l E Y).FullSubcategory,
          e.app P = representative l E k f (DerivedCategory.Q.obj P.obj) P (Iso.refl _)) ∧
      (∀ (K K' : DerivedCategory (integralTowerModules.{t, u} l E Y))
        (P P' : (integralOperationsGoodComplex.{t, u} l E Y).FullSubcategory)
        (q : DerivedCategory.Q.obj P.obj ≅ K) (q' : DerivedCategory.Q.obj P'.obj ≅ K')
        (u : P.obj ⟶ P'.obj) (h : K ⟶ K'),
        DerivedCategory.Q.map u ≫ q'.hom = q.hom ≫ h →
        (completedSections l E k f).map h ≫ (representative l E k f K' P' q').hom =
          (representative l E k f K P q).hom ≫
            (moduleQ l E).map ((sectionRoos l E k f).map u)) ∧
      (∀ (K K' : DerivedCategory (integralTowerModules.{t, u} l E Y))
        (P P' W : (integralOperationsGoodComplex.{t, u} l E Y).FullSubcategory)
        (q : DerivedCategory.Q.obj P.obj ≅ K) (q' : DerivedCategory.Q.obj P'.obj ≅ K')
        (a : W.obj ⟶ P.obj) (b : W.obj ⟶ P'.obj) (ha : QuasiIso a) (h : K ⟶ K'),
        h = q.inv ≫
          inv (I := (DerivedCategory.isIso_Q_map_iff_quasiIso _ a).mpr ha)
            (DerivedCategory.Q.map a) ≫ DerivedCategory.Q.map b ≫ q'.hom →
        (completedSections l E k f).map h ≫ (representative l E k f K' P' q').hom =
          (representative l E k f K P q).hom ≫
            inv (I := (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).mpr (hInv W P a ha))
              ((moduleQ l E).map ((sectionRoos l E k f).map a)) ≫
            (moduleQ l E).map ((sectionRoos l E k f).map b)) ∧
      (∀ (P P' : (integralOperationsGoodComplex.{t, u} l E Y).FullSubcategory)
        (h : DerivedCategory.Q.obj P.obj ⟶ DerivedCategory.Q.obj P'.obj),
        ∃ (W : (integralOperationsGoodComplex.{t, u} l E Y).FullSubcategory)
          (a : W.obj ⟶ P.obj) (b : W.obj ⟶ P'.obj) (ha : QuasiIso a),
          h = inv (I := (DerivedCategory.isIso_Q_map_iff_quasiIso _ a).mpr ha)
            (DerivedCategory.Q.map a) ≫ DerivedCategory.Q.map b) ∧
      (∀ P : (integralOperationsGoodComplex.{t, u} l E Y).FullSubcategory,
        IsDerivedLimit
          (K := fun n : ℕ ↦ (moduleQ l E).obj
            (((sectionTower l E k f).obj P.obj).obj (op n)))
          (fun n : ℕ ↦ (moduleQ l E).map
            (integralOperationsTowerStep ((sectionTower l E k f).obj P.obj) n))
          ((moduleQ l E).obj ((sectionRoos l E k f).obj P.obj))) := by
  classical
  have hc (T) : Coordinates l E k T (sectionRoosComparison l E k T) :=
    (sectionRoosComparison_existsUnique l E k T).exists.choose_spec
  have hn : RoosNaturality (sections l E k) (sectionRoosComparison l E k) :=
    roosCoordinates_naturality (sections l E k) (sectionRoosComparison l E k) hc
  let c := roosNaturalityIso (sections l E k) (sectionRoosComparison l E k) hn
  let e₁ := Functor.isoWhiskerRight (integralDerivedPullbackComparison l E f)
    (derivedSections l E k)
  let e₂ := Functor.isoWhiskerLeft ((integralOperationsGoodComplex l E Y).ι ⋙
    integralOperationsPullbackComplexFunctor l E f) (sectionsFactors l E k)
  let e₃ := Functor.isoWhiskerRight
    (Functor.isoWhiskerLeft ((integralOperationsGoodComplex l E Y).ι ⋙ pullbackTower l E k f) c)
    (moduleQ l E)
  let e : integralOperationsGoodLocalization l E Y ⋙ completedSections l E k f ≅
      (integralOperationsGoodComplex l E Y).ι ⋙ sectionRoos l E k f ⋙ moduleQ l E :=
    e₁ ≪≫ e₂ ≪≫ e₃
  have hrep (K) (P : (integralOperationsGoodComplex l E Y).FullSubcategory)
      (q : DerivedCategory.Q.obj P.obj ≅ K) :
      (representative l E k f K P q).hom =
        (completedSections l E k f).map q.inv ≫ (e.app P).hom := by
    simp only [representative, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom]
    rfl
  have he (P : (integralOperationsGoodComplex l E Y).FullSubcategory) :
      e.app P = representative l E k f (DerivedCategory.Q.obj P.obj) P (Iso.refl _) := by
    apply Iso.ext
    rw [hrep]
    simp
  have hnat (K K') (P P' : (integralOperationsGoodComplex l E Y).FullSubcategory)
      (q : DerivedCategory.Q.obj P.obj ≅ K) (q' : DerivedCategory.Q.obj P'.obj ≅ K')
      (u : P.obj ⟶ P'.obj) (h : K ⟶ K')
      (hw : DerivedCategory.Q.map u ≫ q'.hom = q.hom ≫ h) :
      (completedSections l E k f).map h ≫ (representative l E k f K' P' q').hom =
        (representative l E k f K P q).hom ≫
          (moduleQ l E).map ((sectionRoos l E k f).map u) := by
    have hq : h ≫ q'.inv = q.inv ≫ DerivedCategory.Q.map u := by
      calc
        h ≫ q'.inv = q.inv ≫ (q.hom ≫ h) ≫ q'.inv := by simp
        _ = q.inv ≫ (DerivedCategory.Q.map u ≫ q'.hom) ≫ q'.inv := by rw [← hw]
        _ = q.inv ≫ DerivedCategory.Q.map u := by simp
    have hu := e.hom.naturality (ObjectProperty.homMk (X := P) (Y := P') u)
    change (completedSections l E k f).map (DerivedCategory.Q.map u) ≫ (e.app P').hom =
      (e.app P).hom ≫ (moduleQ l E).map ((sectionRoos l E k f).map u) at hu
    rw [hrep, hrep, ← Category.assoc, ← Functor.map_comp, hq, Functor.map_comp,
      Category.assoc, hu, Category.assoc]
  have hInv (P P' : (integralOperationsGoodComplex l E Y).FullSubcategory)
      (u : P.obj ⟶ P'.obj) (hu : QuasiIso u) :
      QuasiIso ((sectionRoos l E k f).map u) := by
    let : QuasiIso u := hu
    have hu' := e.hom.naturality (ObjectProperty.homMk (X := P) (Y := P') u)
    change (completedSections l E k f).map (DerivedCategory.Q.map u) ≫ (e.app P').hom =
      (e.app P).hom ≫ (moduleQ l E).map ((sectionRoos l E k f).map u) at hu'
    apply (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).1
    have : IsIso ((e.app P).hom ≫ (moduleQ l E).map ((sectionRoos l E k f).map u)) := by
      rw [← hu']
      infer_instance
    exact IsIso.of_isIso_comp_left (e.app P).hom _
  refine And.intro ?_ (And.intro hc (And.intro hn (Exists.intro hInv
    (And.intro ⟨e, he⟩ (And.intro hnat (And.intro ?_ (And.intro ?_ ?_)))))))
  · intro P n
    simpa only [ReductionComputedBy, reductionCounit] using
      (unrestrictedTowerCounit_isIso l E Y n P.obj P.property.1)
  · intro K K' P P' W q q' a b ha h hh
    let : QuasiIso a := ha
    let : IsIso ((moduleQ l E).map ((sectionRoos l E k f).map a)) :=
      (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2 (hInv W P a ha)
    have hA := hnat (DerivedCategory.Q.obj W.obj) K W P
      (Iso.refl (DerivedCategory.Q.obj W.obj)) q a (DerivedCategory.Q.map a ≫ q.hom) (by simp)
    have hB := hnat (DerivedCategory.Q.obj W.obj) K' W P'
      (Iso.refl (DerivedCategory.Q.obj W.obj)) q' b (DerivedCategory.Q.map b ≫ q'.hom) (by simp)
    apply (cancel_epi ((completedSections l E k f).map
      (DerivedCategory.Q.map a ≫ q.hom))).1
    rw [← Functor.map_comp_assoc]
    have hw : (DerivedCategory.Q.map a ≫ q.hom) ≫ h =
        DerivedCategory.Q.map b ≫ q'.hom := by
      rw [hh]
      simp only [Category.assoc, Iso.hom_inv_id_assoc, IsIso.hom_inv_id_assoc]
    rw [hw]
    simp only [← Category.assoc]
    rw [hA]
    simpa only [Category.assoc, IsIso.hom_inv_id_assoc] using hB
  · intro P P' h
    obtain ⟨Z, a, ha, b, hb⟩ := DerivedCategory.right_fac h
    let := ha
    obtain ⟨W, r, hk, hf, hr, _⟩ :=
      CochainComplex.exists_isKFlatResolutionIndependentCoefficients
        (R := completedIntegralCommRingSheafUnrestricted l E Y) Z
    let := hr
    have hW : integralOperationsGoodComplex l E Y W := by
      refine ⟨hk, fun i ↦ ?_⟩
      exact (exactFunctor _ _).prop_of_iso
        (SheafOfModules.siteSheafTensorRightIso
          (completedIntegralCommRingSheafUnrestricted l E Y) (W.X i)).symm (hf i)
    have hra : QuasiIso (r ≫ a) := by
      apply (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).1
      rw [Functor.map_comp]
      infer_instance
    refine ⟨⟨W, hW⟩, r ≫ a, r ≫ b, hra, ?_⟩
    rw [hb]
    simp only [Functor.map_comp, IsIso.inv_comp, Category.assoc,
      IsIso.inv_hom_id_assoc]
  · intro P
    simpa only [sectionRoos, Functor.comp_obj, integralOperationsRoosFunctor] using
      (roos_derivedLimit ((sectionTower l E k f).obj P.obj))

end WeilConjectures.PointPullbackRepresentative
