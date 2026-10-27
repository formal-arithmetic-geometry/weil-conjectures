module

public import Sheaf.Paper.PodMixedSupportCupProduct
public import Sheaf.Algebra.Homology.OrdinaryDerivedChangeOfRings
public import Sheaf.Paper.IntegralScalarExtensionUniverses
public import Sheaf.Paper.PointSectionsDerivedReduction
public import Sheaf.Paper.AdmissibleCupCoefficientPassages
public import Sheaf.Paper.MixedCupCoefficientData
public import Sheaf.Paper.BasicOperationsCoefficientReduction
import Sheaf.Paper.CompactSupportCondensedRealization

/-! # Coefficient comparisons for the mixed-support cup

Source: current blueprint, sec-six-functors/sk-thm-sf-package,
def-pod-mixed-support-cup-product, final coefficient compatibility sentence
(blueprint: def-sf-mixed-cup-ringed-normalization).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [-instance] WeilConjectures.IntegralHom.derivedCategory
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open CategoryTheory.MonoidalCategory
open scoped ChangeOfRings
namespace WeilConjectures.MixedCupCoefficientChange
open scoped WeilConjectures.MixedCupCoefficientChange

variable {D : FiniteFieldDatum.{u}} (C : D.CoefficientDatum)

/-- Only finite and completed integral stages are realized as ringed modules.
Source: proof steps 2--4 (blueprint: def-sf-mixed-cup-ringed-normalization). -/
def IsRinged : Stage C → Prop
  | .finite _ _ => True
  | .integral _ => True
  | _ => False

/-- Ambient inclusion at a ringed stage, without a field-stage ambient embedding.
Source: proof steps 2--3 (blueprint: def-sf-mixed-cup-ringed-normalization). -/
def ringedForget (W : Scheme.{u}) : (a : Stage C) → IsRinged C a →
    ambient C W a ⥤ DerivedCategory (pbcModules.{u} W ((coefficients C a).ring W))
  | .finite _ _, _ => 𝟭 _
  | .integral F, _ => (sfIntegralConstructible C.l (FieldAt C F) W).ι

/-- The source of a ringed elementary passage is a ringed stage.
Source: proof steps 2--3 (blueprint: def-sf-mixed-cup-ringed-normalization).
Proof: inspect the three constructors; both endpoints are finite or integral. -/
theorem ringedSource {a b : Stage C} {f : Passage C a b} (hf : RingedPassage C f) :
    IsRinged C a := by
  cases hf <;> trivial

/-- The target of a ringed elementary passage is a ringed stage.
Source: proof steps 2--3 (blueprint: def-sf-mixed-cup-ringed-normalization).
Proof: inspect the three constructors; both endpoints are finite or integral. -/
theorem ringedTarget {a b : Stage C} {f : Passage C a b} (hf : RingedPassage C f) :
    IsRinged C b := by
  cases hf <;> trivial

/-- Scalar completion's normalized ordinary-ring presentation exists.
Source: proof step 3; lem-fix-operation-reduction
(blueprint: def-sf-mixed-cup-ringed-normalization).
Proof: the ordinary tensor functors have the same pure-tensor generators and
relations. Their derived functors are exact and their universal counits identify
termwise models. These give the displayed pure-tensor and counit equations. -/
theorem scalarTransport_exists (F G : Padic.FiniteCoefficientFields C.l C.Qbar)
    (h : F ≤ G) (W : Scheme.{u}) :
    Nonempty (OperationScalarTransport C.l (FieldAt C F) (FieldAt C G)
      (AlgebraicallyClosedCoefficients.coefficientInclusion C.l C.Qbar F G h) W) := by
  let : NormedField (FieldAt C F) := spectralNorm.normedField (Padic C.l) (FieldAt C F)
  let : NormedAlgebra (Padic C.l) (FieldAt C F) :=
    spectralNorm.normedAlgebra (Padic C.l) (FieldAt C F)
  let : NormedField (FieldAt C G) := spectralNorm.normedField (Padic C.l) (FieldAt C G)
  let : NormedAlgebra (Padic C.l) (FieldAt C G) :=
    spectralNorm.normedAlgebra (Padic C.l) (FieldAt C G)
  exact CompactSupportCondensedRealization.scalarModelTransport_nonempty C.l
    (FieldAt C F) (FieldAt C G)
    (AlgebraicallyClosedCoefficients.coefficientInclusion C.l C.Qbar F G h) W

/-- Scalar completion is the ordinary derived scalar functor on constructible inputs.
The transport is fixed by pure tensors and its universal counit.
Source: proof step 3 (blueprint: def-sf-mixed-cup-ringed-normalization). -/
def ringedScalarCoordinates (X : SixFunctorSpace D) [IsSeparated X.obj.hom]
    {a b : Stage C} (f : Passage C a b) (hf : RingedPassage C f)
    (K : (domain C X.obj.left a).FullSubcategory) :
    (ringedForget C X.obj.left b (ringedTarget C hf)).obj ((change C X f).obj K).obj ≅
      (pbcDerivedExtend ((ringedChange C f hf).map X.obj.left)).obj
        ((ringedForget C X.obj.left a (ringedSource C hf)).obj K.obj) :=
  by
    cases hf with
    | finite φ => exact Iso.refl _
    | reduction F n => exact (PurCompactSupport.finiteReductionIso C.l (FieldAt C F)
        X.obj.left n).symm.app K.obj.obj
    | integral h => exact
        (operationConstructibleScalarTransport C.l _ _
          (AlgebraicallyClosedCoefficients.coefficientInclusion C.l C.Qbar _ _ h)
          X.obj.left (scalarTransport_exists C _ _ h X.obj.left).some).app K.obj

/-- The fixed ambient direct or compact-support functor of a coefficient system.
Source: proof steps 2--3 (blueprint: def-sf-mixed-cup-ringed-normalization). -/
def ringedOperation (X : SixFunctorSpace D) [IsSeparated X.obj.hom]
    (c : Compactification (sixFunctorStructure X).hom.left) (compact : Bool) (a : Stage C) :=
  if compact then PurCompactSupport.image (coefficients C a) c
  else PurCompactSupport.push (coefficients C a) X.obj.hom

/-- The coefficient comparison is exactly the proper/open scalar mate, or the
ordinary counit-transpose mate. Neither branch supplies a free isomorphism.
Source: proof steps 2 and 5 (blueprint: def-sf-mixed-cup-ringed-normalization). -/
def ringedOperationMap (X : SixFunctorSpace D) [IsSeparated X.obj.hom]
    (c : Compactification (sixFunctorStructure X).hom.left) (compact : Bool)
    {a b : Stage C} (f : Passage C a b) (hf : RingedPassage C f) :
    ringedOperation C X c compact a ⋙
        pbcDerivedExtend ((ringedChange C f hf).map (Spec (.of D.k))) ⟶
      pbcDerivedExtend ((ringedChange C f hf).map X.obj.left) ⋙
        ringedOperation C X c compact b :=
  match compact with
  | true => PurCompactSupport.comparison (ringedChange C f hf) c
  | false => PurCompactSupport.properComparison (ringedChange C f hf) X.obj.hom

/-- Completed direct image has exactly the recorded coefficient structure map.
Source: proof step 3 (blueprint: def-sf-mixed-cup-ringed-normalization).
Proof: the ringed structural map is the transpose of completedPullMap. The
adjunction inverse laws identify it with sfCompletedCoefficientMap. Thus the
ordinary pushforward functors are equal, hence so are their chosen derived images. -/
theorem integralPush_eq (F : Padic.FiniteCoefficientFields C.l C.Qbar)
    (X : SixFunctorSpace D) :
    sfCompletedDerivedDirectImage C.l (FieldAt C F) X.obj.hom =
      PurCompactSupport.push (coefficients C (.integral F)) X.obj.hom := by
  have hmap : proEtaleRingDirectImageMap X.obj.hom
      ((PurCompactSupport.completed C.l (FieldAt C F)).ring (Spec (.of D.k)))
      ((PurCompactSupport.completed C.l (FieldAt C F)).ring X.obj.left)
      ((PurCompactSupport.completed C.l (FieldAt C F)).pull X.obj.hom) =
        sfCompletedCoefficientMap C.l (FieldAt C F) X.obj.hom := by
    exact (proEtaleSheafAdjunction X.obj.hom CommRingCat.{u + 1}).homEquiv _ _
      |>.apply_symm_apply (sfCompletedCoefficientMap C.l (FieldAt C F) X.obj.hom)
  change (sfCompletedModuleDirectImage C.l (FieldAt C F) X.obj.hom).rightDerivedFunctor =
    (proEtaleRingModuleDirectImage X.obj.hom _ _ _).rightDerivedFunctor
  congr 1
  unfold sfCompletedModuleDirectImage proEtaleRingModuleDirectImage
  dsimp only [coefficients, PurCompactSupport.completed] at *
  rw [hmap]

/-- Sheaf cohomology before its exact point fibre, restricted to the given domain.
Source: proof step 7 (blueprint: def-sf-mixed-cup-ringed-normalization). -/
def ringedSheafCohomology (S : Operations C) (X : SixFunctorSpace D)
    [IsSeparated X.obj.hom] (c : Compactification (sixFunctorStructure X).hom.left)
    (compact : Bool) : (a : Stage C) → (ha : IsRinged C a) →
    (domain C X.obj.left a).FullSubcategory ⥤
      DerivedCategory (pbcModules.{u} (Spec (.of D.k)) ((coefficients C a).ring (Spec (.of D.k))))
  | .finite F n, _ =>
      ObjectProperty.lift (intrinsicFiniteTorsionConstructible.{u} C.l (FieldAt C F) (n + 1)
        (Nat.succ_le_succ (Nat.zero_le n)) X.obj.left)
        (domain C X.obj.left (.finite F n)).ι (fun K ↦ K.property.1) ⋙
      (if compact then (S F n).finite.support (sixFunctorStructure X) c
        else (S F n).finite.direct (sixFunctorStructure X)) ⋙
      (intrinsicFiniteTorsionConstructible.{u} C.l (FieldAt C F) (n + 1)
        (Nat.succ_le_succ (Nat.zero_le n)) (Spec (.of D.k))).ι
  | .integral F, _ => (domain C X.obj.left (.integral F)).ι ⋙
      (if compact then (S F 0).higher.integral.support (sixFunctorStructure X) c
        else (S F 0).higher.integral.direct (sixFunctorStructure X)) ⋙
      (sfIntegralConstructible C.l (FieldAt C F) (Spec (.of D.k))).ι

/-- Coordinates from the prescribed normalized operations to the actual proper/open
or ordinary ringed image. Integral support uses the fixed chosen-value equality,
the fixed recorded support value equality, and recordedIdentification.
Source: proof steps 2--3 (blueprint: def-sf-mixed-cup-ringed-normalization). -/
def ringedOperationCoordinates (S : Operations C) (X : SixFunctorSpace D)
    [IsSeparated X.obj.hom] (c : Compactification (sixFunctorStructure X).hom.left)
    (compact : Bool) : (a : Stage C) → (ha : IsRinged C a) →
    (K : (domain C X.obj.left a).FullSubcategory) →
    (ringedSheafCohomology C S X c compact a ha).obj K ≅
      (ringedOperation C X c compact a).obj ((ringedForget C X.obj.left a ha).obj K.obj)
  | .finite F n, _, K => by
      letI := proEtaleConstantModuleDirectImage_additive X.obj.hom
        (Padic.coefficientExtensionRing C.l (FieldAt C F) (n + 1))
      cases compact
      · exact ((S F n).finiteDirectImage (sixFunctorStructure X)).app
          ⟨K.obj, K.property.1⟩ ≪≫
          (Functor.rightDerivedFunctorNatIso
            (eqToIso (PurCompactSupport.finiteDirectImage_eq C.l (FieldAt C F) n
              X.obj.hom))).symm.app K.obj
      · exact ((S F n).finiteSupport (sixFunctorStructure X) c).app
          ⟨K.obj, K.property.1⟩ ≪≫
          (PurCompactSupport.finiteImageIso C.l (FieldAt C F) n c).symm.app K.obj
  | .integral F, _, K => by
      letI : LocallyOfFiniteType (sixFunctorStructure X).hom.left := X.property.1
      letI : QuasiCompact (sixFunctorStructure X).hom.left := X.property.2
      letI : LocallyOfFiniteType X.obj.hom := X.property.1
      letI : QuasiCompact X.obj.hom := X.property.2
      letI : (Spec (.of D.k)).Over (Spec (.of D.k)) := ⟨𝟙 _⟩
      letI : X.obj.hom.IsOver (Spec (.of D.k)) := ⟨Category.comp_id _⟩
      letI : IsSeparated (sixFunctorStructure X).hom.left :=
        inferInstanceAs (IsSeparated X.obj.hom)
      letI : IsSeparated (X.obj.left ↘ Spec (.of D.k)) :=
        inferInstanceAs (IsSeparated X.obj.hom)
      cases compact
      · exact ((S F 0).higher.integralDirectImage (sixFunctorStructure X)).app K.obj ≪≫
          (eqToIso (integralPush_eq C F X)).app K.obj.obj
      · exact eqToIso (congrArg
          (fun M : sfIntegralConstructibleCategory C.l (FieldAt C F) (Spec (.of D.k)) ↦ M.obj)
          (((S F 0).higher.supportConstruction (sixFunctorStructure X)
            (PurCompactSupport.coefficientPrimeUnit C.l D C.different) c).choose_spec.2.2.1
              K.obj)) ≪≫
          eqToIso (congrArg
            (fun M : sfIntegralConstructibleCategory C.l (FieldAt C F) (Spec (.of D.k)) ↦ M.obj)
            (sfCompactSupportFiniteIntegralFunctor_obj C.l D.k
              (PurCompactSupport.coefficientPrimeUnit C.l D C.different) c (FieldAt C F)
              K.obj)).symm ≪≫
          ((PurCompactSupport.recordedIdentification C.l (FieldAt C F) D C.different
            X.obj.hom c).symm.app ⟨K.obj.obj, K.property⟩)

/-- Exact point-fibre coordinates at finite and integral stages.
Source: proof step 7 (blueprint: def-sf-mixed-cup-ringed-normalization). -/
def ringedCohomologyCoordinates (S : Operations C) (X : SixFunctorSpace D)
    [IsSeparated X.obj.hom] (c : Compactification (sixFunctorStructure X).hom.left)
    (compact : Bool) : (a : Stage C) → (ha : IsRinged C a) →
    cohomology C S X c compact a ≅
      ringedSheafCohomology C S X c compact a ha ⋙
        (sectionFunctor (D := D) ((coefficients C a).ring (Spec (.of D.k)))
          (ring C a) (sectionMap C a)).mapDerivedCategory
  | .finite _ _, _ => Iso.refl _
  | .integral F, _ => by
      exact Functor.associator (domain C X.obj.left (.integral F)).ι
        ((if compact then (S F 0).higher.integral.support (sixFunctorStructure X) c
          else (S F 0).higher.integral.direct (sixFunctorStructure X)) ⋙
          (sfIntegralConstructible C.l (FieldAt C F) (Spec (.of D.k))).ι)
        (pointFibreIntegralAmbient D C.l (FieldAt C F))

/-- The actual ringed map, composed with its point scalar identification and with
both prescribed operation realizations. This component equality fixes u_c and u_o,
including integral reduction, and rules out a per-stage sign twist.
Source: proof steps 2, 3, 5 and 7 (blueprint: def-sf-mixed-cup-ringed-normalization). -/
def RingedCohomologyNormalized (S : Operations C) (X : SixFunctorSpace D)
    [IsSeparated X.obj.hom] (c : Compactification (sixFunctorStructure X).hom.left)
    (uc : ∀ {a b : Stage C} (f : Passage C a b) (compact : Bool),
      cohomology C S X c compact a ⋙ pointChange C f ≅
        change C X f ⋙ cohomology C S X c compact b) : Prop :=
  ∀ {a b : Stage C} (f : Passage C a b) (hf : RingedPassage C f) (compact : Bool)
    (K : (domain C X.obj.left a).FullSubcategory),
    (pointChange C f).map
        ((ringedCohomologyCoordinates C S X c compact a (ringedSource C hf)).hom.app K) ≫
      (ringedPoint C f hf).hom.app
        ((ringedSheafCohomology C S X c compact a (ringedSource C hf)).obj K) ≫
      (sectionFunctor (D := D) ((coefficients C b).ring (Spec (.of D.k)))
        (ring C b) (sectionMap C b)).mapDerivedCategory.map
          ((pbcDerivedExtend ((ringedChange C f hf).map (Spec (.of D.k)))).map
              (ringedOperationCoordinates C S X c compact a (ringedSource C hf) K).hom ≫
            (ringedOperationMap C X c compact f hf).app
              ((ringedForget C X.obj.left a (ringedSource C hf)).obj K.obj)) =
      (uc f compact).hom.app K ≫
        (ringedCohomologyCoordinates C S X c compact b (ringedTarget C hf)).hom.app
          ((change C X f).obj K) ≫
        (sectionFunctor (D := D) ((coefficients C b).ring (Spec (.of D.k)))
          (ring C b) (sectionMap C b)).mapDerivedCategory.map
            ((ringedOperationCoordinates C S X c compact b (ringedTarget C hf)
                ((change C X f).obj K)).hom ≫
              (ringedOperation C X c compact b).map (ringedScalarCoordinates C X f hf K).hom)

end WeilConjectures.MixedCupCoefficientChange
