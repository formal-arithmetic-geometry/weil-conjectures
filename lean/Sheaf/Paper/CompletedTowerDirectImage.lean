/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF groups Q08 and Q31
-/
module

public import Sheaf.Paper.AdicCoefficientDatum
public import Sheaf.Paper.CompletedTowerPullback
public import Sheaf.Paper.CompletedTowerDerivedLimitFunctor
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
import WeilConjectures.Algebra.Homology.TowerEvaluationKInjective
import Mathlib.Algebra.Homology.Functor
import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import Sheaf.CategoryTheory.SiteCoveringAxioms
import Sheaf.CategoryTheory.KInjectiveTotalDerived
import Sheaf.Paper.PbcDerivedProductRepresentation
import Sheaf.Paper.KoszulReconstruction
import Sheaf.Paper.PbcRoosTriangle
import Sheaf.AlgebraicGeometry.ProEtaleFiniteCoefficientDirectImage
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution

/-!
# Total direct image of strict completed-coefficient towers

Source: blueprint sec-proper-base-change/sk-thm-properbasechange, order 1276;
Stacks Project, Tag 099N (blueprint: prop-weil-pbc-direct-image-limits).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme

variable {X Y : Scheme.{u}} (f : X ⟶ Y) {A : Type (u + 1)} [CommRing A]
  (d : AdicCoefficientDatum A)

/-- The completed coefficient direct-image structure map adjoint to c_f.
Source: blueprint order 1276 (blueprint: prop-weil-pbc-direct-image-limits). -/
def completedCoefficientDirectImageMap :
    pbcAdicCompletion Y d ⟶
      (proEtaleSheafDirectImage f CommRingCat.{u + 1}).obj (pbcAdicCompletion X d) :=
  (proEtaleSheafAdjunction f CommRingCat.{u + 1}).unit.app (pbcAdicCompletion Y d) ≫
    (proEtaleSheafDirectImage f CommRingCat.{u + 1}).map (completedCoefficientMap f d)

/-- Sectionwise module direct image with the completed coefficient action.
Source: blueprint order 1276 (blueprint: prop-weil-pbc-direct-image-limits). -/
def completedModuleDirectImage :
    pbcModules X (pbcAdicCompletion X d) ⥤ pbcModules Y (pbcAdicCompletion Y d) :=
  SheafOfModules.pushforward.{u + 1} (F := proEtaleBaseChange f)
    (J := ProEt.topology Y) (K := ProEt.topology X)
    (S := reductionModuleRing Y (pbcAdicCompletion Y d))
    (R := reductionModuleRing X (pbcAdicCompletion X d))
    ⟨Functor.whiskerRight (completedCoefficientDirectImageMap f d).hom
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})⟩

/-- Sectionwise completed direct image is additive.
Source: blueprint order 1276 (blueprint: prop-weil-pbc-direct-image-limits).
Proof: direct image applies the same underlying maps to sections on base-changed objects.
Addition of linear maps is sectionwise, so direct image preserves addition. -/
@[instance]
theorem completedModuleDirectImage_additive : (completedModuleDirectImage f d).Additive := by
  sorry

/-- Levelwise direct image, retaining every tower transition and module map.
Source: blueprint order 1276 (blueprint: prop-weil-pbc-direct-image-limits). -/
def completedTowerModuleDirectImage :
    pbcTowers X (pbcAdicCompletion X d) ⥤ pbcTowers Y (pbcAdicCompletion Y d) :=
  (Functor.whiskeringRight ℕᵒᵖ _ _).obj (completedModuleDirectImage f d)

/-- Levelwise direct image is additive.
Source: blueprint order 1276 (blueprint: prop-weil-pbc-direct-image-limits).
Proof: check equality of natural transformations at each level and apply additivity
of the module direct image there. -/
@[instance]
theorem completedTowerModuleDirectImage_additive :
    (completedTowerModuleDirectImage f d).Additive := by
  sorry

/-- The unbounded total derived completed-coefficient module direct image.
Source: blueprint order 1276 (blueprint: prop-weil-pbc-direct-image-limits). -/
abbrev completedDerivedDirectImage :
    DerivedCategory (pbcModules X (pbcAdicCompletion X d)) ⥤
      DerivedCategory (pbcModules Y (pbcAdicCompletion Y d)) :=
  (completedModuleDirectImage f d).rightDerivedFunctor

/-- Total right derived levelwise direct image, computed on K-injective strict towers.
Source: blueprint order 1276 (blueprint: prop-weil-pbc-direct-image-limits). -/
abbrev completedTowerDirectImage :
    DerivedCategory (pbcTowers X (pbcAdicCompletion X d)) ⥤
      DerivedCategory (pbcTowers Y (pbcAdicCompletion Y d)) :=
  (completedTowerModuleDirectImage f d).rightDerivedFunctor

/-- Derived tower evaluation commutes with total levelwise direct image.
Source: blueprint order 1276 (blueprint: prop-weil-pbc-direct-image-limits).
Proof: evaluation is exact and preserves K-injectives because its left adjoint is
exact. Evaluate a K-injective tower resolution. Both sides are then the same levelwise
direct-image complex. Their universal derived units determine the natural comparison. -/
theorem completedTowerDirectImage_evaluation (n : ℕ) :
    Nonempty (completedTowerDirectImage f d ⋙
      pbcTowerEvaluation Y (pbcAdicCompletion Y d) n ≅
        pbcTowerEvaluation X (pbcAdicCompletion X d) n ⋙ completedDerivedDirectImage f d) := by
  sorry

/-- Sectionwise completed direct image preserves all limits.
Source: Stacks Tag 099N (blueprint: prop-weil-pbc-direct-image-limits).
Proof: module direct image is right adjoint to inverse image followed by scalar
extension along c_f. Right adjoints preserve limits; the comparison is induced by
the direct images of the limit projections. -/
@[instance]
theorem completedModuleDirectImage_preservesLimits :
    PreservesLimits (completedModuleDirectImage f d) := by
  sorry

/-- Restrict the existing limit-preservation instance to the small tower index universe.
Source: Stacks Tag 099N (blueprint: prop-weil-pbc-direct-image-limits). -/
instance completedModuleDirectImage_preservesSmallestLimits :
    PreservesLimitsOfSize.{0, 0} (completedModuleDirectImage f d) :=
  preservesSmallestLimits_of_preservesLimits (completedModuleDirectImage f d)

/-- The projection-induced ordinary limit comparison is natural in strict towers.
Source: Stacks Tag 099N (blueprint: prop-weil-pbc-direct-image-limits).
Proof: compose both maps with every target limit projection. Both composites are
direct image applied to the corresponding component of the same tower morphism.
The target limit projections are jointly monomorphic. -/
theorem completedDirectImageLimit_naturality
    {M N : pbcTowers X (pbcAdicCompletion X d)} (h : M ⟶ N) :
    (completedModuleDirectImage f d).map (lim.map h) ≫
        (preservesLimitIso (completedModuleDirectImage f d) N).hom =
      (preservesLimitIso (completedModuleDirectImage f d) M).hom ≫
        lim.map ((completedTowerModuleDirectImage f d).map h) := by
  sorry

/-- The ordinary limit comparison, fixed by the universal limit projections.
Source: Stacks Tag 099N (blueprint: prop-weil-pbc-direct-image-limits). -/
def completedDirectImageLimitIso :
    (lim : pbcTowers X (pbcAdicCompletion X d) ⥤
      pbcModules X (pbcAdicCompletion X d)) ⋙ completedModuleDirectImage f d ≅
    completedTowerModuleDirectImage f d ⋙
      (lim : pbcTowers Y (pbcAdicCompletion Y d) ⥤
        pbcModules Y (pbcAdicCompletion Y d)) :=
  NatIso.ofComponents (fun M ↦ preservesLimitIso (completedModuleDirectImage f d) M)
    (fun h ↦ completedDirectImageLimit_naturality f d h)

/-- Limit preserves K-injective complexes because constant strict towers are exact.
Source: Stacks Tag 099N (blueprint: prop-weil-pbc-direct-image-limits).
Proof: map a homotopy from an acyclic source across the constant-limit adjunction.
The constant tower of an acyclic complex is acyclic by levelwise exactness, so
K-injectivity annihilates the resulting Hom group. Transport the null-homotopy back. -/
@[instance]
theorem completedTowerLimit_preservesKInjective (T : Scheme.{u}) :
    (lim : pbcTowers T (pbcAdicCompletion T d) ⥤
      pbcModules T (pbcAdicCompletion T d)).PreservesKInjectiveComplexes := by
  sorry

/-- Completed levelwise direct image preserves K-injective strict towers.
Source: Stacks Tag 099N (blueprint: prop-weil-pbc-direct-image-limits).
Proof: the completed coefficient structure map is flat by the constant-to-completed
comparison and its finite reductions. Thus the levelwise left adjoint is exact.
Apply the exact-adjoint K-injective criterion to the strict tower adjunction. -/
@[instance]
theorem completedTowerDirectImage_preservesKInjective :
    (completedTowerModuleDirectImage f d).PreservesKInjectiveComplexes := by
  sorry

/-- The canonical Rf_* Rlim ≅ Rlim Rf_*^Tow comparison obtained by deriving the
projection-induced ordinary limit comparison, with universal derived units retained.
Source: Stacks Tag 099N (blueprint: prop-weil-pbc-direct-image-limits). -/
def completedDirectImageRlimIso :
    completedTowerRlim d X ⋙ completedDerivedDirectImage f d ≅
      completedTowerDirectImage f d ⋙ completedTowerRlim d Y :=
  (Functor.rightDerivedFunctorCompIso
    (lim : pbcTowers X (pbcAdicCompletion X d) ⥤
      pbcModules X (pbcAdicCompletion X d)) (completedModuleDirectImage f d)).symm ≪≫
  Functor.rightDerivedFunctorNatIso (completedDirectImageLimitIso f d) ≪≫
  Functor.rightDerivedFunctorCompIso (completedTowerModuleDirectImage f d)
    (lim : pbcTowers Y (pbcAdicCompletion Y d) ⥤
      pbcModules Y (pbcAdicCompletion Y d))

/-- Completed direct image preserves intrinsic derived completeness.
Source: Stacks Tag 099N, clauses (1),(3),(4)
(blueprint: prop-weil-pbc-direct-image-limits).
Proof: the constant/completed comparison identifies intrinsic completion with the
finite-reduction derived limit. Perfect projection formula identifies the reductions
of Rf_*K with Rf_* of the reductions. Apply completedDirectImageRlimIso to the
input completion unit; the output unit is the stated composite and is invertible. -/
theorem completedDirectImage_complete (d : AdicCoefficientDatum A)
    (r : ℕ) (a : Fin r → A) (ha : Ideal.span (Set.range a) = d.ideal)
    (K : DerivedCategory (pbcModules X (pbcAdicCompletion X d)))
    (C : CochainComplex (pbcModules X (pbcAdicCompletion X d)) ℤ)
    (e : DerivedCategory.Q.obj C ≅ K)
    (_hK : IsDerivedCompleteIntrinsic X d r a ha K C e)
    (P : CochainComplex (pbcModules Y (pbcAdicCompletion Y d)) ℤ)
    (eP : DerivedCategory.Q.obj P ≅ (completedDerivedDirectImage f d).obj K) :
    IsDerivedCompleteIntrinsic Y d r a ha
      ((completedDerivedDirectImage f d).obj K) P eP := by
  sorry

/-- Module direct image with the actual finite quotient coefficient ring.
Source: blueprint order 1276 (blueprint: prop-weil-pbc-direct-image-limits). -/
abbrev completedFiniteModuleDirectImage (n : ℕ) :=
  proEtaleRingModuleDirectImage f ((pbcAdicRings Y d).obj (op n))
    ((pbcAdicRings X d).obj (op n))
    (asIso (completedFiniteCoefficientMap f d n))

/-- The finite quotient direct image obtained by total right derivation.
Source: blueprint order 1276 (blueprint: prop-weil-pbc-direct-image-limits). -/
abbrev completedFiniteDerivedDirectImage (n : ℕ) :=
  (completedFiniteModuleDirectImage f d n).rightDerivedFunctor

/-- Restriction commutes with ordinary direct image by identity on underlying sections.
Source: blueprint order 1276 (blueprint: prop-weil-pbc-direct-image-limits).
Proof: the square of completed structure maps and finite projections commutes by the
component construction of c_f. The two module actions therefore agree. Identity on
sections is a natural linear isomorphism and sectionwise faithfulness proves uniqueness. -/
theorem completedRestrictionDirectImageIso_exists (n : ℕ) :
    ∃! e : pbcRestrict (pbcAdicProjection X d n) ⋙ completedModuleDirectImage f d ≅
        completedFiniteModuleDirectImage f d n ⋙ pbcRestrict (pbcAdicProjection Y d n),
      ∀ (M : pbcModules X ((pbcAdicRings X d).obj (op n))) (U : Y.ProEtᵒᵖ)
        (x : ((pbcRestrict (pbcAdicProjection X d n) ⋙
          completedModuleDirectImage f d).obj M).val.obj U),
        (e.hom.app M).val.app U x = x := by
  sorry

/-- The uniquely section-normalized restriction/direct-image comparison.
Source: blueprint order 1276 (blueprint: prop-weil-pbc-direct-image-limits). -/
def completedRestrictionDirectImageIso (n : ℕ) :
    pbcRestrict (pbcAdicProjection X d n) ⋙ completedModuleDirectImage f d ≅
      completedFiniteModuleDirectImage f d n ⋙ pbcRestrict (pbcAdicProjection Y d n) :=
  (completedRestrictionDirectImageIso_exists f d n).exists.choose

/-- The total right-derived comparison on a completed-coefficient cochain complex.
Source: blueprint order 1276 (blueprint: prop-weil-pbc-direct-image-limits). -/
def completedDirectImageComplexUnit
    (C : CochainComplex (pbcModules X (pbcAdicCompletion X d)) ℤ) :
    DerivedCategory.Q.obj
        (((completedModuleDirectImage f d).mapHomologicalComplex (.up ℤ)).obj C) ⟶
      (completedDerivedDirectImage f d).obj (DerivedCategory.Q.obj C) :=
  (DerivedCategory.quotientCompQhIso _).inv.app _ ≫
    DerivedCategory.Qh.map
      (((completedModuleDirectImage f d).mapHomotopyCategoryFactors (.up ℤ)).inv.app C) ≫
    (completedModuleDirectImage f d).rightDerivedFunctorUnit.app
      ((HomotopyCategory.quotient _ _).obj C) ≫
    (completedDerivedDirectImage f d).map ((DerivedCategory.quotientCompQhIso _).hom.app C)

/-- The total right-derived comparison on a finite-coefficient cochain complex.
Source: blueprint order 1276 (blueprint: prop-weil-pbc-direct-image-limits). -/
def completedFiniteDirectImageComplexUnit (n : ℕ)
    (C : CochainComplex (pbcModules X ((pbcAdicRings X d).obj (op n))) ℤ) :
    DerivedCategory.Q.obj
        (((completedFiniteModuleDirectImage f d n).mapHomologicalComplex (.up ℤ)).obj C) ⟶
      (completedFiniteDerivedDirectImage f d n).obj (DerivedCategory.Q.obj C) :=
  (DerivedCategory.quotientCompQhIso _).inv.app _ ≫
    DerivedCategory.Qh.map
      (((completedFiniteModuleDirectImage f d n).mapHomotopyCategoryFactors (.up ℤ)).inv.app C) ≫
    (completedFiniteModuleDirectImage f d n).rightDerivedFunctorUnit.app
      ((HomotopyCategory.quotient _ _).obj C) ≫
    (completedFiniteDerivedDirectImage f d n).map
      ((DerivedCategory.quotientCompQhIso _).hom.app C)

/-- The derived coefficient comparison is fixed by the ordinary identity comparison
and the universal right-derived units. This normalization prevents an arbitrary
natural isomorphism from being substituted in the projection-formula construction.
Source: blueprint order 1276 (blueprint: prop-weil-pbc-direct-image-limits).
Proof: finite module inverse image is exact, and direct images of injective finite
module sheaves are acyclic after scalar restriction. Derive the sectionwise comparison
using such resolutions. The universal right-derived units give the displayed equation
on complexes, and the universal derived property gives uniqueness and invertibility. -/
theorem completedDerivedRestrictionDirectImageIso_exists (n : ℕ) :
    ∃! e : pbcDerivedRestrict (pbcAdicProjection X d n) ⋙ completedDerivedDirectImage f d ≅
        completedFiniteDerivedDirectImage f d n ⋙
          pbcDerivedRestrict (pbcAdicProjection Y d n),
      ∀ C : CochainComplex (pbcModules X ((pbcAdicRings X d).obj (op n))) ℤ,
        completedDirectImageComplexUnit f d
            (((pbcRestrict (pbcAdicProjection X d n)).mapHomologicalComplex (.up ℤ)).obj C) ≫
          (completedDerivedDirectImage f d).map
            ((pbcRestrict (pbcAdicProjection X d n)).mapDerivedCategoryFactors.inv.app C) ≫
          e.hom.app (DerivedCategory.Q.obj C) =
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex
          (completedRestrictionDirectImageIso f d n).hom (.up ℤ)).app C) ≫
          (pbcRestrict (pbcAdicProjection Y d n)).mapDerivedCategoryFactors.inv.app
            (((completedFiniteModuleDirectImage f d n).mapHomologicalComplex (.up ℤ)).obj C) ≫
          (pbcDerivedRestrict (pbcAdicProjection Y d n)).map
            (completedFiniteDirectImageComplexUnit f d n C) := by
  sorry

/-- The canonical derived restriction/direct-image comparison.
Source: blueprint order 1276 (blueprint: prop-weil-pbc-direct-image-limits). -/
def completedDerivedRestrictionDirectImageIso (n : ℕ) :
    pbcDerivedRestrict (pbcAdicProjection X d n) ⋙ completedDerivedDirectImage f d ≅
      completedFiniteDerivedDirectImage f d n ⋙
        pbcDerivedRestrict (pbcAdicProjection Y d n) :=
  (completedDerivedRestrictionDirectImageIso_exists f d n).exists.choose

/-- The finite projection-formula arrow is the scalar-adjunction mate of direct image
of the reduction unit, followed by the canonical restriction/direct-image comparison.
Source: blueprint order 1276 (blueprint: prop-weil-pbc-direct-image-limits). -/
def completedDirectImageProjectionFormula (n : ℕ)
    (K : DerivedCategory (pbcModules X (pbcAdicCompletion X d))) :
    (pbcDerivedExtend (pbcAdicProjection Y d n)).obj
        ((completedDerivedDirectImage f d).obj K) ⟶
      (completedFiniteDerivedDirectImage f d n).obj
        ((pbcDerivedExtend (pbcAdicProjection X d n)).obj K) :=
  ((pbcDerivedScalarAdjunction (pbcAdicProjection Y d n)).homEquiv _ _).symm
    ((completedDerivedDirectImage f d).map
      ((pbcDerivedScalarAdjunction (pbcAdicProjection X d n)).unit.app K) ≫
      (completedDerivedRestrictionDirectImageIso f d n).hom.app
        ((pbcDerivedExtend (pbcAdicProjection X d n)).obj K))

/-- Perfectness of each quotient makes this specified projection-formula arrow an
isomorphism, functorial in the input.
Source: blueprint order 1276 (blueprint: prop-weil-pbc-direct-image-limits).
Proof: a finite projective resolution of A/I^(n+1) reduces the assertion to the free
rank-one projection formula. It is the identity there. Finite sums, shifts, cones and
retracts preserve invertibility. The mate construction is natural in K throughout. -/
theorem completedDirectImageProjectionFormula_properties (d : AdicCoefficientDatum A) :
    (∀ (n : ℕ) (K : DerivedCategory (pbcModules X (pbcAdicCompletion X d))),
      IsIso (completedDirectImageProjectionFormula f d n K)) ∧
    ∀ (n : ℕ) (K L : DerivedCategory (pbcModules X (pbcAdicCompletion X d)))
      (h : K ⟶ L),
      (pbcDerivedExtend (pbcAdicProjection Y d n)).map
          ((completedDerivedDirectImage f d).map h) ≫
        completedDirectImageProjectionFormula f d n L =
      completedDirectImageProjectionFormula f d n K ≫
        (completedFiniteDerivedDirectImage f d n).map
          ((pbcDerivedExtend (pbcAdicProjection X d n)).map h) := by
  sorry

/-- Exact tower evaluation preserves K-injectives by its exact left adjoint.
Source: blueprint order 1276, proof step 2 (blueprint: prop-weil-pbc-direct-image-limits).
Proof: the left adjoint puts V at levels at most n and zero above n, with identity
transitions. It is exact levelwise. Apply the exact-adjoint K-injective criterion,
or tower_evaluation_isKInjective, to every complex of strict towers. -/
@[instance]
theorem completedEvaluation_preservesKInjective (T : Scheme.{u})
    (R : Sheaf (ProEt.topology T) CommRingCat.{u + 1}) (n : ℕ) :
    ((CategoryTheory.evaluation ℕᵒᵖ (pbcModules T R)).obj
      (op n)).PreservesKInjectiveComplexes := by
  sorry

/-- The ordinary evaluation/direct-image comparison is identity at every object and map.
Source: blueprint order 1276, proof step 2 (blueprint: prop-weil-pbc-direct-image-limits). -/
def completedDirectImageEvaluationIso (n : ℕ) :
    completedTowerModuleDirectImage f d ⋙
        (CategoryTheory.evaluation ℕᵒᵖ (pbcModules Y (pbcAdicCompletion Y d))).obj (op n) ≅
      (CategoryTheory.evaluation ℕᵒᵖ (pbcModules X (pbcAdicCompletion X d))).obj (op n) ⋙
        completedModuleDirectImage f d :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun _ ↦ rfl)

/-- Canonical evaluation comparison, retaining the universal right-derived units.
Source: blueprint order 1276, proof step 2 (blueprint: prop-weil-pbc-direct-image-limits). -/
def completedDerivedDirectImageEvaluationIso (n : ℕ) :
    completedTowerDirectImage f d ⋙ pbcTowerEvaluation Y (pbcAdicCompletion Y d) n ≅
      pbcTowerEvaluation X (pbcAdicCompletion X d) n ⋙ completedDerivedDirectImage f d :=
  (Functor.isoWhiskerLeft (completedTowerDirectImage f d)
    ((CategoryTheory.evaluation ℕᵒᵖ (pbcModules Y (pbcAdicCompletion Y d))).obj
      (op n)).rightDerivedFunctorIsoMapDerivedCategory).symm ≪≫
    (Functor.rightDerivedFunctorCompIso (completedTowerModuleDirectImage f d)
      ((CategoryTheory.evaluation ℕᵒᵖ (pbcModules Y (pbcAdicCompletion Y d))).obj
        (op n))).symm ≪≫
    Functor.rightDerivedFunctorNatIso (completedDirectImageEvaluationIso f d n) ≪≫
    Functor.rightDerivedFunctorCompIso
      ((CategoryTheory.evaluation ℕᵒᵖ (pbcModules X (pbcAdicCompletion X d))).obj (op n))
      (completedModuleDirectImage f d) ≪≫
    Functor.isoWhiskerRight
      ((CategoryTheory.evaluation ℕᵒᵖ (pbcModules X (pbcAdicCompletion X d))).obj
        (op n)).rightDerivedFunctorIsoMapDerivedCategory (completedDerivedDirectImage f d)

/-- The ordinary limit projection as a natural transformation to evaluation.
Source: blueprint order 1276, proof steps 3--5
(blueprint: prop-weil-pbc-direct-image-limits). -/
def completedLimitEvaluation (T : Scheme.{u}) (n : ℕ) :
    (lim : pbcTowers T (pbcAdicCompletion T d) ⥤ pbcModules T (pbcAdicCompletion T d)) ⟶
      (CategoryTheory.evaluation ℕᵒᵖ (pbcModules T (pbcAdicCompletion T d))).obj (op n) :=
  { app M := limit.π M (op n)
    naturality _ _ h := limMap_π h (op n) }

/-- The derived limit projection, obtained from the ordinary projection and derived units.
Source: blueprint order 1276, proof steps 3--5
(blueprint: prop-weil-pbc-direct-image-limits). -/
def completedRlimEvaluation (T : Scheme.{u}) (n : ℕ) :
    completedTowerRlim d T ⟶ pbcTowerEvaluation T (pbcAdicCompletion T d) n :=
  Functor.rightDerivedFunctorNatTrans (completedLimitEvaluation d T n) ≫
    ((CategoryTheory.evaluation ℕᵒᵖ (pbcModules T (pbcAdicCompletion T d))).obj
      (op n)).rightDerivedFunctorIsoMapDerivedCategory.hom

/-- The canonical map from the derived limit to the product of its evaluations.
Source: blueprint order 1276, proof steps 3--5
(blueprint: prop-weil-pbc-direct-image-limits). -/
def completedRlimProductMap (T : Scheme.{u})
    (M : DerivedCategory (pbcTowers T (pbcAdicCompletion T d)))
    [HasProduct (completedTowerDerivedSequence T d M)] :
    (completedTowerRlim d T).obj M ⟶ ∏ᶜ (completedTowerDerivedSequence T d M) :=
  Pi.lift (fun n ↦ (completedRlimEvaluation d T n).app M)

/-- The product comparison has exactly the direct images of the source projections,
transported by the canonical evaluation comparisons.
Source: blueprint order 1276, proof step 3 (blueprint: prop-weil-pbc-direct-image-limits). -/
def completedDirectImageProductMap
    (M : DerivedCategory (pbcTowers X (pbcAdicCompletion X d)))
    [HasProduct (completedTowerDerivedSequence X d M)]
    [HasProduct (completedTowerDerivedSequence Y d ((completedTowerDirectImage f d).obj M))] :
    (completedDerivedDirectImage f d).obj (∏ᶜ (completedTowerDerivedSequence X d M)) ⟶
      ∏ᶜ (completedTowerDerivedSequence Y d ((completedTowerDirectImage f d).obj M)) :=
  Pi.lift (fun n ↦ (completedDerivedDirectImage f d).map
    (Pi.π (completedTowerDerivedSequence X d M) n) ≫
      (completedDerivedDirectImageEvaluationIso f d n).inv.app M)

/-- The fixed inverse-limit comparison is induced by the canonical product comparison
and commutes with both canonical Roos triangles, including their connecting arrows.
Source: blueprint order 1276, proof steps 3--5; Stacks Tag 099N
(blueprint: prop-weil-pbc-direct-image-limits).
Proof: resolve M by a K-injective strict tower J. Exact evaluation makes each J_n
K-injective. Products and the mapping fiber of 1-shift are K-injective. The ordinary
right-adjoint product comparison is fixed by its projections; these projections show
that it commutes with shift and hence 1-shift. Direct image commutes with the finite
sum and matrix defining the mapping fiber. The resulting isomorphism of fiber complexes
is the derived ordinary-limit comparison already defined above. Localizing its cone
triangle gives both displayed squares, with the derived functor's shift comparison. -/
theorem completedDirectImageRlim_roos
    (M : DerivedCategory (pbcTowers X (pbcAdicCompletion X d))) :
    ∃ (_ : HasProduct (completedTowerDerivedSequence X d M))
      (_ : HasProduct (completedTowerDerivedSequence Y d
        ((completedTowerDirectImage f d).obj M))),
      IsIso (completedDirectImageProductMap f d M) ∧
      (completedDerivedDirectImage f d).map
          (towerTransitionEndomorphism (completedTowerDerivedStep X d M)) ≫
        completedDirectImageProductMap f d M =
      completedDirectImageProductMap f d M ≫ towerTransitionEndomorphism
        (completedTowerDerivedStep Y d ((completedTowerDirectImage f d).obj M)) ∧
      ∃ (δX : ∏ᶜ (completedTowerDerivedSequence X d M) ⟶
          ((completedTowerRlim d X).obj M)⟦(1 : ℤ)⟧)
        (δY : ∏ᶜ (completedTowerDerivedSequence Y d
          ((completedTowerDirectImage f d).obj M)) ⟶
            ((completedTowerRlim d Y).obj ((completedTowerDirectImage f d).obj M))⟦(1 : ℤ)⟧),
        IsDerivedLimitTriangle (completedTowerDerivedStep X d M)
          ((completedTowerRlim d X).obj M) (completedRlimProductMap d X M) δX ∧
        IsDerivedLimitTriangle
          (completedTowerDerivedStep Y d ((completedTowerDirectImage f d).obj M))
          ((completedTowerRlim d Y).obj ((completedTowerDirectImage f d).obj M))
          (completedRlimProductMap d Y ((completedTowerDirectImage f d).obj M)) δY ∧
        (completedDirectImageRlimIso f d).hom.app M ≫
            completedRlimProductMap d Y ((completedTowerDirectImage f d).obj M) =
          (completedDerivedDirectImage f d).map (completedRlimProductMap d X M) ≫
            completedDirectImageProductMap f d M ∧
        (completedDerivedDirectImage f d).map δX ≫
            ((completedDerivedDirectImage f d).commShiftIso (1 : ℤ)).hom.app
              ((completedTowerRlim d X).obj M) ≫
            (shiftFunctor _ (1 : ℤ)).map ((completedDirectImageRlimIso f d).hom.app M) =
          completedDirectImageProductMap f d M ≫ δY := by
  sorry

/-- The actual completed-linear transition between two reductions of K.
Source: blueprint order 1276, proof step 6 (blueprint: prop-weil-pbc-direct-image-limits). -/
def completedReductionStep (T : Scheme.{u})
    (K : DerivedCategory (pbcModules T (pbcAdicCompletion T d)))
    (b a : ℕ) (hab : a ≤ b) :
    (pbcDerivedRestrict (pbcAdicProjection T d b)).obj
        ((pbcDerivedExtend (pbcAdicProjection T d b)).obj K) ⟶
      (pbcDerivedRestrict (pbcAdicProjection T d a)).obj
        ((pbcDerivedExtend (pbcAdicProjection T d a)).obj K) :=
  (pbcDerivedRestrict (pbcAdicProjection T d b)).map
      (pbcReductionTransition (pbcAdicProjection T d b) (pbcAdicQuotient T d b a hab)
        (pbcAdicProjection T d a) (pbcAdicProjection_comp T d b a hab) K) ≫
    (pbcDerivedRestrictComp (pbcAdicProjection T d b) (pbcAdicQuotient T d b a hab)
      (pbcAdicProjection T d a) (pbcAdicProjection_comp T d b a hab)).hom.app _

/-- The finite projection formula after restriction to the completed coefficient rings.
Source: blueprint order 1276, proof step 6 (blueprint: prop-weil-pbc-direct-image-limits). -/
def completedRestrictedProjectionFormula (n : ℕ)
    (K : DerivedCategory (pbcModules X (pbcAdicCompletion X d))) :
    (pbcDerivedRestrict (pbcAdicProjection Y d n)).obj
        ((pbcDerivedExtend (pbcAdicProjection Y d n)).obj
          ((completedDerivedDirectImage f d).obj K)) ⟶
      (completedDerivedDirectImage f d).obj
        ((pbcDerivedRestrict (pbcAdicProjection X d n)).obj
          ((pbcDerivedExtend (pbcAdicProjection X d n)).obj K)) :=
  (pbcDerivedRestrict (pbcAdicProjection Y d n)).map
      (completedDirectImageProjectionFormula f d n K) ≫
    (completedDerivedRestrictionDirectImageIso f d n).inv.app
      ((pbcDerivedExtend (pbcAdicProjection X d n)).obj K)

/-- Projection formula respects every quotient transition and the reductions from K.
Source: blueprint order 1276, proof step 6 (blueprint: prop-weil-pbc-direct-image-limits).
Proof: the projection formula is the scalar-adjunction mate of direct image of the
reduction unit. Quotient balancing takes 1 tensor x to 1 tensor x. Thus both quotient
paths have the same adjunct, namely direct image of the same reduction unit followed
by the lower quotient. The normalized restriction/direct-image comparisons are identity
on sections and retain these equalities after deriving. Apply the Hom bijection for
scalar extension; it gives the quotient square and the equation for the unit from K. -/
theorem completedDirectImageProjectionFormula_quotients
    (K : DerivedCategory (pbcModules X (pbcAdicCompletion X d))) :
    (∀ (b a : ℕ) (hab : a ≤ b),
      completedReductionStep d Y ((completedDerivedDirectImage f d).obj K) b a hab ≫
          completedRestrictedProjectionFormula f d a K =
        completedRestrictedProjectionFormula f d b K ≫
          (completedDerivedDirectImage f d).map (completedReductionStep d X K b a hab)) ∧
    ∀ n : ℕ,
      (pbcDerivedScalarAdjunction (pbcAdicProjection Y d n)).unit.app
          ((completedDerivedDirectImage f d).obj K) ≫
        completedRestrictedProjectionFormula f d n K =
      (completedDerivedDirectImage f d).map
        ((pbcDerivedScalarAdjunction (pbcAdicProjection X d n)).unit.app K) := by
  sorry

/-- The canonical quotient-tower completion map, induced by the strict reduction unit.
Source: blueprint order 1276, proof step 6 (blueprint: prop-weil-pbc-direct-image-limits). -/
def completedQuotientCompletionUnit (T : Scheme.{u})
    (K : DerivedCategory (pbcModules T (pbcAdicCompletion T d))) :
    K ⟶ (completedTowerRlim d T).obj ((completedReductionTower T d).obj K) :=
  (completedConstantRlimUnit d T).app K ≫
    (completedTowerRlim d T).map ((completedReductionTowerUnit d T).app K)

/-- The output completion unit is precisely direct image of the input completion unit
followed by the fixed inverse-limit comparison and the finite projection-formula comparison.
The comparisons with intrinsic Koszul completion retain their unit normalization.
Source: blueprint order 1276, proof step 6; Stacks Tag 099N
(blueprint: prop-weil-pbc-direct-image-limits).
Proof: Koszul reconstruction identifies intrinsic completion with the quotient-tower
limit and identifies their units. Perfect projection formula at each quotient is an
isomorphism; the preceding quotient and unit equations make these an isomorphism of
the reduction towers with their maps from Rf_*K. Apply derived inverse limit and its
canonical direct-image comparison. The resulting composite is the output completion
map. The input completion map is invertible by the hypothesis, hence so is its direct
image and the displayed composite; this also proves output completeness. On complete
inputs the composite out of Rf_*K is invertible, so its unit equation determines the
last comparison uniquely. -/
theorem completedDirectImage_completionUnit (d : AdicCoefficientDatum A)
    (r : ℕ) (a : Fin r → A) (ha : Ideal.span (Set.range a) = d.ideal)
    (K : DerivedCategory (pbcModules X (pbcAdicCompletion X d)))
    (C : CochainComplex (pbcModules X (pbcAdicCompletion X d)) ℤ)
    (e : DerivedCategory.Q.obj C ≅ K)
    (_hK : IsDerivedCompleteIntrinsic X d r a ha K C e)
    (P : CochainComplex (pbcModules Y (pbcAdicCompletion Y d)) ℤ)
    (eP : DerivedCategory.Q.obj P ≅ (completedDerivedDirectImage f d).obj K) :
    ∃ (κX : intrinsicCompletion X d r a ha K C e ≅
        (completedTowerRlim d X).obj ((completedReductionTower X d).obj K))
      (κY : intrinsicCompletion Y d r a ha ((completedDerivedDirectImage f d).obj K)
        P eP ≅ (completedTowerRlim d Y).obj ((completedReductionTower Y d).obj
          ((completedDerivedDirectImage f d).obj K))),
      intrinsicCompletionUnit X d r a ha K C e ≫ κX.hom =
        completedQuotientCompletionUnit d X K ∧
      intrinsicCompletionUnit Y d r a ha ((completedDerivedDirectImage f d).obj K)
          P eP ≫ κY.hom =
        completedQuotientCompletionUnit d Y ((completedDerivedDirectImage f d).obj K) ∧
      ∃! β : (completedTowerRlim d Y).obj ((completedTowerDirectImage f d).obj
          ((completedReductionTower X d).obj K)) ≅
        (completedTowerRlim d Y).obj ((completedReductionTower Y d).obj
          ((completedDerivedDirectImage f d).obj K)),
        (completedDerivedDirectImage f d).map
            (completedQuotientCompletionUnit d X K) ≫
          (completedDirectImageRlimIso f d).hom.app
            ((completedReductionTower X d).obj K) ≫ β.hom =
        completedQuotientCompletionUnit d Y
          ((completedDerivedDirectImage f d).obj K) := by
  sorry

end AlgebraicGeometry.Scheme
