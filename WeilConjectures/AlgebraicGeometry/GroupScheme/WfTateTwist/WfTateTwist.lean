/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Supporting.PbcWeilCategory
public import WeilConjectures.AlgebraicGeometry.Pbc.PbcCoefficientTwists
public import WeilConjectures.SmoothPurity.FrobeniusCoefficientTwists.FrobeniusCoefficientTwistsCanonical
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.AlgebraicGeometry.Weil.WeilTensorProduct
public import WeilConjectures.AlgebraicGeometry.Pbc.PbcUniformCompleteTriangulated
public import WeilConjectures.CategoryTheory.ScalarLocalization.ScalarLocalizationTriangulated
public import WeilConjectures.AlgebraicGeometry.Localized.LocalizedTStructure
public import WeilConjectures.AlgebraicGeometry.Pbc.PbcRationalCategory
public import WeilConjectures.Algebra.Homology.CanonicalTensorPullbackOfUniverses.RingedTopoiCanonicalTensorPullbackOfUniverses
public import WeilConjectures.AlgebraicGeometry.Weil.WeilCompletedTensorReflector
public import WeilConjectures.AlgebraicGeometry.Picard.SiteDerivedTensorDescentIndependentCoefficients
public import WeilConjectures.AlgebraicGeometry.Picard.KFlatResolutionIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatFixedTensor.KFlatFixedTensorTriangulatedSupplement
public import WeilConjectures.ProperBaseChange.RingedKoszulCompletionReflector
public import WeilConjectures.ProperBaseChange.RingedStrictTowerHomotopyLimitIndependentCoefficients
public import Mathlib.CategoryTheory.Triangulated.Subcategory
public import WeilConjectures.Mathlib.CategoryTheory.Triangulated.Functor
public import WeilConjectures.CategoryTheory.Ringed.RingedInternalHomExactRestrictionSupplement
public import Mathlib.CategoryTheory.Triangulated.Adjunction
public import WeilConjectures.Algebra.Homology.DerivedInternalHomOfUniverses
public import WeilConjectures.AlgebraicGeometry.CoefficientHomRepresentativeEvaluation
public import WeilConjectures.CategoryTheory.Ringed.RingedInternalHomDerivedComplete
public import WeilConjectures.CategoryTheory.Ringed.RingedPresentationTransport
public import WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMapOfUniverses
import WeilConjectures.AlgebraicGeometry.Integral.IntegralStratifiedPerfectCharacterization
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.CategoryTheory.Limits.HasLimits
import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
import WeilConjectures.AlgebraicGeometry.Pur.PurTwistSheafLocallyFree
import WeilConjectures.SmoothPurity.Coefficient.CoefficientTwistsDetailed
import WeilConjectures.AlgebraicGeometry.CompletedIntegralConstantMapOfUniverses
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleRootsOfUnityInverseImageSupplement
import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantRingMap
import WeilConjectures.SmoothPurity.CompletedCoefficientNormalization.CompletedCoefficientTensorNormalization
import WeilConjectures.AlgebraicGeometry.WeilSheaf.ProfiniteCoefficientInverseImageSupplement
import WeilConjectures.AlgebraicGeometry.ProEtale.Finite.ProEtaleFiniteTowerLimit
import WeilConjectures.AlgebraicGeometry.Pur.PurRootTowerPreservation
import WeilConjectures.AlgebraicGeometry.Pur.PurTwistSheavesSupplement
import WeilConjectures.AlgebraicGeometry.SmoothPurity.RootsOfUnityInverseImageIso
import WeilConjectures.AlgebraicGeometry.Cartesian.CartesianCoefficientTwistsSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtale.Ring.ProEtaleRingSheafChangeAdjunctionSupplement
public import WeilConjectures.CategoryTheory.ScalarLocalization.ScalarLocalizationComponentIso
public import WeilConjectures.ProperBaseChange.IntegralPullbackIdentificationExists

/-! # Tate twists in the raw rational Weil category

Source: main-20261015, sec-algebraic-groups-lie-algebras/sk-d-ab-cyclotomic,
Definition of Tate twists (blueprint: def-wf-tate-twist).

The signed lines and their root-normalized transport are the existing constructions.
This module transports them through the canonical completed coefficient isomorphism
and restricts their tensor action to the actual PBC integral and rational categories.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme

namespace WeilConjectures.WfTateTwist

variable (D : FiniteFieldDatum.{u}) (c : D.CoefficientDatum)
  (X₀ : Over (Spec (CommRingCat.of D.k₀)))
  [IsSeparated X₀.hom] [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]

variable (E : Padic.FiniteCoefficientFields c.l c.Qbar)

private theorem localizedCommutingComparison
    (R : Type*) [CommRing R] (C : Type*) [Category C] [Preadditive C] [Linear R C]
    (p : R) (T P : C ⥤ C) [T.Additive] [P.Additive] [T.Linear R] [P.Linear R]
    (a : T ⋙ P ≅ P ⋙ T) :
    ∃! e : ScalarLocalization.transport R p T ⋙ ScalarLocalization.map R C p P ≅
        ScalarLocalization.map R C p P ⋙ ScalarLocalization.transport R p T,
      ∀ K : ScalarLocalization R C p, HEq (e.hom.app K)
        ((ScalarLocalization.localization R C p).map (a.hom.app K.obj)) := by
  apply ScalarLocalization.existsUnique_iso_of_component_formulas p p id
    (T ⋙ P) (P ⋙ T) a _ _ (fun _ ↦ rfl) (fun _ ↦ rfl)
  · intro K K' f r
    apply heq_of_eq
    change ScalarLocalization.mapHom R C p P _ _
      (ScalarLocalization.transportHom R p T _ _ (r ⊗ₜ[R] f)) = r ⊗ₜ[R] P.map (T.map f)
    simp only [ScalarLocalization.mapHom, ScalarLocalization.transportHom,
      LinearMap.baseChange_tmul, CategoryTheory.Functor.mapLinearMap_apply]
    rfl
  · intro K K' f r
    apply heq_of_eq
    change ScalarLocalization.transportHom R p T _ _
      (ScalarLocalization.mapHom R C p P _ _ (r ⊗ₜ[R] f)) = r ⊗ₜ[R] T.map (P.map f)
    simp only [ScalarLocalization.mapHom, ScalarLocalization.transportHom,
      LinearMap.baseChange_tmul, CategoryTheory.Functor.mapLinearMap_apply]
    rfl

/-- The existing completed coefficient module category, with its fixed small-site size.
Source: definition, completed coefficients (blueprint: def-wf-tate-twist). -/
abbrev Modules := pbcModules (D.geometricFiber X₀).left
  (pbcAdicCompletion (D.geometricFiber X₀).left (pbcStageDatum.{u} c.l c.Qbar E))

/-- The published signed line, in the PBC coefficient coordinates.
Source: definition, E(0), E(m), and E(-m) (blueprint: def-wf-tate-twist). -/
abbrev line (m : ℤ) : Modules D c X₀ E :=
  pbcTateLineSheaf c.l (D.geometricFiber X₀).left (pbcFiniteField.{u} c.l c.Qbar E) m

/-- Exact transport on completed module sheaves along geometric Frobenius.
Source: definition, P_E (blueprint: def-wf-tate-twist). -/
abbrev pull := pbcIsoModulePullback (D.geometricFrobenius X₀).hom
  (pbcStageDatum.{u} c.l c.Qbar E)

/-- Insertion into the canonical module pullback, through its normalized adjunction unit.
Source: definition, inverse-image tensor comparison (blueprint: def-wf-tate-twist). -/
def sectionMap (M : Modules D c X₀ E) (V : (D.geometricFiber X₀).left.ProEt)
    (x : M.val.obj (op V)) :=
  ((proEtaleRingModuleAdjunction (D.geometricFrobenius X₀).hom
    (pbcAdicCompletion _ (pbcStageDatum.{u} c.l c.Qbar E))
    (pbcAdicCompletion _ (pbcStageDatum.{u} c.l c.Qbar E))
    (asIso (AlgebraicGeometry.Scheme.completedCoefficientMap (D.geometricFrobenius X₀).hom
      (pbcStageDatum.{u} c.l c.Qbar E)))).unit.app M).val.app (op V) x

/-- Transport the existing root-normalized signed-line map through the coefficient
isomorphism, retaining its value on every adjunction-unit section. The underlying
additive sheaves of coefficient restriction are unchanged, hence the HEq formula.
Source: definition, root pullbacks, signed powers and duals (blueprint: def-wf-tate-twist).
Proof: the coefficient isomorphism is fixed by every finite projection. Its square
with Frobenius commutes since both maps induce the same constant quotient maps.
Restrict the published signedLineMaps through that square. The positive maps are
fixed on ordered root tensors, at zero on the coefficient unit, and the negative maps
by evaluation with the inverse positive map. This yields the displayed formula.
The module adjunction and generation by its unit sections prove uniqueness. -/
theorem lineMap_exists (m : ℤ) :
    ∃! t : (pull D c X₀ E).obj (line D c X₀ E m) ≅ line D c X₀ E m,
      ∀ (V : (D.geometricFiber X₀).left.ProEt)
        (x : (line D c X₀ E m).val.obj (op V)),
        HEq (t.hom.val.app (op ((proEtaleBaseChange
          (D.geometricFrobenius X₀).hom).obj V))
            (sectionMap D c X₀ E (line D c X₀ E m) V x))
          ((FrobeniusCoefficientTwists.signedLineMaps c.l
            (pbcFiniteField.{u} c.l c.Qbar E) (D.geometricFrobenius X₀).hom m).hom.val.app
              (op ((proEtaleBaseChange (D.geometricFrobenius X₀).hom).obj V))
            (FrobeniusCoefficientTwists.moduleSection c.l
              (pbcFiniteField.{u} c.l c.Qbar E) (D.geometricFrobenius X₀).hom
              (FrobeniusCoefficientTwists.line c.l (pbcFiniteField.{u} c.l c.Qbar E)
                (D.geometricFiber X₀).left m) V x)) := by
  let X := (D.geometricFiber X₀).left
  let F := pbcFiniteField.{u} c.l c.Qbar E
  let f := (D.geometricFrobenius X₀).hom
  let A := pbcAdicCompletion X (pbcIntegralDatum c.l F)
  let B := (PurCompactSupport.completed c.l F).ring X
  let a := (purCoefficientIso c.l F X).hom
  let r := asIso (AlgebraicGeometry.Scheme.completedCoefficientMap f (pbcIntegralDatum c.l F))
  let t := (PurCompactSupport.completed c.l F).pull f
  have hc : sfCompletedCoefficientMap c.l F f = IntegralAmbient.coefficientMap c.l F f := by
    apply (IntegralAmbient.coefficientMap_existsUnique c.l F f).unique
    · intro n
      exact (sfCompletedCoefficientMap_existsUnique c.l F f).exists.choose_spec n
    · exact (IntegralAmbient.coefficientMap_existsUnique c.l F f).exists.choose_spec
  have hs : a ≫ sfCompletedCoefficientMap c.l F f =
      AlgebraicGeometry.Scheme.completedCoefficientDirectImageMap f (pbcIntegralDatum c.l F) ≫
        (proEtaleSheafDirectImage f CommRingCat.{u + 1}).map a := by
    rw [hc]
    exact coefficientSquare c.l F f
  have hcomm : r.hom ≫ a =
      (proEtaleSheafInverseImage f CommRingCat.{u + 1}).map a ≫ t.hom := by
    apply ((proEtaleSheafAdjunction f CommRingCat.{u + 1}).homEquiv _ _).injective
    have hr : ((proEtaleSheafAdjunction f CommRingCat.{u + 1}).homEquiv A A)
        r.hom =
        AlgebraicGeometry.Scheme.completedCoefficientDirectImageMap f
          (pbcIntegralDatum c.l F) := by
      rw [Adjunction.homEquiv_unit]
      rfl
    have ht : ((proEtaleSheafAdjunction f CommRingCat.{u + 1}).homEquiv B B)
        t.hom = sfCompletedCoefficientMap c.l F f := by
      change ((proEtaleSheafAdjunction f CommRingCat.{u + 1}).homEquiv _ _)
        (((proEtaleSheafAdjunction f CommRingCat.{u + 1}).homEquiv _ _).symm _) = _
      exact Equiv.apply_symm_apply _ _
    calc
      _ = ((proEtaleSheafAdjunction f CommRingCat.{u + 1}).homEquiv A A)
          r.hom ≫ (proEtaleSheafDirectImage f CommRingCat.{u + 1}).map a :=
        Adjunction.homEquiv_naturality_right _ _ _
      _ = a ≫ sfCompletedCoefficientMap c.l F f := by rw [hr]; exact hs.symm
      _ = ((proEtaleSheafAdjunction f CommRingCat.{u + 1}).homEquiv A B)
          ((proEtaleSheafInverseImage f CommRingCat.{u + 1}).map a ≫ t.hom) := by
        rw [Adjunction.homEquiv_naturality_left]
        exact congrArg (fun z ↦ a ≫ z) ht.symm
  let k := proEtaleRingRestrictionPullbackInv f A B A B a a r t hcomm
  have : IsIso k := proEtaleRingRestrictionPullbackInv_isIso f A B A B a a r t hcomm
  let L := FrobeniusCoefficientTwists.line c.l F X m
  let e := (asIso k).app L ≪≫ (pbcRestrict a).mapIso
    (FrobeniusCoefficientTwists.signedLineMaps c.l F f m)
  have hk (V : X.ProEt) (x : L.val.obj (op V)) :
      (k.app L).val.app (op ((proEtaleBaseChange f).obj V))
          (sectionMap D c X₀ E (line D c X₀ E m) V x) =
        FrobeniusCoefficientTwists.moduleSection c.l F f L V x := by
    let adj := proEtaleRingModuleAdjunction f A A r
    let adj' := proEtaleRingModuleAdjunction f B B t
    let d := proEtaleRingRestrictionDirectImage f A B A B a a r t hcomm
    let N := (proEtaleRingModulePullback f B B t).obj L
    have happ : k.app L = (adj.homEquiv _ _).symm
        ((proEtaleRingRestrictScalars a).map (adj'.unit.app L) ≫ d.hom.app N) := by
      simp only [Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc]
      rfl
    have hm := (adj.homEquiv _ _).apply_symm_apply
      ((proEtaleRingRestrictScalars a).map (adj'.unit.app L) ≫ d.hom.app N)
    rw [← happ, Adjunction.homEquiv_unit] at hm
    have hx := congrArg (fun q ↦ q.val.app (op V) x) hm
    have hd := (Classical.choose_spec (proEtaleRingRestrictionDirectImage_existsUnique
      f A B A B a a r t hcomm)).1 N (op V)
        (FrobeniusCoefficientTwists.moduleSection c.l F f L V x)
    change (k.app L).val.app (op ((proEtaleBaseChange f).obj V)) _ =
      (d.hom.app N).val.app (op V)
        (FrobeniusCoefficientTwists.moduleSection c.l F f L V x) at hx
    exact hx.trans hd
  have he (V : X.ProEt) (x : L.val.obj (op V)) :
      HEq (e.hom.val.app (op ((proEtaleBaseChange f).obj V))
          (sectionMap D c X₀ E (line D c X₀ E m) V x))
        ((FrobeniusCoefficientTwists.signedLineMaps c.l F f m).hom.val.app
          (op ((proEtaleBaseChange f).obj V))
          (FrobeniusCoefficientTwists.moduleSection c.l F f L V x)) := by
    apply heq_of_eq
    change (FrobeniusCoefficientTwists.signedLineMaps c.l F f m).hom.val.app _
      ((k.app L).val.app _ _) = _
    rw [hk]
  refine ⟨e, he, ?_⟩
  intro e' he'
  apply Iso.ext
  apply ((proEtaleRingModuleAdjunction f A A r).homEquiv _ _).injective
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro V
  ext x
  exact eq_of_heq ((he' V.unop x).trans (he V.unop x).symm)

/-- Every signed line belongs to the actual PBC integral coefficient category.
Source: definition, one-stratum perfect model R[0] (blueprint: def-wf-tate-twist).
Proof: the completed root line is locally free of rank one with its compatible
finite reductions. The unit, all positive powers and their duals have the same
local model R[0]. The geometric fibre is noetherian and finite dimensional and
l is invertible. The stratified-perfect characterization therefore applies with
one stratum, giving bounded constructibility, completeness and compatible etale
origin. Coefficient restriction along the canonical isomorphism preserves these
conditions and gives precisely the PBC line written here. -/
theorem line_mem (m : ℤ) :
    PbcIsBoundedConstructibleComplete (D.geometricFiber X₀).left
      (pbcStageDatum.{u} c.l c.Qbar E)
      ((DerivedCategory.singleFunctor _ 0).obj (line D c X₀ E m)) := by
  let X := (D.geometricFiber X₀).left
  let F := pbcFiniteField.{u} c.l c.Qbar E
  let R := pbcRestrict (purCoefficientIso c.l F X).hom
  have hdim := (weilGeometricFiber_coefficientHypotheses D c X₀).2.1
  have hinv := (weilGeometricFiber_coefficientHypotheses D c X₀).2.2
  have hl : IsUnit (c.l : Γ(X, ⊤)) :=
    X.toRingedSpace.isUnit_of_isUnit_germ ⊤ _ (by
      intro x hx
      simpa only [map_natCast] using hinv x)
  have hM := intrinsicIntegralCoefficientTwist_mem D c.l c.different F X m
  have hK := (integralStratifiedPerfectDetailed X c.l F hdim hl _).mp hM
  have he := congrArg Iso.hom
    (purCoefficientIso_existsUnique c.l F X).exists.choose_spec
  let P : ObjectProperty (PbcCompletedDerived X (pbcIntegralDatum c.l F)) :=
    PbcIsBoundedConstructibleComplete X (pbcIntegralDatum c.l F)
  have hP := pbcIntegralUniformComplete_isTriangulated c.l F X hdim hinv
  have : P.IsClosedUnderIsomorphisms := hP.1
  let S := SheafOfModules.restrictScalars.{u + 1}
    (integralDetailedCoefficientComparison X c.l F).hom
  have : PreservesFiniteLimits S := (integralDetailedCoefficientRestriction_exact X c.l F).1
  have : PreservesFiniteColimits S := (integralDetailedCoefficientRestriction_exact X c.l F).2
  have hRS : R = S := congrArg SheafOfModules.restrictScalars he
  have hK' : P (R.mapDerivedCategory.obj
      (integralCoefficientTwist D c.l c.different F X m)) := by
    exact P.prop_of_iso
      ((Functor.mapDerivedCategoryNatIso (eqToIso hRS)).app _).symm hK
  exact P.prop_of_iso
    ((R.mapDerivedCategorySingleFunctor 0).app
      (FrobeniusCoefficientTwists.line c.l F X m)) hK'

/-- Exact sheaf tensor with the existing signed line.
Source: definition, K(m) (blueprint: def-wf-tate-twist). -/
abbrev tensor (m : ℤ) :=
  pbcTateSheafTensor c.l (D.geometricFiber X₀).left (pbcFiniteField.{u} c.l c.Qbar E) m

/-- The unique ordinary tensor/pullback comparison, followed by the root-line map.
The formula tests every module, every local section and every signed-line section;
thus it fixes the entire natural isomorphism, including the negative exponents.
Source: definition, induced tensor Weil map (blueprint: def-wf-tate-twist).
Proof: the module pullback tensor comparison sends a pulled pure tensor x tensor y
to pulled x tensor pulled y. Compose the second factor with lineMap. The coefficient
isomorphism preserves balancing. These formulas give inverse maps by inverse transport
and the inverse line map. They are natural in the input module. Local pure tensors
generate after sheafification, and adjunction-unit sections generate pullback, so the
formula determines the comparison uniquely. -/
theorem tensorComparison_exists (m : ℤ) :
    ∃! g : tensor D c X₀ E m ⋙ pull D c X₀ E ≅
        pull D c X₀ E ⋙ tensor D c X₀ E m,
      ∀ (M : Modules D c X₀ E) (V : (D.geometricFiber X₀).left.ProEt)
        (x : M.val.obj (op V)) (y : (line D c X₀ E m).val.obj (op V)),
        HEq ((g.hom.app M).val.app (op ((proEtaleBaseChange
          (D.geometricFrobenius X₀).hom).obj V))
            (sectionMap D c X₀ E ((tensor D c X₀ E m).obj M) V
              (SheafOfModules.siteSheafTensorTmul
                ((purOrdinaryCoefficientModel c.l (pbcFiniteField.{u} c.l c.Qbar E)
                  (D.geometricFiber X₀).left).obj M)
                (FrobeniusCoefficientTwists.line c.l (pbcFiniteField.{u} c.l c.Qbar E)
                  (D.geometricFiber X₀).left m) (op V) x y)))
          (SheafOfModules.siteSheafTensorTmul
            ((purOrdinaryCoefficientModel c.l (pbcFiniteField.{u} c.l c.Qbar E)
              (D.geometricFiber X₀).left).obj ((pull D c X₀ E).obj M))
            (FrobeniusCoefficientTwists.line c.l (pbcFiniteField.{u} c.l c.Qbar E)
              (D.geometricFiber X₀).left m)
            (op ((proEtaleBaseChange (D.geometricFrobenius X₀).hom).obj V))
            (sectionMap D c X₀ E M V x)
            ((lineMap D c X₀ E m).hom.val.app
              (op ((proEtaleBaseChange (D.geometricFrobenius X₀).hom).obj V))
              (sectionMap D c X₀ E (line D c X₀ E m) V y))) := by
  sorry

/-- The ordinary comparison with its unique pure-tensor normalization.
Source: definition, tensor Frobenius map (blueprint: def-wf-tate-twist). -/
def tensorComparison (m : ℤ) := (tensorComparison_exists D c X₀ E m).exists.choose

/-- Exact descent of the ordinary tensor/pullback comparison to the derived category.
Source: definition, completed derived tensor with a line (blueprint: def-wf-tate-twist). -/
def ambientComparison (m : ℤ) :
    (tensor D c X₀ E m).mapDerivedCategory ⋙ (pull D c X₀ E).mapDerivedCategory ≅
      (pull D c X₀ E).mapDerivedCategory ⋙ (tensor D c X₀ E m).mapDerivedCategory :=
  (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryNatIso (tensorComparison D c X₀ E m) ≪≫
      Functor.mapDerivedCategoryCompIso _ _

/-- Restriction of the actual exact line tensor to the integral coefficient category.
Source: definition, integral representatives (blueprint: def-wf-tate-twist). -/
def integral (m : ℤ) :=
  pbcConditionalIntegral (pbcStageDatum.{u} c.l c.Qbar E)
    (pbcTateAmbient c.l (D.geometricFiber X₀).left (pbcFiniteField.{u} c.l c.Qbar E) m)
    (pbcTateAmbient_mem c.l (D.geometricFiber X₀).left
      (pbcFiniteField.{u} c.l c.Qbar E)
      (weilGeometricFiber_coefficientHypotheses D c X₀).2.1 m)

/-- The existing rational twist, with the geometric hypotheses supplied by finite type.
Source: definition, raw rationalization of K(m) (blueprint: def-wf-tate-twist). -/
def rational (m : ℤ) :=
  letI : Fact (∃ n : ℕ, topologicalKrullDim (D.geometricFiber X₀).left ≤ n) :=
    ⟨(weilGeometricFiber_coefficientHypotheses D c X₀).2.1⟩
  pbcTateRational c.l (D.geometricFiber X₀).left c.Qbar E m

/-- Restrict and rationalize the prescribed comparison, without choosing a new map.
Its components on integral representatives are exactly the ambient derived comparison.
Source: definition, rational tensor Weil map (blueprint: def-wf-tate-twist).
Proof: tensor by a rank-one line preserves complete stratified-perfect objects by
the single-stratum criterion. Transport also preserves this full subcategory. Thus
the ambient comparison restricts uniquely. Apply raw scalar localization to its
components: denominators have the same scalar on both sides, so naturality extends
to every localized arrow. The integral representative equation below and linearity
fix the resulting natural isomorphism uniquely. -/
theorem rationalComparison_exists (m : ℤ) :
    ∃! g : rational D c X₀ E m ⋙ weilFrobeniusPullback D c X₀ E ≅
        weilFrobeniusPullback D c X₀ E ⋙ rational D c X₀ E m,
      ∀ K : pbcIntegralStage c.l c.Qbar (D.geometricFiber X₀).left E,
        HEq (g.hom.app ((pbcStageLocalization c.l c.Qbar
          (D.geometricFiber X₀).left E).obj K))
          ((pbcStageLocalization c.l c.Qbar (D.geometricFiber X₀).left E).map
            (ObjectProperty.homMk
              (X := (pbcIsoIntegralPullback (D.geometricFrobenius X₀).hom
                (pbcStageDatum.{u} c.l c.Qbar E)).obj ((integral D c X₀ E m).obj K))
              (Y := (integral D c X₀ E m).obj
                ((pbcIsoIntegralPullback (D.geometricFrobenius X₀).hom
                  (pbcStageDatum.{u} c.l c.Qbar E)).obj K))
              ((ambientComparison D c X₀ E m).hom.app K.obj))) := by
  let T := integral D c X₀ E m
  have : T.Additive := by
    dsimp [T, integral]
    infer_instance
  have : T.Linear (PbcIntegralRing c.l (pbcFiniteField.{u} c.l c.Qbar E)) := by
    dsimp [T, integral]
    infer_instance
  let P := pbcIsoIntegralPullback (D.geometricFrobenius X₀).hom
    (pbcStageDatum.{u} c.l c.Qbar E)
  let a : T ⋙ P ≅ P ⋙ T := NatIso.ofComponents
    (fun K ↦ ObjectProperty.isoMk _ ((ambientComparison D c X₀ E m).app K.obj))
    (fun f ↦ by
      apply ObjectProperty.hom_ext
      exact (ambientComparison D c X₀ E m).hom.naturality f.hom)
  obtain ⟨e, he, hu⟩ := localizedCommutingComparison
    (PbcIntegralRing c.l (pbcFiniteField.{u} c.l c.Qbar E)) _
    (pbcStageUniformizer.{u} c.l c.Qbar E) T P a
  refine ⟨e, fun K ↦ he ⟨K⟩, ?_⟩
  intro e' he'
  exact hu e' (fun K ↦ he' K.obj)

end WeilConjectures.WfTateTwist
