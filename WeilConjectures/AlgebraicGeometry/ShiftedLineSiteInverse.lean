/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.PurityFiniteSetting
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import WeilConjectures.SixFunctors.Etale.Derived.LocallyConstantInvertible
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ComparisonMonoidal
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.TorAmplitude
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ConstructibleIntrinsic
public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes
public import WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType

import WeilConjectures.AlgebraicGeometry.EtaleTorAmplitude
import WeilConjectures.AlgebraicGeometry.FiniteTorAmplitudeSites
import WeilConjectures.AlgebraicGeometry.ProEtaleSiteComparisonSupplement
import WeilConjectures.AlgebraicGeometry.FlatConstructibleTensor
import WeilConjectures.Algebra.Homology.BoundedAboveFlatSheafKFlatSupplement
import WeilConjectures.AlgebraicGeometry.FiniteTensorConstructibleCohomology
import WeilConjectures.Algebra.Homology.FlatSingleDerivedNormalization
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FiniteFreeDualPullback
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.LineEvaluationInversePair
import WeilConjectures.AlgebraicGeometry.ComparisonPullbackExact
import WeilConjectures.Algebra.Homology.RingedDerivedClosedSymmetricMonoidal
import WeilConjectures.Algebra.Homology.RingedKFlatSingleTensorComparison
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Homology.HomologicalComplex
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import WeilConjectures.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import Mathlib.CategoryTheory.Localization.Construction
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import Mathlib.CategoryTheory.Functor.Currying
import Mathlib.CategoryTheory.Whiskering
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.RingTheory.Flat.CategoryTheory
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.CategoryTheory.Localization.Prod
import Mathlib.Algebra.Homology.BifunctorFlip
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorHomotopy
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import Mathlib.Algebra.Homology.DerivedCategory.Fractions
import Mathlib.CategoryTheory.Localization.CalculusOfFractions
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.SiteTensorFunctorialitySupplement
import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import WeilConjectures.Algebra.Homology.KFlatFixedTensorTriangulatedSupplement
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
import WeilConjectures.Algebra.Homology.KFlatTensorPreservesQuasiIsoIndependentCoefficients
import WeilConjectures.Algebra.Homology.PrincipalKoszulQuotientTowersSupplement
import WeilConjectures.SixFunctors.RingedDerivedMonoidalComparisons
import WeilConjectures.Algebra.Homology.DerivedTensorShiftDescent
import WeilConjectures.AlgebraicGeometry.PullbackTensorCanonicalShiftUnit
public import WeilConjectures.AlgebraicGeometry.RingedTopoiCanonicalTensorPullbackOfUniverses
public import WeilConjectures.AlgebraicGeometry.IntrinsicFiniteTorsionConstructibility
public import WeilConjectures.AlgebraicGeometry.ComparisonDerivedPullbackFixed

/-! # Shifted line inverses on the etale and pro-etale sites

Source: main-20261015, sk-prop-cohsm, thm-pur-cohomological-smoothness, first paragraph;
Stacks Project, Tags 0B8Q, 0B8N, 06YQ, 07A4 and 0FNH.
(blueprint: lem-pur-shifted-line-site-inverse)
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v w d h

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace AlgebraicGeometry.ProEtale

/-- The canonical comparison for exact inverse image from the etale to the pro-etale
site. This is an abbreviation for the existing left-derived tensor comparison, with its
canonical identifications with termwise exact inverse image. It retains the general
ringed-topos representative normalization and makes no new choice.
Source: Stacks Project, Tag 07A4
(blueprint: lem-pur-shifted-line-site-inverse). -/
noncomputable abbrev siteComparisonCanonicalDerivedTensor
    (B : Type v) [Category.{u + 1} B] [Abelian B]
    [IsGrothendieckAbelian.{u + 1} B] [MonoidalCategory B] [MonoidalPreadditive B]
    [SymmetricCategory B] [MonoidalClosed B] [Abelian.HasFunctorialFlatResolution B]
    (T : Scheme.{u}) [(comparisonUpperStar B T).PreservesFlat]
    (K : DerivedCategory (Sheaf T.smallEtaleTopology B)) :
    (Etale.derivedTensor B T).obj K ⋙ (comparisonUpperStar B T).mapDerivedCategory ≅
      (comparisonUpperStar B T).mapDerivedCategory ⋙
        (derivedTensor B T).obj ((comparisonUpperStar B T).mapDerivedCategory.obj K) :=
  derivedTensorObjCompMapDerivedCategoryComparisonUpperStarIso B K

end AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry.ShiftedLineSiteInverse

section Normalization

variable {C : Type v} [Category.{w} C] [Abelian C] [IsGrothendieckAbelian.{w} C]
  [MonoidalCategory C] [MonoidalPreadditive C] [SymmetricCategory C] [MonoidalClosed C]
  [Abelian.HasFunctorialFlatResolution C]

/-- The canonical single-term tensor comparison, obtained from the localization's lax
monoidal comparison and the sole degree-zero tensor summand. No inverse is chosen.
Source: Stacks 06YQ (blueprint: lem-pur-shifted-line-site-inverse). -/
def singleTensorMap (L M : C) :
    (DerivedCategory.singleFunctor C 0).obj L ⊗
      (DerivedCategory.singleFunctor C 0).obj M ⟶
        (DerivedCategory.singleFunctor C 0).obj (L ⊗ M) :=
  (tensorIso
    ((DerivedCategory.singleFunctorIsoCompQ C 0).app L ≪≫
      (DerivedCategory.quotientCompQhIso C).symm.app _)
    ((DerivedCategory.singleFunctorIsoCompQ C 0).app M ≪≫
      (DerivedCategory.quotientCompQhIso C).symm.app _)).hom ≫
  Functor.LaxMonoidal.μ (DerivedCategory.Qh (C := C)) _ _ ≫
  DerivedCategory.Qh.map
    ((Functor.Monoidal.μIso (HomotopyCategory.quotient C (.up ℤ)) _ _).hom ≫
      (HomotopyCategory.quotient C (.up ℤ)).map
        ((((CochainComplex.map₂HomologicalComplexObjSingleIso
          (curriedTensor C) L).app _) ≪≫
          ((HomologicalComplex.singleMapHomologicalComplex
            (tensorLeft L) (.up ℤ) 0).app M)).hom)) ≫
  ((DerivedCategory.singleFunctorIsoCompQ C 0).app (L ⊗ M) ≪≫
    (DerivedCategory.quotientCompQhIso C).symm.app _).inv

/-- Evaluation of oppositely shifted degree-zero sheaves. Extract the first shift and
then the second by the signed total-tensor comparisons, cancel their sum, and evaluate
on the sole degree-zero term. In particular the reverse order is specified separately,
without inserting the graded braiding.
Source: Stacks 0FNH and 06YQ (blueprint: lem-pur-shifted-line-site-inverse). -/
def evaluation (L M : C) (e : L ⊗ M ⟶ 𝟙_ C) (m : ℤ) :
    ((DerivedCategory.singleFunctor C 0).obj L)⟦m⟧ ⊗
      ((DerivedCategory.singleFunctor C 0).obj M)⟦-m⟧ ⟶ 𝟙_ (DerivedCategory C) :=
  (DerivedCategory.shiftTensorShiftIso C _ _ m (-m)).hom ≫
  (shiftFunctorZero' _ (m + -m) (add_neg_cancel m)).hom.app _ ≫
  singleTensorMap L M ≫ (DerivedCategory.singleFunctor C 0).map e ≫
  (DerivedCategory.singleFunctorObjUnitIso C).hom

end Normalization

section Comparison

variable (B : Type v) [Category.{u + 1} B] [Abelian B]
  [IsGrothendieckAbelian.{u + 1} B] [MonoidalCategory B] [MonoidalPreadditive B]
  [SymmetricCategory B] [MonoidalClosed B] [Abelian.HasFunctorialFlatResolution B]
  (T : Scheme.{u})

/-- The existing exact inverse image in the fixed constant-ring presentation.
Source: Stacks 099R (blueprint: lem-pur-shifted-line-site-inverse). -/
abbrev inverseImage := ProEtale.comparisonUpperStar B T

/-- The termwise derived comparison on the unbounded derived categories.
Source: Stacks 099R (blueprint: lem-pur-shifted-line-site-inverse). -/
abbrev derivedInverseImage := (inverseImage B T).mapDerivedCategory

/-- The canonical comparison of a pulled internal dual with the dual of the pulled line.
Source: Stacks 0GMX (blueprint: lem-pur-shifted-line-site-inverse). -/
def dualComparison (L : Sheaf T.smallEtaleTopology B) :
    (inverseImage B T).obj ((ihom L).obj (𝟙_ _)) ⟶
      (ihom ((inverseImage B T).obj L)).obj (𝟙_ _) :=
  (Functor.LaxMonoidal.ihomComparison (inverseImage B T) L).natTrans.app (𝟙_ _) ≫
    (ihom ((inverseImage B T).obj L)).map (Functor.OplaxMonoidal.η (inverseImage B T))

/-- Pullback of a sheaf pairing, with the canonical tensor and coefficient-unit maps.
Source: Stacks 07A4 and 0GMX (blueprint: lem-pur-shifted-line-site-inverse). -/
def pulledPairing (L M : Sheaf T.smallEtaleTopology B)
    (e : L ⊗ M ⟶ 𝟙_ _) :
    (inverseImage B T).obj L ⊗ (inverseImage B T).obj M ⟶ 𝟙_ _ :=
  Functor.LaxMonoidal.μ (inverseImage B T) L M ≫
    (inverseImage B T).map e ≫ Functor.OplaxMonoidal.η (inverseImage B T)

/-- Canonical comparison on a shifted single sheaf, including its signed shift map.
Source: Stacks 099R and 0FNH (blueprint: lem-pur-shifted-line-site-inverse). -/
def shiftedSingleComparison (L : Sheaf T.smallEtaleTopology B)
    (m : ℤ) :
    (derivedInverseImage B T).obj (((DerivedCategory.singleFunctor _ 0).obj L)⟦m⟧) ≅
      ((DerivedCategory.singleFunctor _ 0).obj ((inverseImage B T).obj L))⟦m⟧ :=
  ((derivedInverseImage B T).commShiftIso m).app _ ≪≫
    (shiftFunctor _ m).mapIso (((inverseImage B T).mapDerivedCategorySingleFunctor 0).app L)

/-- The derived coefficient-unit comparison, induced from the ordinary unit comparison.
Source: Stacks 07A4 (blueprint: lem-pur-shifted-line-site-inverse). -/
def unitComparison : (derivedInverseImage B T).obj (𝟙_ _) ≅ 𝟙_ _ :=
  (derivedInverseImage B T).mapIso (DerivedCategory.singleFunctorObjUnitIso _).symm ≪≫
  ((inverseImage B T).mapDerivedCategorySingleFunctor 0).app _ ≪≫
  (DerivedCategory.singleFunctor _ 0).mapIso
    (asIso (Functor.OplaxMonoidal.η (inverseImage B T))) ≪≫
  DerivedCategory.singleFunctorObjUnitIso _

/-- The commuting square for the specified derived evaluation, using the canonical
K-flat tensor comparison, signed single-shift comparisons, and coefficient-unit comparison.
Source: Stacks 07A4 and 0GMX (blueprint: lem-pur-shifted-line-site-inverse). -/
def evaluationComparison [(inverseImage B T).PreservesFlat]
    (L M : Sheaf T.smallEtaleTopology B)
    (e : L ⊗ M ⟶ 𝟙_ _) (m : ℤ) : Prop :=
  (derivedInverseImage B T).map (evaluation L M e m) ≫ (unitComparison B T).hom =
    (ProEtale.siteComparisonCanonicalDerivedTensor
      B T (((DerivedCategory.singleFunctor _ 0).obj L)⟦m⟧)).hom.app
        (((DerivedCategory.singleFunctor _ 0).obj M)⟦-m⟧) ≫
    (tensorIso (shiftedSingleComparison B T L m)
      (shiftedSingleComparison B T M (-m))).hom ≫
    evaluation ((inverseImage B T).obj L) ((inverseImage B T).obj M)
      (pulledPairing B T L M e) m

end Comparison

variable (A : Type (u + 1)) [CommRing A] (T : Scheme.{u})

/-- The covering-sieve formulation of local isomorphy, used here only to spell out
that each of the four sheaves is a line over its specified constant coefficient unit.
Source: Stacks 0B8Q (blueprint: lem-pur-shifted-line-site-inverse). -/
def locallyIsomorphic {B : Type v} [Category.{w} B] (J : GrothendieckTopology B)
    {D : Type d} [Category.{h} D] (F G : Sheaf J D) : Prop :=
  ∀ U : B, ∃ s : Sieve U, s ∈ J U ∧
    ∀ (V : B) (f : V ⟶ U), s f → Nonempty (F.over V ≅ G.over V)

/-- Finiteness of the prescribed positive-level quotient, transported by the standard
universe lift. Source: blueprint purity conventions; Stacks finite coefficient setting
(blueprint: lem-pur-shifted-line-site-inverse). -/
instance coefficientFinite (P : WeilConjectures.PurityFiniteSetting.{u}) :
    Finite P.Coefficient :=
  letI : Finite P.Ring := Padic.finite_coefficientExtensionRing
    P.coefficients.l P.extension P.level P.level_pos
  inferInstanceAs (Finite (ULift.{u + 1} P.Ring))

/-- The sheaf dual is the existing closed sheaf-category internal Hom into the unit.
Source: Stacks 0B8Q (blueprint: lem-pur-shifted-line-site-inverse). -/
abbrev dual (L : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) :=
  (ihom L).obj (𝟙_ _)

/-- An etale sheaf placed in the stated shifted degree in the ordinary derived category.
Source: Stacks 06YQ (blueprint: lem-pur-shifted-line-site-inverse). -/
abbrev etaleSingle (L : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) (m : ℤ) :=
  ((DerivedCategory.singleFunctor _ 0).obj L)⟦m⟧

/-- The corresponding pro-etale sheaf in the ordinary derived category.
Source: Stacks 099R (blueprint: lem-pur-shifted-line-site-inverse). -/
abbrev proEtaleSingle (L : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) (m : ℤ) :=
  ((DerivedCategory.singleFunctor _ 0).obj ((inverseImage (ModuleCat.{u + 1} A) T).obj L))⟦m⟧

/-- The specified ordinary evaluation, sending a local basis and its dual to one.
Source: Stacks 0B8Q (blueprint: lem-pur-shifted-line-site-inverse). -/
def pairing (L : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) :
    L ⊗ dual A T L ⟶ 𝟙_ _ :=
  (ihom.ev L).app (𝟙_ _)

/-- The reverse ordinary evaluation, before shifting. Its formula is multiplication,
without the sign of the derived braiding on the shifted factors.
Source: Stacks 0B8N and 0FNH (blueprint: lem-pur-shifted-line-site-inverse). -/
def reversePairing (L : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) :
    dual A T L ⊗ L ⟶ 𝟙_ _ :=
  (β_ (dual A T L) L).hom ≫ pairing A T L

/-- The two factors: false is the line, true is its internal sheaf dual.
Source: Stacks 0B8Q (blueprint: lem-pur-shifted-line-site-inverse). -/
def factor (L : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) (b : Bool) :
    Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A) :=
  if b then dual A T L else L

/-- The shift of the line and the opposite shift of its dual.
Source: Stacks 0FNH (blueprint: lem-pur-shifted-line-site-inverse). -/
def factorShift (m : ℤ) (b : Bool) : ℤ := if b then -m else m

/-- The two ordinary pairings, in their stated orders.
Source: Stacks 0B8N (blueprint: lem-pur-shifted-line-site-inverse). -/
def factorPairing (L : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) (b : Bool) :
    factor A T L b ⊗ factor A T L (!b) ⟶ 𝟙_ _ :=
  match b with
  | false => pairing A T L
  | true => reversePairing A T L

/-- A shifted etale line has the oppositely shifted internal dual as its specified
inverse, on both sites, compatibly with the canonical comparison. Tensoring with either
factor preserves bounded constructibility and translates every universal Tor interval.
No absolute separatedness or constructibility condition on Tor-test sheaves is imposed.

Source: main-20261015, sk-prop-cohsm, thm-pur-cohomological-smoothness, first paragraph;
Stacks 0B8Q, 0B8N, 0GMX, 06YQ, 07A4, 0FNH, 095I, 0961 and 094H.
(blueprint: lem-pur-shifted-line-site-inverse)

Proof plan:
1. Apply lem-pur-sheaf-line-evaluation-inverse-pair to L on the etale site. On a
   local basis e its dual basis gives evaluation (ae) tensor (be-dual) to ab, inverse
   a to ae tensor e-dual. Changing e by a unit changes the dual by its inverse.
   Both sheaves are flat. Their finite locally constant values make them constructible
   on the one-stratum stratification, by def-weil-pbc-constructible-complexes.
2. The site inclusion preserves finite limits and covers. Apply
   lem-sf-comparison-pullback-exact and lem-pur-ringed-site-finite-free-dual-pullback.
   The pulled dual is the dual of the pulled line, with the pulled dual basis, and both
   pulled sheaves are locally the unit, flat and constructible.
3. By lem-pc-bounded-above-flat-kflat-site the flat singles and their shifts are K-flat.
   Use lem-sf-ringed-kflat-single-tensor-comparison and
   lem-weil-pbc-derived-tensor-shift-descent to compute both total tensors in degree zero.
   Apply their respective ordinary evaluations. The reverse arrow is specified on its
   own term, rather than obtained from the graded braiding, which would introduce (-1)^m.
4. Apply lem-weil-pbc-ringed-topoi-derived-tensor-pullback and
   lem-weil-pbc-pullback-tensor-canonical-shift-unit. On flat representatives both
   comparison/evaluation composites take a tensor (x tensor phi) to a phi(x).
   Thus the precise evaluations, not just their endpoints, agree under comparison.
5. Test each shifted line P[s] against every module sheaf M in degree zero.
   The K-flat-single calculation is (P tensor M)[s], concentrated in degree -s.
   The constructible single cohomology sheaf gives bounded constructibility.
6. By lem-pur-flat-single-derived-normalization and tensor-shift descent,
   H^r(K tensor P[s]) is H^(r+s)(K) tensor P. Hence boundedness shifts by -s.
7. Apply lem-fd-flat-constructible-tensor on the etale site and
   lem-pur-finite-tensor-constructible-cohomology on the pro-etale site; ell is invertible
   since T is over the prescribed field. This gives constructibility without separatedness.
8. For an arbitrary Tor-test sheaf M, use
   lem-sf-ringed-derived-closed-symmetric-monoidal and
   lem-sfb-ringed-derived-monoidal-comparisons to identify
   (K tensor P[s]) tensor M with (K tensor M) tensor P[s]. Step 6 translates
   [a,b] to [a-s,b-s]. Substitute s=m and s=-m, on each site.
-/
theorem shifted_line_site_inverse
    (P : WeilConjectures.PurityFiniteSetting.{u}) (T : Scheme.{u})
    [T.Over (Spec (CommRingCat.of P.field.k))]
    [LocallyOfFiniteType (T ↘ Spec (CommRingCat.of P.field.k))]
    [QuasiCompact (T ↘ Spec (CommRingCat.of P.field.k))]
    (L : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient))
    (hL : locallyIsomorphic T.smallEtaleTopology L (𝟙_ _)) (m : ℤ) :
    IsIso (dualComparison (ModuleCat.{u + 1} P.Coefficient) T L) ∧
    pulledPairing (ModuleCat.{u + 1} P.Coefficient) T L
      (dual P.Coefficient T L)
      (pairing P.Coefficient T L) =
        ((inverseImage (ModuleCat.{u + 1} P.Coefficient) T).obj L ◁
          dualComparison (ModuleCat.{u + 1} P.Coefficient) T L) ≫
          (ihom.ev ((inverseImage (ModuleCat.{u + 1} P.Coefficient) T).obj L)).app (𝟙_ _) ∧
    ∀ b : Bool,
      Scheme.IsConstructibleEtaleModuleSheaf (factor P.Coefficient T L b) ∧
      ObjectProperty.flat (factor P.Coefficient T L b) ∧
      ProEtale.IsConstructible P.Coefficient
        ((inverseImage (ModuleCat.{u + 1} P.Coefficient) T).obj (factor P.Coefficient T L b)) ∧
      ObjectProperty.flat
        ((inverseImage (ModuleCat.{u + 1} P.Coefficient) T).obj (factor P.Coefficient T L b)) ∧
      locallyIsomorphic (Scheme.ProEt.topology T)
        ((inverseImage (ModuleCat.{u + 1} P.Coefficient) T).obj
          (factor P.Coefficient T L b)) (𝟙_ _) ∧
      IsIso (evaluation (factor P.Coefficient T L b) (factor P.Coefficient T L (!b))
        (factorPairing P.Coefficient T L b) (factorShift m b)) ∧
      IsIso (evaluation
        ((inverseImage (ModuleCat.{u + 1} P.Coefficient) T).obj (factor P.Coefficient T L b))
        ((inverseImage (ModuleCat.{u + 1} P.Coefficient) T).obj (factor P.Coefficient T L (!b)))
        (pulledPairing (ModuleCat.{u + 1} P.Coefficient) T _ _
          (factorPairing P.Coefficient T L b))
        (factorShift m b)) ∧
      evaluationComparison (ModuleCat.{u + 1} P.Coefficient) T _ _
        (factorPairing P.Coefficient T L b)
        (factorShift m b) ∧
      Etale.DerivedCategory.isBoundedConstructible P.Coefficient T
        (etaleSingle P.Coefficient T (factor P.Coefficient T L b) (factorShift m b)) ∧
      Etale.DerivedCategory.hasTorAmplitudeIn P.Coefficient T
        (-(factorShift m b)) (-(factorShift m b))
        (etaleSingle P.Coefficient T (factor P.Coefficient T L b) (factorShift m b)) ∧
      ProEtale.DerivedCategory.boundedConstructibleIntrinsic P.Coefficient T
        (proEtaleSingle P.Coefficient T (factor P.Coefficient T L b) (factorShift m b)) ∧
      ProEtale.DerivedCategory.torAmplitudeIn (ModuleCat.{u + 1} P.Coefficient) T
        (-(factorShift m b)) (-(factorShift m b))
        (proEtaleSingle P.Coefficient T (factor P.Coefficient T L b) (factorShift m b)) ∧
      (∀ (K : Etale.DerivedCategoryModule P.Coefficient T) (a c : ℤ),
        Etale.DerivedCategory.isBoundedConstructible P.Coefficient T K →
        Etale.DerivedCategory.hasTorAmplitudeIn P.Coefficient T a c K →
        Etale.DerivedCategory.isBoundedConstructible P.Coefficient T
          (((Etale.derivedTensor (ModuleCat.{u + 1} P.Coefficient) T).obj K).obj
            (etaleSingle P.Coefficient T (factor P.Coefficient T L b) (factorShift m b))) ∧
        Etale.DerivedCategory.hasTorAmplitudeIn P.Coefficient T
          (a - factorShift m b) (c - factorShift m b)
          (((Etale.derivedTensor (ModuleCat.{u + 1} P.Coefficient) T).obj K).obj
            (etaleSingle P.Coefficient T (factor P.Coefficient T L b) (factorShift m b)))) ∧
      (∀ (K : DerivedCategory
          (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} P.Coefficient))) (a c : ℤ),
        ProEtale.DerivedCategory.boundedConstructibleIntrinsic P.Coefficient T K →
        ProEtale.DerivedCategory.torAmplitudeIn (ModuleCat.{u + 1} P.Coefficient) T a c K →
        ProEtale.DerivedCategory.boundedConstructibleIntrinsic P.Coefficient T
          (((ProEtale.derivedTensor (ModuleCat.{u + 1} P.Coefficient) T).obj K).obj
            (proEtaleSingle P.Coefficient T (factor P.Coefficient T L b) (factorShift m b))) ∧
        ProEtale.DerivedCategory.torAmplitudeIn (ModuleCat.{u + 1} P.Coefficient) T
          (a - factorShift m b) (c - factorShift m b)
          (((ProEtale.derivedTensor (ModuleCat.{u + 1} P.Coefficient) T).obj K).obj
            (proEtaleSingle P.Coefficient T (factor P.Coefficient T L b) (factorShift m b)))) := by
  sorry

end AlgebraicGeometry.ShiftedLineSiteInverse
