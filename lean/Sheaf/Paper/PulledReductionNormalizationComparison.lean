/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q43
-/
module

public import Sheaf.Paper.PulledReductionStrictTowerComparison
public import Sheaf.Algebra.Homology.SuccessiveDerivedQuotientNormalization
public import Sheaf.Paper.FourCorners
public import Sheaf.Paper.AdicCoefficientDatum
public import Sheaf.Paper.PbcQbarCompletedPullback
public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
public import Mathlib.Algebra.Homology.BifunctorShift
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.Paper.ConstantCompletionEquivalence
import Sheaf.Paper.KFlatRingedToposPullback
import Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel
import Sheaf.Paper.RingedTopoiDerivedPullbackIndependent
import Sheaf.Algebra.Homology.FlatCoefficientReductionAdjunct
import Sheaf.Paper.KFlatScalarComparisonNormalization
import Sheaf.Paper.RingedTopoiTensorSections
import Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients

/-! # Successive normalizations of the pulled reduction comparison

Source: Stacks Project, sites-cohomology.tex, Tags 07A4, 0D6D and 0G7E;
current blueprint completed-pullback-reduction, paragraphs 1 and 2.
(blueprint: lem-weil-pbc-pulled-reduction-normalization-comparison).

All quotient indices are zero based: `n` denotes the positive exponent `n + 1`.
The maps retain the finite coefficient action and the universal computation counits.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genInjectivity false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genCtorIdx false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe t
open CategoryTheory CategoryTheory.Limits Opposite
open SheafOfModules.SuccessiveDerivedQuotient
namespace AlgebraicGeometry.Scheme.PulledNormalization

variable {A : Type (t + 1)} [CommRing A] (d : AdicCoefficientDatum A)
variable {X Y : Scheme.{t}} (g : X ⟶ Y)

/-- The existing scalar extension with its universal presentation, on the original site.
Source: Stacks 06YY (blueprint: lem-weil-pbc-pulled-reduction-normalization-comparison). -/
def scalarPresentation (T : Scheme.{t})
    {R S : Sheaf (ProEt.topology T) CommRingCat.{t + 1}} (a : R ⟶ S) :
    Presentation.{t + 1, t, t + 1, t + 2} a where
  ordinary := reductionChange T a
  obj_eq := (reductionChangeExistence T a).choose_spec.choose
  map_eq := (reductionChangeExistence T a).choose_spec.choose_spec.choose
  additive := reductionChangeAdditive T a
  derived := reductionDerivedChange T a
  counit := reductionDerivedCounit T a
  universal := reductionDerivedUniversal T a

attribute [local irreducible] reductionChange reductionDerivedChange Functor.mapDerivedCategory

/-- Finite inverse image with the specified finite coefficient identification.
Source: Stacks 0D6D (blueprint: lem-weil-pbc-pulled-reduction-normalization-comparison). -/
abbrev finitePull (n : ℕ) :=
  proEtaleRingModulePullback g (d.finiteRing Y n) (d.finiteRing X n) (d.finiteRingIso g n)

/-- The functor whose value is H_n, before forgetting the quotient action.
Source: Stacks 0D6D (blueprint: lem-weil-pbc-pulled-reduction-normalization-comparison). -/
def H (n : ℕ) := d.reduction Y n ⋙ (finitePull d g n).mapDerivedCategory

/-- The functor whose value is N_n, for arbitrary ambient completed inputs.
Source: Stacks 06YY (blueprint: lem-weil-pbc-pulled-reduction-normalization-comparison). -/
def N (n : ℕ) := PulledReduction.source d g ⋙
  reductionDerivedChange X (OrderedExchange.quotient d X n)

/-- The actual pulled finite complex functor, on modules in each cochain degree.
Source: Stacks 03EL (blueprint: lem-weil-pbc-pulled-reduction-normalization-comparison). -/
abbrev ordinaryH (n : ℕ) := reductionChange Y (d.projection Y n) ⋙ finitePull d g n

/-- The canonical comparison from H_n on a representative to the ordinary pulled complex.
Source: Stacks 06YY (blueprint: lem-weil-pbc-pulled-reduction-normalization-comparison). -/
def hCounit (n : ℕ) (P : CochainComplex (reductionModules Y (d.completedRing Y)) ℤ) :
    (H d g n).obj (DerivedCategory.Q.obj P) ⟶
      DerivedCategory.Q.obj (((ordinaryH d g n).mapHomologicalComplex (.up ℤ)).obj P) :=
  (finitePull d g n).mapDerivedCategory.map
      (reductionScalarComplexCounit Y (d.projection Y n) P) ≫
    (finitePull d g n).mapDerivedCategoryFactors.hom.app
      ((reductionChangeComplex Y (d.projection Y n)).obj P)

/-- The coefficient associativity equality for constant reduction.
Source: blueprint paragraph 1
(blueprint: lem-weil-pbc-pulled-reduction-normalization-comparison). -/
abbrev quotientComp (T : Scheme.{t}) (b a : ℕ) (h : a ≤ b) :
    OrderedExchange.quotient d T b ≫ reductionCoefficientMap T d b a h =
      OrderedExchange.quotient d T a :=
  (Category.assoc _ _ _).trans
    (congrArg (fun f ↦ exchangeScalar d T ≫ f)
      (completedReductionProjection_comp T d b a h))

/-- The recorded normalization interface, with the published coefficient sheafification
and locally-bijective comparison specified at the existing coefficient universe.
Source: Stacks 06YY, 0D6D
(blueprint: lem-weil-pbc-pulled-reduction-normalization-comparison). -/
abbrev ScalarNormalization (T : Scheme.{t}) :=
  @Normalization.{t + 1, t, t + 1, t + 2} T.ProEt inferInstance
    (essentiallySmallSelf.{0} T.ProEt) (ProEt.topology T) inferInstance
    (WeilConjectures.integralCoefficientAbLocallyBijective.{t, t} T)
    (WeilConjectures.integralCoefficientAbSheafify.{t, t} T)
    (fun R ↦ reductionModulesHasDerivedCategory T R)
    (fun {R S : Sheaf (ProEt.topology T) CommRingCat.{t + 1}}
      (a : R ⟶ S) ↦ scalarPresentation.{t} T a)

/-- The existing normalized derived scalar associator with explicit site instances.
Source: Stacks 0D6D (blueprint: lem-weil-pbc-pulled-reduction-normalization-comparison). -/
def scalarAssoc (T : Scheme.{t}) (nrm : ScalarNormalization T)
    {R S V : Sheaf (ProEt.topology T) CommRingCat.{t + 1}} (a : R ⟶ S) (b : S ⟶ V) :
    reductionDerivedChange T a ⋙ reductionDerivedChange T b ≅
      reductionDerivedChange T (a ≫ b) :=
  @Normalization.derived.{t + 1, t, t + 1, t + 2} T.ProEt inferInstance
    (essentiallySmallSelf.{0} T.ProEt) (ProEt.topology T) inferInstance
    (WeilConjectures.integralCoefficientAbLocallyBijective.{t, t} T)
    (WeilConjectures.integralCoefficientAbSheafify.{t, t} T)
    (fun U ↦ reductionModulesHasDerivedCategory T U)
    (fun {U V : Sheaf (ProEt.topology T) CommRingCat.{t + 1}}
      (f : U ⟶ V) ↦ scalarPresentation.{t} T f) nrm R S V a b

/-- The canonical successive scalar normalization of N, using the recorded normalized family.
Source: Stacks 0D6D (blueprint: lem-weil-pbc-pulled-reduction-normalization-comparison). -/
def thetaN (nrm : ScalarNormalization X)
    (b a : ℕ) (h : a ≤ b) :
    N d g b ⋙ reductionDerivedChange X (reductionCoefficientMap X d b a h) ≅ N d g a :=
  Functor.isoWhiskerLeft (PulledReduction.source d g)
    (scalarAssoc X nrm (OrderedExchange.quotient d X b)
      (reductionCoefficientMap X d b a h) ≪≫
      eqToIso (congrArg (fun f ↦ reductionDerivedChange X f) (quotientComp d X b a h)))


/-- The coefficient-square equation needed for the canonical inverse scalar mate.
Source: Stacks 0D6D (blueprint: lem-weil-pbc-pulled-reduction-normalization-comparison). -/
def QuotientCompatibility : Prop :=
  ∀ (b a : ℕ) (h : a ≤ b),
    (d.finiteRingIso g b).hom ≫ reductionCoefficientMap X d b a h =
      (proEtaleSheafInverseImage g CommRingCat.{t + 1}).map
        (reductionCoefficientMap Y d b a h) ≫ (d.finiteRingIso g a).hom

/-- Theta for H is the inverse scalar/pullback mate followed by pullback of the
specified completed normalization; no free comparison morphism is substituted.
Source: Stacks 0D6D, 07A4
(blueprint: lem-weil-pbc-pulled-reduction-normalization-comparison). -/
def thetaH (hq : QuotientCompatibility d g) (b a : ℕ) (h : a ≤ b) :
    H d g b ⋙ reductionDerivedChange X (reductionCoefficientMap X d b a h) ⟶ H d g a :=
  (Functor.associator (d.reduction Y b) (finitePull d g b).mapDerivedCategory
      (reductionDerivedChange X (reductionCoefficientMap X d b a h))).hom ≫
    Functor.whiskerLeft (d.reduction Y b)
      (proEtaleReductionPullbackInv g (d.finiteRing Y b) (d.finiteRing Y a)
        (d.finiteRing X b) (d.finiteRing X a)
        (reductionCoefficientMap Y d b a h) (reductionCoefficientMap X d b a h)
        (d.finiteRingIso g b) (d.finiteRingIso g a) (hq b a h)) ≫
    (Functor.associator (d.reduction Y b)
      (reductionDerivedChange Y (reductionCoefficientMap Y d b a h))
      (finitePull d g a).mapDerivedCategory).inv ≫
    Functor.whiskerRight (completedReductionDerivedNormalization Y d b a h)
      (finitePull d g a).mapDerivedCategory

/-- Ordinary inverse image of a section, with its finite scalar action retained.
Source: Stacks 03EL (blueprint: lem-weil-pbc-pulled-reduction-normalization-comparison). -/
def finiteGenerator (n : ℕ) (M : reductionModules Y (d.completedRing Y))
    (U : Y.ProEtᵒᵖ) (x : M.val.obj U) :
    ((ordinaryH d g n).obj M).val.obj ((proEtaleBaseChange g).op.obj U) :=
  ((proEtaleRingModuleAdjunction g (d.finiteRing Y n) (d.finiteRing X n)
      (d.finiteRingIso g n)).unit.app ((reductionChange Y (d.projection Y n)).obj M)).val.app U
    (reductionTensorSection Y (d.projection Y n) M U 1 x)

/-- The ordinary source of the finite comparison, using the same exact inverse image
as the strict-tower comparison. Source: Stacks 06YY, 03EL
(blueprint: lem-weil-pbc-pulled-reduction-normalization-comparison). -/
abbrev ordinaryN (n : ℕ) := PulledReduction.ordinarySource d g ⋙
  reductionChange X (OrderedExchange.quotient d X n)

/-- Inverse-image generator with its target scalar action made explicit.
Source: Stacks 03EL (blueprint: lem-weil-pbc-pulled-reduction-normalization-comparison). -/
def constantGenerator (M : reductionModules Y (d.completedRing Y))
    (U : Y.ProEtᵒᵖ) (x : M.val.obj U) :
    ((PulledReduction.ordinarySource d g).obj M).val.obj ((proEtaleBaseChange g).op.obj U) :=
  (((proEtaleRingModuleAdjunction g (exchangeConstantRing Y A)
    (exchangeConstantRing X A) (exchangeConstantIso g A)).unit.app
      ((PulledReduction.res d Y).obj M)).val.app U x)

/-- The comparison from N_n to its common ordinary K-flat computation.
Source: Stacks 06YY (blueprint: lem-weil-pbc-pulled-reduction-normalization-comparison). -/
def nCounit (n : ℕ) (P : CochainComplex (reductionModules Y (d.completedRing Y)) ℤ) :
    (N d g n).obj (DerivedCategory.Q.obj P) ⟶
      DerivedCategory.Q.obj (((ordinaryN d g n).mapHomologicalComplex (.up ℤ)).obj P) :=
  (reductionDerivedChange X (OrderedExchange.quotient d X n)).map
      ((PulledReduction.ordinarySource d g).mapDerivedCategoryFactors.hom.app P) ≫
    reductionScalarComplexCounit X (OrderedExchange.quotient d X n)
      (((PulledReduction.ordinarySource d g).mapHomologicalComplex (.up ℤ)).obj P)

/-- The actual derived scalar associator between two quotient changes.
Source: Stacks 0D6D (blueprint: lem-weil-pbc-pulled-reduction-normalization-comparison). -/
def quotientAssociator
    (nrm : ScalarNormalization X)
    (c b a : ℕ) (hab : a ≤ b) (hbc : b ≤ c) :
    reductionDerivedChange X (reductionCoefficientMap X d c b hbc) ⋙
        reductionDerivedChange X (reductionCoefficientMap X d b a hab) ≅
      reductionDerivedChange X (reductionCoefficientMap X d c a (hab.trans hbc)) :=
  scalarAssoc X nrm (reductionCoefficientMap X d c b hbc)
      (reductionCoefficientMap X d b a hab) ≪≫
    eqToIso (congrArg (fun f ↦ reductionDerivedChange X f)
      (reductionCoefficientMap_comp X d c b a hab hbc))

/-- All finite normalization data and laws, fixed on actual sheaf tensor complexes.
The ordinary formulas use scalar-first tensors, as does the recorded coefficient datum.
Source: Stacks 03EL, 0D6D and 0G7E; blueprint completed-pullback-reduction, paragraph 1
(blueprint: lem-weil-pbc-pulled-reduction-normalization-comparison). -/
structure Comparison where
  /-- Compatibility of the specified finite coefficient identifications. -/
  quotientCompatibility : QuotientCompatibility d g
  /-- The recorded coherent normalization specialized to the actual scalar functors. -/
  scalarNormalization : ScalarNormalization X
  /-- The finite coefficient isomorphisms of the specified strict comparison. -/
  tau : ∀ n : ℕ, N d g n ≅ H d g n
  /-- Its ordinary balanced section map, before derived localization. -/
  ordinaryTau : ∀ n : ℕ, ordinaryN d g n ≅ ordinaryH d g n
  /-- Normalization of tau on inverse-image generators, including target coefficients. -/
  ordinaryTau_formula : ∀ (n : ℕ) (M : reductionModules Y (d.completedRing Y))
    (U : Y.ProEtᵒᵖ) (x : M.val.obj U)
    (r : (exchangeConstantRing X A).obj.obj ((proEtaleBaseChange g).op.obj U))
    (s : (d.finiteRing X n).obj.obj ((proEtaleBaseChange g).op.obj U)),
    ((ordinaryTau n).hom.app M).val.app ((proEtaleBaseChange g).op.obj U)
      (reductionTensorSection X (OrderedExchange.quotient d X n)
        ((PulledReduction.ordinarySource d g).obj M) ((proEtaleBaseChange g).op.obj U) s
        (r • constantGenerator d g M U x)) =
      (((OrderedExchange.quotient d X n).hom.app
        ((proEtaleBaseChange g).op.obj U) r) * s) • finiteGenerator d g n M U x
  /-- Both universal counits compute every flat-term K-flat completed representative. -/
  computed : ∀ (n : ℕ) (P : CochainComplex (reductionModules Y (d.completedRing Y)) ℤ),
    @CochainComplex.IsKFlatIndependentCoefficients.{t + 1, t, t + 1}
      Y.ProEt inferInstance (essentiallySmallSelf.{0} Y.ProEt) (ProEt.topology Y)
      (d.completedRing Y) P →
    (∀ i : ℤ, @SheafOfModules.IsFlatOnSite.{t + 1, t, t + 1, t + 1}
      Y.ProEt inferInstance (ProEt.topology Y) inferInstance
      (WeilConjectures.integralCoefficientAbLocallyBijective.{t, t} Y)
      (WeilConjectures.integralCoefficientAbSheafify.{t, t} Y).isRightAdjoint
      (d.completedRing Y) (P.X i)) →
    IsIso (nCounit d g n P) ∧ IsIso (hCounit d g n P)
  /-- The finite derived map is the localization of this particular ordinary map. -/
  tau_representative :
    ∀ (n : ℕ) (P : CochainComplex (reductionModules Y (d.completedRing Y)) ℤ),
    @CochainComplex.IsKFlatIndependentCoefficients.{t + 1, t, t + 1}
      Y.ProEt inferInstance (essentiallySmallSelf.{0} Y.ProEt) (ProEt.topology Y)
      (d.completedRing Y) P →
    (∀ i : ℤ, @SheafOfModules.IsFlatOnSite.{t + 1, t, t + 1, t + 1}
      Y.ProEt inferInstance (ProEt.topology Y) inferInstance
      (WeilConjectures.integralCoefficientAbLocallyBijective.{t, t} Y)
      (WeilConjectures.integralCoefficientAbSheafify.{t, t} Y).isRightAdjoint
      (d.completedRing Y) (P.X i)) →
    (tau n).hom.app (DerivedCategory.Q.obj P) ≫ hCounit d g n P =
      nCounit d g n P ≫
        DerivedCategory.Q.map ((NatIso.mapHomologicalComplex (ordinaryTau n) (.up ℤ)).hom.app P)
  /-- Invertibility in the quotient-coefficient category. -/
  thetaH_isIso : ∀ (b a : ℕ) (h : a ≤ b), IsIso (thetaH d g quotientCompatibility b a h)
  /-- The square thetaH (tau_b tensor 1) = tau_a thetaN, naturally in K. -/
  square : ∀ (b a : ℕ) (h : a ≤ b) (K : d.derived Y),
    (reductionDerivedChange X (reductionCoefficientMap X d b a h)).map ((tau b).hom.app K) ≫
        (thetaH d g quotientCompatibility b a h).app K =
      (thetaN d g scalarNormalization b a h).hom.app K ≫ (tau a).hom.app K
  /-- The triple-normalization equality under canonical derived scalar associativity. -/
  associative : ∀ (c b a : ℕ) (hab : a ≤ b) (hbc : b ≤ c) (K : d.derived Y),
    (reductionDerivedChange X (reductionCoefficientMap X d b a hab)).map
        ((thetaH d g quotientCompatibility c b hbc).app K) ≫
        (thetaH d g quotientCompatibility b a hab).app K =
      (quotientAssociator d scalarNormalization c b a hab hbc).hom.app ((H d g c).obj K) ≫
        (thetaH d g quotientCompatibility c a (hab.trans hbc)).app K
  /-- Ordinary theta, a natural map of the actual pulled module tensor functors. -/
  ordinaryTheta : ∀ (b a : ℕ) (h : a ≤ b),
    ordinaryH d g b ⋙ reductionChange X (reductionCoefficientMap X d b a h) ≅
      ordinaryH d g a
  /-- Its balancing formula after inverse image and scalar extension. -/
  ordinaryTheta_formula : ∀ (b a : ℕ) (h : a ≤ b)
    (M : reductionModules Y (d.completedRing Y)) (U : Y.ProEtᵒᵖ) (x : M.val.obj U)
    (s : (d.finiteRing X b).obj.obj ((proEtaleBaseChange g).op.obj U))
    (v : (d.finiteRing X a).obj.obj ((proEtaleBaseChange g).op.obj U)),
    ((ordinaryTheta b a h).hom.app M).val.app ((proEtaleBaseChange g).op.obj U)
      (reductionTensorSection X (reductionCoefficientMap X d b a h)
        ((ordinaryH d g b).obj M) ((proEtaleBaseChange g).op.obj U) v
        (s • finiteGenerator d g b M U x)) =
      (((reductionCoefficientMap X d b a h).hom.app ((proEtaleBaseChange g).op.obj U) s) * v) •
        finiteGenerator d g a M U x
  /-- Both triple composites before localization have the same balanced value.
  Naturality of scalar extension and the two ordinary normalization maps give the
  first route; quotient associativity gives the second route. -/
  ordinaryTriple_formula : ∀ (c b a : ℕ) (hab : a ≤ b) (hbc : b ≤ c)
    (M : reductionModules Y (d.completedRing Y)) (U : Y.ProEtᵒᵖ) (x : M.val.obj U)
    (t : (d.finiteRing X c).obj.obj ((proEtaleBaseChange g).op.obj U))
    (s : (d.finiteRing X b).obj.obj ((proEtaleBaseChange g).op.obj U))
    (v : (d.finiteRing X a).obj.obj ((proEtaleBaseChange g).op.obj U)),
    ((reductionChange X (reductionCoefficientMap X d b a hab)).map
      ((ordinaryTheta c b hbc).hom.app M) ≫ (ordinaryTheta b a hab).hom.app M).val.app
        ((proEtaleBaseChange g).op.obj U)
      (reductionTensorSection X (reductionCoefficientMap X d b a hab)
        ((reductionChange X (reductionCoefficientMap X d c b hbc)).obj
          ((ordinaryH d g c).obj M)) ((proEtaleBaseChange g).op.obj U) v
        (reductionTensorSection X (reductionCoefficientMap X d c b hbc)
          ((ordinaryH d g c).obj M) ((proEtaleBaseChange g).op.obj U) s
          (t • finiteGenerator d g c M U x))) =
      ((((reductionCoefficientMap X d c a (hab.trans hbc)).hom.app
          ((proEtaleBaseChange g).op.obj U) t) *
        ((reductionCoefficientMap X d b a hab).hom.app
          ((proEtaleBaseChange g).op.obj U) s)) * v) • finiteGenerator d g a M U x ∧
    ((ordinaryTheta c a (hab.trans hbc)).hom.app M).val.app
      ((proEtaleBaseChange g).op.obj U)
      (reductionTensorSection X (reductionCoefficientMap X d c a (hab.trans hbc))
        ((ordinaryH d g c).obj M) ((proEtaleBaseChange g).op.obj U)
        (((reductionCoefficientMap X d b a hab).hom.app
          ((proEtaleBaseChange g).op.obj U) s) * v)
        (t • finiteGenerator d g c M U x)) =
      ((((reductionCoefficientMap X d c a (hab.trans hbc)).hom.app
          ((proEtaleBaseChange g).op.obj U) t) *
        ((reductionCoefficientMap X d b a hab).hom.app
          ((proEtaleBaseChange g).op.obj U) s)) * v) • finiteGenerator d g a M U x
  /-- The specified thetaH is precisely the map induced on flat-term K-flat complexes. -/
  theta_representative : ∀ (b a : ℕ) (h : a ≤ b)
    (P : CochainComplex (reductionModules Y (d.completedRing Y)) ℤ),
    @CochainComplex.IsKFlatIndependentCoefficients.{t + 1, t, t + 1}
      Y.ProEt inferInstance (essentiallySmallSelf.{0} Y.ProEt) (ProEt.topology Y)
      (d.completedRing Y) P →
    (∀ i : ℤ, @SheafOfModules.IsFlatOnSite.{t + 1, t, t + 1, t + 1}
      Y.ProEt inferInstance (ProEt.topology Y) inferInstance
      (WeilConjectures.integralCoefficientAbLocallyBijective.{t, t} Y)
      (WeilConjectures.integralCoefficientAbSheafify.{t, t} Y).isRightAdjoint
      (d.completedRing Y) (P.X i)) →
    (thetaH d g quotientCompatibility b a h).app (DerivedCategory.Q.obj P) ≫
        hCounit d g a P =
      (reductionDerivedChange X (reductionCoefficientMap X d b a h)).map (hCounit d g b P) ≫
        reductionScalarComplexCounit X (reductionCoefficientMap X d b a h)
          (((ordinaryH d g b).mapHomologicalComplex (.up ℤ)).obj P) ≫
        DerivedCategory.Q.map
          ((NatIso.mapHomologicalComplex (ordinaryTheta b a h) (.up ℤ)).hom.app P)
  /-- Ordinary extension along the equal-index quotient, normalized as multiplication. -/
  ordinaryUnit : ∀ a : ℕ,
    reductionChange X (reductionCoefficientMap X d a a (le_refl a)) ≅
      𝟭 (reductionModules X (d.finiteRing X a))
  /-- The unit identification on every local tensor, not an unspecified automorphism. -/
  ordinaryUnit_formula : ∀ (a : ℕ) (M : reductionModules X (d.finiteRing X a))
    (U : X.ProEtᵒᵖ) (s : (d.finiteRing X a).obj.obj U) (x : M.val.obj U),
    ((ordinaryUnit a).hom.app M).val.app U
      (reductionTensorSection X (reductionCoefficientMap X d a a (le_refl a)) M U s x) =
        s • x
  /-- The unit is its exact derived localization through the universal scalar counit. -/
  derivedUnit : ∀ a : ℕ,
    reductionDerivedChange X (reductionCoefficientMap X d a a (le_refl a)) ≅
      𝟭 (reductionDerivedCategory X (d.finiteRing X a))
  /-- Its representative computation fixes the derived scalar unit uniquely. -/
  unit_representative : ∀ (a : ℕ)
    (P : CochainComplex (reductionModules X (d.finiteRing X a)) ℤ),
    @CochainComplex.IsKFlatIndependentCoefficients.{t + 1, t, t + 1}
      X.ProEt inferInstance (essentiallySmallSelf.{0} X.ProEt) (ProEt.topology X)
      (d.finiteRing X a) P →
    (∀ i : ℤ, @SheafOfModules.IsFlatOnSite.{t + 1, t, t + 1, t + 1}
      X.ProEt inferInstance (ProEt.topology X) inferInstance
      (WeilConjectures.integralCoefficientAbLocallyBijective.{t, t} X)
      (WeilConjectures.integralCoefficientAbSheafify.{t, t} X).isRightAdjoint
      (d.finiteRing X a) (P.X i)) →
    (derivedUnit a).hom.app (DerivedCategory.Q.obj P) =
      reductionScalarComplexCounit X (reductionCoefficientMap X d a a (le_refl a)) P ≫
        DerivedCategory.Q.map
          ((NatIso.mapHomologicalComplex (ordinaryUnit a) (.up ℤ)).hom.app P)
  /-- Equal-index thetaH is the scalar-extension unit identification. -/
  unit : ∀ (a : ℕ) (K : d.derived Y),
    (thetaH d g quotientCompatibility a a (le_refl a)).app K =
      (derivedUnit a).hom.app ((H d g a).obj K)

/-- Successive pulled quotient normalization, with its finite square, cocycle, unit
and sectionwise K-flat computation, for arbitrary K in the ambient derived category.

Source: Stacks Project, Tags 07A4, 0D6D, 0G7E, 06YS and 06YY; current blueprint,
completed-pullback-reduction, paragraph 1
(blueprint: lem-weil-pbc-pulled-reduction-normalization-comparison).

Proof: (1) Choose a flat-term K-flat completed-coefficient representative P by
lem-pc-kflat-resolution. By lem-weil-pbc-constant-completion-equivalence its restriction
is K-flat with flat terms over the constant ring, without any completeness hypothesis.
(2) Pullback and scalar extension preserve this class by
lem-weil-pbc-ringed-pullback-preserves-kflat. Compute all reductions on these complexes
using lem-pur-derived-change-of-rings and lem-weil-pbc-ringed-topoi-derived-pullback.
(3) The specified strict comparison of
lem-weil-pbc-pulled-reduction-strict-tower-comparison sends ([x] tensor r) tensor s to
[x tensor 1] times r-bar times s, by lem-weil-pbc-flat-coefficient-reduction-adjunct and
lem-sfb-kflat-scalar-comparison-normalization. Sheaf tensor generators determine it.
(4) The inverse scalar/pullback mate followed by pulled completed normalization gives
thetaH; its ordinary formula is ([x tensor 1]t) tensor s mapped to
[x tensor 1]q(t)s, with inverse h s mapped to h tensor s. ThetaN is the normalization of
lem-sfb-successive-derived-quotient-normalization.
(5) On generators the square is q(r-bar t)s = r-bar q(t)s, by the quotient ring map
identity. (6) Both triple composites are x tensor q_ca(t)q_ba(s)v by the quotient
cocycle and scalar associativity. Equal indices give multiplication h tensor s to hs,
with inverse h mapped to h tensor 1. The same balancing computation before inverse image
is the existing reductionBalance formula. All maps commute with restrictions and
differentials of def-pc-tensor-complex-sheaves.
(7) Chain maps change only x, proving naturality. Derived scalar and pullback computation
counits and lem-weil-pbc-site-derived-tensor-descent descend the maps, inverses and all
equalities through resolving quasi-isomorphisms. Thus the result holds on all derived
objects and is independent of the chosen flat-term K-flat representative. -/
theorem pulled_reduction_normalization_comparison : Nonempty (Comparison d g) := by
  sorry

end AlgebraicGeometry.Scheme.PulledNormalization
