/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q150
-/
module

public import Sheaf.Paper.IntegralCompletedTowerPullbackUniverses
public import Sheaf.SixFunctors.IntegralOpenReductionComparison
public import Sheaf.Paper.ExactProductFunctorStrictLimit
public import Sheaf.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory
import all Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients
import all Sheaf.Paper.IntegralOperationsWellDefined

/-! # Open strict quotient comparison and actual completion units

Source: Stacks Project, proetale.tex, Tag 099N (2),(5), and sites-cohomology.tex,
Tags 0G7E and 07A4 (blueprint: def-sf-augmented-strict-integral-completion).
The index n denotes exponent n+1. Site and coefficient universes are independent.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option genInjectivity false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genCtorIdx false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe t u
open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.OpenQuotientCompletion
open CompletedTowerIndependent

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- Sheafification at the common site/coefficient size.
Source: Stacks 0941, 099N
(blueprint: def-sf-augmented-strict-integral-completion). -/
instance abSheafify (W : Scheme.{t}) :
    HasSheafify (ProEt.topology W) AddCommGrpCat.{max u (t+1)} :=
  integralCoefficientAbSheafify.{t, u} W
/-- The locally bijective criterion for this sheafification.
Source: Stacks 0941, 099N
(blueprint: def-sf-augmented-strict-integral-completion). -/
instance abLocallyBijective (W : Scheme.{t}) :
    (ProEt.topology W).WEqualsLocallyBijective AddCommGrpCat.{max u (t+1)} :=
  integralCoefficientAbLocallyBijective.{t, u} W

/-- The Grothendieck property for the recorded completed module category.
Source: Stacks 0941, 099N
(blueprint: def-sf-augmented-strict-integral-completion). -/
instance moduleGrothendieck (W : Scheme.{t}) :
    IsGrothendieckAbelian.{max u (t+1)} (Modules l E W) :=
  SheafOfModules.isGrothendieckAbelianOfUniverses.{t+1, t, max u (t+1), 0}
    (ProEt.topology W) (completedIntegralCoefficientSheafUnrestricted l E W)

/-- The Grothendieck property for strict countable diagrams.
Source: Stacks 0941, 099N
(blueprint: def-sf-augmented-strict-integral-completion). -/
instance towerGrothendieck (W : Scheme.{t}) :
    IsGrothendieckAbelian.{max u (t+1)} (Towers l E W) :=
  CategoryTheory.tower_grothendieck (Modules l E W)

/-- The ordinary constant strict-tower functor.
Source: Stacks 0941, 099N
(blueprint: def-sf-augmented-strict-integral-completion). -/
abbrev delta (W : Scheme.{t}) : Modules l E W ⥤ Towers l E W := Functor.const ℕᵒᵖ
/-- Additivity of the constant strict-tower functor.
Source: Stacks 0941, 099N
(blueprint: def-sf-augmented-strict-integral-completion). -/
instance deltaAdditive (W : Scheme.{t}) : (delta l E W).Additive where
  map_add := by intros; ext; rfl
/-- The exact constant functor on ordinary unbounded derived categories.
Source: Stacks 0941, 099N
(blueprint: def-sf-augmented-strict-integral-completion). -/
abbrev deltaD (W : Scheme.{t}) := (delta l E W).mapDerivedCategory
/-- Ordinary inverse limit of strict completed-module towers.
Source: Stacks 0941, 099N
(blueprint: def-sf-augmented-strict-integral-completion). -/
abbrev inverseLimit (W : Scheme.{t}) : Towers l E W ⥤ Modules l E W := lim
/-- Additivity of the ordinary inverse limit functor.
Source: Stacks 0941, 099N
(blueprint: def-sf-augmented-strict-integral-completion). -/
instance limitAdditive (W : Scheme.{t}) : (inverseLimit l E W).Additive :=
  Functor.additive_of_preserves_binary_products _
/-- Total right derived inverse limit in the ordinary tower category.
Source: Stacks 0941, 099N
(blueprint: def-sf-augmented-strict-integral-completion). -/
abbrev rlim (W : Scheme.{t}) := (inverseLimit l E W).rightDerivedFunctor

/-- The canonical derived constant-tower/inverse-limit adjunction.
Source: Stacks 0941, 099N
(blueprint: def-sf-augmented-strict-integral-completion). -/
def constantAdjunction (W : Scheme.{t}) : deltaD l E W ⊣ rlim l E W :=
  (constLimAdj : delta l E W ⊣ inverseLimit l E W).mapDerivedCategoryRightDerivedAdjunction

/-- Representative normalization of the derived strict augmentation. It uses one
strict map, whose degree/level components are the recorded quotient units.
Source: Stacks 06YY and 099N
(blueprint: def-sf-augmented-strict-integral-completion). -/
def AugmentationNormalized (T : Scheme.{t})
    (gamma : deltaD l E T ⟶ (reductionPair l E T).functor) : Prop :=
  ∀ P : CochainComplex (Modules l E T) ℤ, integralOperationsGoodComplex l E T P →
    ∃ a : ((delta l E T).mapHomologicalComplex (.up ℤ)).obj P ⟶
        (reductionComplex l E T).obj P,
      (∀ (i : ℤ) (n : ℕ), (a.f i).app (op n) =
        (unrestrictedTowerUnit l E T P n).f i) ∧
      gamma.app (DerivedCategory.Q.obj P) ≫ (reductionPair l E T).counit.app P =
        (delta l E T).mapDerivedCategoryFactors.hom.app P ≫ DerivedCategory.Q.map a

private theorem quotientUnit_step (T : Scheme.{t})
    (P : CochainComplex (Modules l E T) ℤ) (n : ℕ) :
    unrestrictedTowerUnit l E T P (n+1) ≫
        (unrestrictedIntegralTransition l E T n).app P =
      unrestrictedTowerUnit l E T P n := by
  ext i U x
  change (((unrestrictedIntegralTransition l E T n).app P).f i).val.app U
      ((((unrestrictedTowerUnit l E T P (n+1)).f i).val.app U) x) =
    (((unrestrictedTowerUnit l E T P n).f i).val.app U) x
  rw [unrestrictedTowerUnit_condition l E T P (n+1) i U x,
    unrestrictedTowerUnit_condition l E T P n i U x]
  change (((unrestrictedIntegralTransition l E T n).app P).f i).val.app U
      (unrestrictedIntegralTensorSection l E T (n+1) (P.X i) U 1 x) =
    unrestrictedIntegralTensorSection l E T n (P.X i) U 1 x
  simpa [unrestrictedIntegralTransition] using
    (unrestrictedIntegralTransition_existsUnique l E T n).exists.choose_spec P i U 1 x

private def strictQuotientUnit (T : Scheme.{t}) (P : CochainComplex (Modules l E T) ℤ) :
    ((delta l E T).mapHomologicalComplex (.up ℤ)).obj P ⟶
      (reductionComplex l E T).obj P where
  f i := NatTrans.ofOpSequence (fun n ↦ (unrestrictedTowerUnit l E T P n).f i)
    (fun n ↦ by
      change 𝟙 _ ≫ _ = _ ≫ _
      rw [Category.id_comp]
      change (unrestrictedTowerUnit l E T P n).f i =
        (unrestrictedTowerUnit l E T P (n+1)).f i ≫
          (((Functor.ofOpSequence (unrestrictedIntegralTransition l E T)).map
            (homOfLE (Nat.le_succ n)).op).app P).f i
      rw [Functor.ofOpSequence_map_homOfLE_succ]
      exact (congrArg (fun a ↦ a.f i) (quotientUnit_step l E T P n)).symm)
  comm' i j _ := by
    apply NatTrans.ext
    funext n
    exact (unrestrictedTowerUnit l E T P n.unop).comm i j

private def strictQuotientUnits (T : Scheme.{t}) :
    (delta l E T).mapHomologicalComplex (.up ℤ) ⟶ reductionComplex l E T where
  app := strictQuotientUnit l E T
  naturality {P Q} a := by
    apply HomologicalComplex.hom_ext
    intro i
    apply NatTrans.ext
    funext n
    change a.f i ≫ (unrestrictedTowerUnit l E T Q n.unop).f i =
      (unrestrictedTowerUnit l E T P n.unop).f i ≫ _
    change a.f i ≫ (scalarReductionExtension_adjunction l E T n.unop).choose.unit.app
        (Q.X i) =
      (scalarReductionExtension_adjunction l E T n.unop).choose.unit.app (P.X i) ≫
        (scalarReductionRestriction l E T n.unop).map
          ((scalarReductionExtension l E T n.unop).map (a.f i))
    exact (scalarReductionExtension_adjunction l E T n.unop).choose.unit.naturality
      (a.f i)

/-- The quotient augmentation descends uniquely with its computation normalization.
Source: Stacks 06YY, 06XN, 099N
(blueprint: def-sf-augmented-strict-integral-completion).
Proof: the scalar-extension units form a strict tower map because quotient maps preserve
one. They are natural in chain maps. Quasi-isomorphisms between flat-term K-flat complexes
are inverted by the whole strict reduction construction, levelwise by change of rings.
Localize the good representatives; their localization is equivalent to the entire derived
category by K-flat resolution. Full faithfulness of restriction along this localization
gives the unique natural transformation, characterized by the displayed counit equation. -/
theorem augmentation_existsUnique (T : Scheme.{t}) :
    ∃! gamma : deltaD l E T ⟶ (reductionPair l E T).functor,
      AugmentationNormalized l E T gamma := by
  let R := reductionPair l E T
  let w := HomologicalComplex.quasiIso (Modules l E T) (.up ℤ)
  have := R.universal
  let b : DerivedCategory.Q ⋙ deltaD l E T ⟶ reductionComplex l E T ⋙ DerivedCategory.Q :=
    (delta l E T).mapDerivedCategoryFactors.hom ≫
      whiskerRight (strictQuotientUnits l E T) DerivedCategory.Q
  let gamma := R.functor.leftDerivedLift R.counit w (deltaD l E T) b
  have hgamma (P : CochainComplex (Modules l E T) ℤ) :
      gamma.app (DerivedCategory.Q.obj P) ≫ R.counit.app P =
        (delta l E T).mapDerivedCategoryFactors.hom.app P ≫
          DerivedCategory.Q.map (strictQuotientUnit l E T P) :=
    R.functor.leftDerived_fac_app R.counit w (deltaD l E T) b P
  refine ⟨gamma, ?_, ?_⟩
  · intro P _
    exact ⟨strictQuotientUnit l E T P, fun _ _ ↦ rfl, hgamma P⟩
  · intro gamma' hgamma'
    let q := integralOperationsGoodLocalization l E T
    let wgood := w.inverseImage (integralOperationsGoodComplex l E T).ι
    have : q.IsLocalization wgood := integralOperationsGoodLocalization_isLocalization l E T
    apply Localization.natTrans_ext q wgood
    intro P
    have := R.computes P.obj P.property
    apply (cancel_mono (R.counit.app P.obj)).mp
    obtain ⟨a, ha, he⟩ := hgamma' P.obj P.property
    have hunit : a = strictQuotientUnit l E T P.obj := by
      apply HomologicalComplex.hom_ext
      intro i
      apply NatTrans.ext
      funext n
      exact ha i n.unop
    exact he.trans ((congrArg
      (fun a ↦ (delta l E T).mapDerivedCategoryFactors.hom.app P.obj ≫
        DerivedCategory.Q.map a) hunit).trans (hgamma P.obj).symm)

/-- The actual strict quotient augmentation, chosen only from its determining universal
normalization. Source: Stacks 099N
(blueprint: def-sf-augmented-strict-integral-completion). -/
def augmentation (T : Scheme.{t}) : deltaD l E T ⟶ (reductionPair l E T).functor :=
  (augmentation_existsUnique l E T).exists.choose

/-- The source's C_T is the composite of strict reduction and total right derived limit.
Source: Stacks 099N (blueprint: def-sf-augmented-strict-integral-completion). -/
abbrev completion (T : Scheme.{t}) := (reductionPair l E T).functor ⋙ rlim l E T

/-- The actual completion unit, obtained from the constant-tower unit and the strict
quotient augmentation. Source: Stacks 099N and 0941
(blueprint: def-sf-augmented-strict-integral-completion). -/
def unit (T : Scheme.{t}) (H : DerivedCategory (Modules l E T)) :
    H ⟶ (completion l E T).obj H :=
  (constantAdjunction l E T).unit.app H ≫
    (rlim l E T).map ((augmentation l E T).app H)

/-- Signed coordinates (x,y)=(u,-v) on the actual shifted cone. Their differential
is (dx,(1-s)x-dy). Source: Stacks 0941
(blueprint: def-sf-augmented-strict-integral-completion). -/
def signedCoordinates (T : Scheme.{t}) (N : CochainComplex (Towers l E T) ℤ) (p : ℤ) :
    (roosF.obj N).X (p+1) ⟶ (roosP N).X (p+1) ⊞ (roosP N).X p :=
  (roosχ N p).hom ≫ (biprod.braiding _ _).hom ≫ biprod.map (𝟙 _) (-𝟙 _)

/-- The universal right-derived comparison at complex representatives, using the
canonical quotient/homotopy-category identifications. Source: Stacks 0941
(blueprint: def-sf-augmented-strict-integral-completion). -/
def rlimUnitCx (T : Scheme.{t}) :
    (inverseLimit l E T).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ rlim l E T :=
  (isoWhiskerLeft _ (DerivedCategory.quotientCompQhIso (Modules l E T)).symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
    isoWhiskerRight ((inverseLimit l E T).mapHomotopyCategoryFactors (.up ℤ)).symm _ ≪≫
    Functor.associator _ _ _).hom ≫
  whiskerLeft (HomotopyCategory.quotient (Towers l E T) (.up ℤ))
    (inverseLimit l E T).rightDerivedFunctorUnit ≫
  (Functor.associator _ _ _).inv ≫
  (isoWhiskerRight (DerivedCategory.quotientCompQhIso (Towers l E T)) (rlim l E T)).hom

/-- The compatible-family inclusion into the Roos complex, starting with the degreewise
ordinary limit used by the derived functor unit. Source: Stacks 0941
(blueprint: def-sf-augmented-strict-integral-completion). -/
def ordinaryRoosMap (T : Scheme.{t}) (I : CochainComplex (Towers l E T) ℤ) :
    ((inverseLimit l E T).mapHomologicalComplex (.up ℤ)).obj I ⟶ roosF.obj I :=
  roosAugment
    (fun n : ℕ ↦ (NatTrans.mapHomologicalComplex (lim.π (op n)) (.up ℤ)).app I)
    (fun n ↦ by
      apply HomologicalComplex.hom_ext
      intro i
      exact limit.w (I.X i) (homOfLE (Nat.le_succ n)).op)

variable {V W : Scheme.{t}} (e : V ⟶ W) [IsOpenImmersion e]
  (o : IntegralOpenReduction.Operations l E e)

/-- The existing normalized ringed-slice restriction, with its actual module categories.
Source: Stacks 0941, 099N
(blueprint: def-sf-augmented-strict-integral-completion). -/
def restrict : Modules l E W ⥤ Modules l E V :=
  IntegralOpenReduction.restriction l E e o
/-- Additivity of ringed-slice restriction.
Source: Stacks 0941, 099N
(blueprint: def-sf-augmented-strict-integral-completion). -/
instance restrictAdditive : (restrict l E e o).Additive :=
  IntegralOpenReduction.restrictionAdditive l E e o
/-- Exact ringed-slice restriction preserves finite limits.
Source: Stacks 0941, 099N
(blueprint: def-sf-augmented-strict-integral-completion). -/
instance restrictLimits : PreservesFiniteLimits (restrict l E e o) :=
  letI := abSheafify.{t, u} W
  letI := abLocallyBijective.{t, u} W
  inferInstanceAs (PreservesFiniteLimits
    (SheafOfModules.localizedSystemRestriction.{t+1, t, max u (t+1)}
      (completedIntegralCommRingSheafUnrestricted l E W)
        (IntegralOpenReduction.openObject e) ⋙ o.integral.inverse))
/-- Exact ringed-slice restriction preserves finite colimits.
Source: Stacks 0941, 099N
(blueprint: def-sf-augmented-strict-integral-completion). -/
instance restrictColimits : PreservesFiniteColimits (restrict l E e o) :=
  letI := abSheafify.{t, u} W
  letI := abLocallyBijective.{t, u} W
  inferInstanceAs (PreservesFiniteColimits
    (SheafOfModules.localizedSystemRestriction.{t+1, t, max u (t+1)}
      (completedIntegralCommRingSheafUnrestricted l E W)
        (IntegralOpenReduction.openObject e) ⋙ o.integral.inverse))
/-- Degreewise exact ringed-slice restriction of unbounded complexes.
Source: Stacks 0941, 099N
(blueprint: def-sf-augmented-strict-integral-completion). -/
abbrev restrictCx : CochainComplex (Modules l E W) ℤ ⥤ CochainComplex (Modules l E V) ℤ :=
  (restrict l E e o).mapHomologicalComplex (.up ℤ)
/-- The localization of exact restriction on the ordinary unbounded derived category.
Source: Stacks 0941, 099N
(blueprint: def-sf-augmented-strict-integral-completion). -/
abbrev restrictD := (restrict l E e o).mapDerivedCategory
/-- Restriction of every object and arrow of one strict tower.
Source: Stacks 0941, 099N
(blueprint: def-sf-augmented-strict-integral-completion). -/
abbrev restrictTow : Towers l E W ⥤ Towers l E V :=
  (Functor.whiskeringRight ℕᵒᵖ _ _).obj (restrict l E e o)
/-- Additivity of restriction on strict towers.
Source: Stacks 0941, 099N
(blueprint: def-sf-augmented-strict-integral-completion). -/
instance restrictTowAdditive : (restrictTow l E e o).Additive :=
  inferInstanceAs (((Functor.whiskeringRight ℕᵒᵖ _ _).obj (restrict l E e o)).Additive)
/-- Finite limits are preserved levelwise by strict-tower restriction.
Source: Stacks 0941, 099N
(blueprint: def-sf-augmented-strict-integral-completion). -/
instance restrictTowLimits : PreservesFiniteLimits (restrictTow l E e o) :=
  letI := abSheafify.{t, u} W
  letI := abLocallyBijective.{t, u} W
  letI := abSheafify.{t, u} V
  letI := abLocallyBijective.{t, u} V
  ⟨fun _ _ _ ↦ inferInstanceAs
    (PreservesLimitsOfShape _ ((Functor.whiskeringRight ℕᵒᵖ _ _).obj (restrict l E e o)))⟩
/-- Finite colimits are preserved levelwise by strict-tower restriction.
Source: Stacks 0941, 099N
(blueprint: def-sf-augmented-strict-integral-completion). -/
instance restrictTowColimits : PreservesFiniteColimits (restrictTow l E e o) :=
  letI := abSheafify.{t, u} W
  letI := abLocallyBijective.{t, u} W
  letI := abSheafify.{t, u} V
  letI := abLocallyBijective.{t, u} V
  ⟨fun _ _ _ ↦ inferInstanceAs
    (PreservesColimitsOfShape _ ((Functor.whiskeringRight ℕᵒᵖ _ _).obj (restrict l E e o)))⟩
/-- Degreewise restriction of complexes of strict towers.
Source: Stacks 0941, 099N
(blueprint: def-sf-augmented-strict-integral-completion). -/
abbrev restrictTowCx := (restrictTow l E e o).mapHomologicalComplex (.up ℤ)
/-- Exact restriction on the derived category of strict towers.
Source: Stacks 0941, 099N
(blueprint: def-sf-augmented-strict-integral-completion). -/
abbrev restrictTowD := (restrictTow l E e o).mapDerivedCategory

/-- The literal identity comparison of constant strict diagrams under restriction.
Source: Stacks 0941 (blueprint: def-sf-augmented-strict-integral-completion). -/
def constantRestrictionOrdinary : delta l E W ⋙ restrictTow l E e o ≅
    restrict l E e o ⋙ delta l E V :=
  NatIso.ofComponents (fun _ ↦ NatIso.ofComponents (fun _ ↦ Iso.refl _)
    (fun _ ↦ by simp [delta, restrictTow]))
    (fun _ ↦ by ext n; simp [delta, restrictTow])

section ConstantComparison

/-- The derived constant-tower comparison induced by the literal identity on constant
strict diagrams. Source: Stacks 0941
(blueprint: def-sf-augmented-strict-integral-completion). -/
def constantRestriction : deltaD l E W ⋙ restrictTowD l E e o ≅
    restrictD l E e o ⋙ deltaD l E V :=
  letI := deltaAdditive l E V
  letI := restrictAdditive l E e o
  letI : PreservesFiniteLimits (delta l E W ⋙ restrictTow l E e o) :=
    ⟨fun _ _ _ ↦ inferInstance⟩
  letI : PreservesFiniteColimits (delta l E W ⋙ restrictTow l E e o) :=
    ⟨fun _ _ _ ↦ inferInstance⟩
  letI : PreservesFiniteLimits (restrict l E e o ⋙ delta l E V) :=
    ⟨fun _ _ _ ↦ inferInstance⟩
  letI : PreservesFiniteColimits (restrict l E e o ⋙ delta l E V) :=
    ⟨fun _ _ _ ↦ inferInstance⟩
  (Functor.mapDerivedCategoryCompIso (delta l E W) (restrictTow l E e o)).symm ≪≫
    Functor.mapDerivedCategoryNatIso (constantRestrictionOrdinary l E e o) ≪≫
      Functor.mapDerivedCategoryCompIso (restrict l E e o) (delta l E V)

end ConstantComparison

/-- The actual section of the restricted module, expressed through the coefficient/site
transport's counit. Source: Stacks 03DJ and 098K
(blueprint: def-sf-augmented-strict-integral-completion). -/
def restrictionSection (M : Modules l E W)
    (Z : Over (IntegralOpenReduction.openObject e)) (x : M.val.obj (op Z.left)) :
    ((restrict l E e o).obj M).val.obj (op ((IntegralOpenReduction.sliceSite e).obj Z)) :=
  (((eqToHom o.integralFunctor).app ((restrict l E e o).obj M)).val.app (op Z))
    ((o.integral.counitIso.inv.app
      ((SheafOfModules.localizedSystemRestriction.{t+1, t, max u (t+1)}
        (completedIntegralCommRingSheafUnrestricted l E W)
          (IntegralOpenReduction.openObject e)).obj M)).val.app (op Z) x)

/-- The augmented construction of completed pullback, after exact open localization.
It applies restriction to the entire strict quotient map before applying Rlim.
Source: Stacks 099N (2),(5)
(blueprint: def-sf-augmented-strict-integral-completion). -/
def alpha (H : DerivedCategory (Modules l E W)) :
    (restrictD l E e o).obj H ⟶ (rlim l E V).obj
      ((restrictTowD l E e o).obj ((reductionPair l E W).functor.obj H)) :=
  (constantAdjunction l E V).unit.app ((restrictD l E e o).obj H) ≫
    (rlim l E V).map ((constantRestriction l E e o).inv.app H ≫
      (restrictTowD l E e o).map ((augmentation l E W).app H))

/-- The distinguished graph into the chosen base change, formed from identity and
structure maps. Source: Stacks 00VC
(blueprint: def-sf-augmented-strict-integral-completion). -/
def sliceGraph (Z : Over (IntegralOpenReduction.openObject e)) :
    (IntegralOpenReduction.sliceSite e).obj Z ⟶ (Scheme.proEtaleBaseChange e).obj Z.left :=
  MorphismProperty.Over.homMk
    (pullback.lift (𝟙 _) Z.hom.left (by exact Z.hom.w.symm)) (by simp; rfl)

/-- All comparisons of the statement, retaining their strict tensor, localization,
Roos and augmentation normalizations. Source: Stacks 099N (2),(5), 0G7E, 07A4, 0941
(blueprint: def-sf-augmented-strict-integral-completion). -/
structure StrictComparison where
  /-- The coefficient identifications are isomorphisms, with constants and projections
  already fixed by Operations.toCoefficients. -/
  finiteIso : ∀ n : ℕ, IsIso (o.finiteMap n)
  completedIso : IsIso o.completedMap
  coefficientTransitions : ∀ n : ℕ, o.finiteMap (n+1) ≫
      ((IntegralOpenReduction.sliceSite e).sheafPushforwardContinuous
        CommRingCat.{max u (t+1)} ((ProEt.topology W).over
          (IntegralOpenReduction.openObject e)) (ProEt.topology V)).map
            (coefficientSequenceCommRingTransition l E V n) =
    ((ProEt.topology W).overPullback CommRingCat.{max u (t+1)}
      (IntegralOpenReduction.openObject e)).map
        (coefficientSequenceCommRingTransition l E W n) ≫ o.finiteMap n
  /-- Exact restriction takes good representatives to good representatives. -/
  good : ∀ P : CochainComplex (Modules l E W) ℤ, integralOperationsGoodComplex l E W P →
    integralOperationsGoodComplex l E V ((restrictCx l E e o).obj P)
  /-- One natural isomorphism of complexes of strict towers, before localization. -/
  strict : reductionComplex l E W ⋙ restrictTowCx l E e o ≅
    restrictCx l E e o ⋙ reductionComplex l E V
  /-- The balanced tensor normalization, tested on every local pure tensor. -/
  tensor : ∀ (P : CochainComplex (Modules l E W) ℤ) (n : ℕ) (i : ℤ)
      (Z : Over (IntegralOpenReduction.openObject e))
      (a : (integralCoefficientCommRingSheaf l E W n).obj.obj (op Z.left))
      (x : (P.X i).val.obj (op Z.left)),
    (((strict.hom.app P).f i).app (op n)).val.app
        (op ((IntegralOpenReduction.sliceSite e).obj Z))
        (restrictionSection l E e o ((unrestrictedTowerComplex l E W n P).X i) Z
          (unrestrictedTowerTensorSection l E W n (P.X i) (op Z.left) a x)) =
      unrestrictedTowerTensorSection l E V n ((restrict l E e o).obj (P.X i))
        (op ((IntegralOpenReduction.sliceSite e).obj Z))
        ((o.finiteMap n).hom.app (op Z) a) (restrictionSection l E e o (P.X i) Z x)
  /-- Every strict quotient transition commutes before localization. -/
  transitions : ∀ (P : CochainComplex (Modules l E W) ℤ) (n : ℕ) (i : ℤ),
    (((reductionComplex l E W ⋙ restrictTowCx l E e o).obj P).X i).map
        (homOfLE (Nat.le_succ n)).op ≫ ((strict.hom.app P).f i).app (op n) =
      ((strict.hom.app P).f i).app (op (n+1)) ≫
        (((restrictCx l E e o ⋙ reductionComplex l E V).obj P).X i).map
          (homOfLE (Nat.le_succ n)).op
  /-- The natural derived strict-tower isomorphism tau. -/
  tau : (reductionPair l E W).functor ⋙ restrictTowD l E e o ≅
    restrictD l E e o ⋙ (reductionPair l E V).functor
  /-- The computation comparisons pin tau on every good representative; naturality
  then supplies independence for every derived morphism and every representative. -/
  computes : ∀ P : CochainComplex (Modules l E W) ℤ, integralOperationsGoodComplex l E W P →
    tau.hom.app (DerivedCategory.Q.obj P) ≫
        (reductionPair l E V).functor.map
          ((restrict l E e o).mapDerivedCategoryFactors.hom.app P) ≫
        (reductionPair l E V).counit.app ((restrictCx l E e o).obj P) =
      (restrictTowD l E e o).map ((reductionPair l E W).counit.app P) ≫
        (restrictTow l E e o).mapDerivedCategoryFactors.hom.app
          ((reductionComplex l E W).obj P) ≫ DerivedCategory.Q.map (strict.hom.app P)
  augmented : ∀ H : DerivedCategory (Modules l E W),
    (restrictTowD l E e o).map ((augmentation l E W).app H) ≫ tau.hom.app H =
      (constantRestriction l E e o).hom.app H ≫
        (augmentation l E V).app ((restrictD l E e o).obj H)
end WeilConjectures.OpenQuotientCompletion
