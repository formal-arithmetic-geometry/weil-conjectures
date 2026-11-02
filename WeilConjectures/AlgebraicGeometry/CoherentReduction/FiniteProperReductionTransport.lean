/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.CoherentReduction.FiniteTowerTransport
public import WeilConjectures.AlgebraicGeometry.QuotientChange.InternalScalarNormalizationExistence
public import WeilConjectures.AlgebraicGeometry.QuotientChange.InternalPullNormalizationExistence
public import WeilConjectures.AlgebraicGeometry.ModuleRingedComparison.SectionDerivedRealization
public import WeilConjectures.AlgebraicGeometry.QuotientChange.CanonicalCoefficientTensorNormalization
public import WeilConjectures.CategoryTheory.Sites.SheafComposeForgetModule

/-! # Proper scalar reduction with fixed finite presentations
Source: Zheng 4.1; the proper projection comparison in step 7 of
lem-sfb-finite-proper-exceptional-coherent-tower.
-/
@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open WeilConjectures WeilConjectures.SemilinearSections
namespace AlgebraicGeometry.ProEtale.CoherentReduction
attribute [local instance] proEtSmall sequenceSmall
variable (l : ℕ) [Fact l.Prime] (E : Type (u + 1)) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The coefficient-sized section localization, transported through the exact section
presentation. This supplies the family required by the published normalizations.
Source: Stacks 00YV, 079D
(blueprint: def-sfb-proper-integral-reduction-comparison). -/
local instance sectionSmallDerived (A : Type (u + 1)) [CommRing A]
    [TopologicalSpace A] [IsTopologicalRing A] :
    ∀ X : Scheme.{u}, HasDerivedCategory.{u + 1}
      (ModuleRingedComparison.modules (abelianPoint A) X) := fun X ↦ by
  letI : IsGrothendieckAbelian.{u + 1}
      (ModuleRingedComparison.modules (abelianPoint A) X) :=
    IsGrothendieckAbelian.of_equivalence
      (ModuleRingedComparison.equivalence (abelianPoint A) X)
  exact HasDerivedCategory.ofIsGrothendieckAbelian _

/-- The original quotient homomorphism of condensed internal rings.
Source: Bhatt--Scholze 6.5.1 (blueprint: def-sfb-proper-integral-reduction-comparison). -/
def pointQuotient (n : ℕ) :
    abelianPoint (Padic.coefficientExtensionIntegers l E) ⟶
      abelianPoint (Etale.FiniteProperQuotient.Ring l E n) :=
  (sheafCompose _ (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
    ((sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
      (continuousPointMap (quotient l E n) (quotient_continuous l E n)))

/-- The quotient preserves the original ring operations.
Source: Stacks 00YV (blueprint: def-sfb-proper-integral-reduction-comparison). -/
instance pointQuotient_monoidal (n : ℕ) : IsMonHom (pointQuotient l E n) := by
  unfold pointQuotient
  infer_instance

/-- Exact finite internal-to-fixed presentation, retaining every additive section.
Source: Stacks 00YV, 03DA
(blueprint: def-sfb-proper-integral-reduction-comparison). -/
def finiteInternalPresentationOrd (X : Scheme.{u}) (n : ℕ) :=
  (ModuleRingedComparison.equivalence
    (abelianPoint (Etale.FiniteProperQuotient.Ring l E n)) X).functor ⋙
      finiteUnrealization X (Etale.FiniteProperQuotient.Ring l E n)

/-- Addition is unchanged by this presentation.
Source: Stacks 00YV (blueprint: def-sfb-proper-integral-reduction-comparison). -/
instance finiteInternalPresentationOrd_additive (X : Scheme.{u}) (n : ℕ) :
    (finiteInternalPresentationOrd l E X n).Additive := by
  unfold finiteInternalPresentationOrd
  infer_instance

/-- The section and constant-ring presentations are equivalences.
Source: Stacks 00YV, 03DA
(blueprint: def-sfb-proper-integral-reduction-comparison). -/
instance finiteInternalPresentationOrd_equivalence (X : Scheme.{u}) (n : ℕ) :
    (finiteInternalPresentationOrd l E X n).IsEquivalence := by
  unfold finiteInternalPresentationOrd
  infer_instance

/-- Exactness of the finite presentation.
Source: Stacks 00YV (blueprint: def-sfb-proper-integral-reduction-comparison). -/
instance finiteInternalPresentationOrd_limits (X : Scheme.{u}) (n : ℕ) :
    PreservesFiniteLimits (finiteInternalPresentationOrd l E X n) := inferInstance

/-- Exactness of the finite presentation.
Source: Stacks 00YV (blueprint: def-sfb-proper-integral-reduction-comparison). -/
instance finiteInternalPresentationOrd_colimits (X : Scheme.{u}) (n : ℕ) :
    PreservesFiniteColimits (finiteInternalPresentationOrd l E X n) := inferInstance

/-- Localization of that exact presentation.
Source: Stacks 05RU (blueprint: def-sfb-proper-integral-reduction-comparison). -/
def finiteInternalPresentation (X : Scheme.{u}) (n : ℕ) :
    DerivedCategory.{u + 1} (QuotientChange.Modules
      (abelianPoint (Etale.FiniteProperQuotient.Ring l E n)) X) ⥤
    DerivedCategory.{u + 1} (Sheaf (Scheme.ProEt.topology X)
      (ModuleCat.{u + 1} (Etale.FiniteProperQuotient.Ring l E n))) :=
  (finiteInternalPresentationOrd l E X n).mapDerivedCategory.{u + 1, u + 1}

set_option maxHeartbeats 1600000 in
-- The explicit source and target scalar actions expand large section presentations.
/-- Scalar compatibility of the identity on the underlying pushed-forward sections.
Source: Stacks 03D7; Bhatt--Scholze finite coefficient comparison
(blueprint: def-sfb-proper-integral-reduction-comparison).
Proof: a constant a acts on p_*M by p_* of its action on M. This is the
unit-normalized coefficient square upperStarFromPointComp. finiteConstantIso
identifies precisely those constant sections, including a=0 and the empty site. -/
theorem finiteInternalPush_smul {Z Y : Scheme.{u}} (p : Z ⟶ Y) (n : ℕ)
    (M : QuotientChange.Modules
      (abelianPoint (Etale.FiniteProperQuotient.Ring l E n)) Z)
    (U : Y.ProEtᵒᵖ) (a : Etale.FiniteProperQuotient.Ring l E n)
    (x : ((finiteInternalPresentationOrd l E Y n).obj
      ((CondensedRing.lowerStar
        (abelianPoint (Etale.FiniteProperQuotient.Ring l E n)) p).obj M)).obj.obj U) :
    let S := ((finiteInternalPresentationOrd l E Y n).obj
      ((CondensedRing.lowerStar
        (abelianPoint (Etale.FiniteProperQuotient.Ring l E n)) p).obj M)).obj.obj U
    let T := ((ProEtale.lowerStar
      (ModuleCat.{u + 1} (Etale.FiniteProperQuotient.Ring l E n)) p).obj
        ((finiteInternalPresentationOrd l E Z n).obj M)).obj.obj U
    @SMul.smul (Etale.FiniteProperQuotient.Ring l E n) S S.isModule.toSMul a x =
      @SMul.smul (Etale.FiniteProperQuotient.Ring l E n) T T.isModule.toSMul a x := by
  sorry

set_option maxHeartbeats 1600000 in
-- Elaboration checks the underlying section identities through both presentations.
/-- The ordinary push comparison is the identity of underlying abelian sheaves;
its linearity is the coefficient-unit square, not an independently chosen map.
Source: Stacks 03D7
(blueprint: def-sfb-proper-integral-reduction-comparison). -/
def finiteInternalPushOrd {Z Y : Scheme.{u}} (p : Z ⟶ Y) (n : ℕ) :
    CondensedRing.lowerStar (abelianPoint (Etale.FiniteProperQuotient.Ring l E n)) p ⋙
      finiteInternalPresentationOrd l E Y n ≅
    finiteInternalPresentationOrd l E Z n ⋙
      ProEtale.lowerStar (ModuleCat.{u + 1} (Etale.FiniteProperQuotient.Ring l E n)) p :=
  Sheaf.natIsoMkOfSheafCompose
    (F₁ := CondensedRing.lowerStar (abelianPoint (Etale.FiniteProperQuotient.Ring l E n)) p ⋙
      finiteInternalPresentationOrd l E Y n)
    (F₂ := finiteInternalPresentationOrd l E Z n ⋙
      ProEtale.lowerStar (ModuleCat.{u + 1} (Etale.FiniteProperQuotient.Ring l E n)) p)
    (fun _ ↦ Iso.refl _)
    (fun M U a x ↦ by
      dsimp
      exact finiteInternalPush_smul l E p n M U a x)
    (fun _ ↦ by ext U x; rfl)

/-- The derived comparison, obtained by deriving that identity on sections.
Source: Stacks 0D6E (blueprint: def-sfb-proper-integral-reduction-comparison). -/
def finiteInternalPush {Z Y : Scheme.{u}} (p : Z ⟶ Y) (n : ℕ) :
    QuotientChange.F (abelianPoint (Etale.FiniteProperQuotient.Ring l E n)) p ⋙
      finiteInternalPresentation l E Y n ≅
    finiteInternalPresentation l E Z n ⋙
      (ProEtale.lowerStar
        (ModuleCat.{u + 1} (Etale.FiniteProperQuotient.Ring l E n)) p).rightDerivedFunctor := by
  unfold QuotientChange.F CondensedRing.moduleObjectDerivedPushforward
  exact (Functor.rightDerivedFunctorCompMapDerivedCategoryIso _ _).symm ≪≫
    Functor.rightDerivedFunctorNatIso (finiteInternalPushOrd l E p n) ≪≫
    Functor.rightDerivedFunctorCompIso _ _ ≪≫
    Functor.isoWhiskerRight (Functor.rightDerivedFunctorIsoMapDerivedCategory _) _

/-- The true evaluation of a constant system is the original functor.
Source: Zheng 4.1 (blueprint: def-sfb-proper-integral-reduction-comparison).
Proof: apply Functor.ext to the object and map clauses of
constantSystem_existsUnique. The horizontal clause is not needed for this
identity, but is needed for the scalar system reduction used next. -/
theorem constantEvaluation_eq (X : Scheme.{u}) (n : ℕ) :
    constantSystem.{u + 1, u, u + 1} (Scheme.ProEt.topology X)
      (sectionRing X (Padic.coefficientExtensionIntegers l E)) ⋙
      evaluation.{u + 1, u, u + 1} (Scheme.ProEt.topology X)
        (constantCoefficients.{u + 1, u, u + 1} (Scheme.ProEt.topology X)
          (sectionRing X (Padic.coefficientExtensionIntegers l E)))
        (constantCoefficientTransitions.{u + 1, u, u + 1} (Scheme.ProEt.topology X)
          (sectionRing X (Padic.coefficientExtensionIntegers l E))) n = 𝟭 _ := by
  sorry

/-- The normalized section scalar comparison from the proved section-scalar theorem.
Its ordinary balanced-generator and derived counit laws determine it.
Source: Stacks 07A6 (blueprint: def-sfb-proper-integral-reduction-comparison). -/
def sectionScalarData (X : Scheme.{u}) (n : ℕ) :=
  (QuotientChange.internal_section_scalar_normalization_exists
    (pointQuotient l E n) X).choose

set_option maxHeartbeats 1600000 in
-- The adjunction conjugation contains both sizes of the section localization.
/-- Scalar extension commutes with the exact section presentation. This is the
left-adjoint conjugate of the localized, identity-on-sections restriction comparison.
The two section localizations here have the larger universe used by system evaluation.
Source: Stacks 07A6 (blueprint: def-sfb-proper-integral-reduction-comparison). -/
def scalarSectionComparison (X : Scheme.{u}) (n : ℕ) :
  letI : HasDerivedCategory.{u + 2}
      (WeilConjectures.SemilinearSections.Mod.{u + 1, u, u + 1} (Scheme.ProEt.topology X)
        (sectionRing X (Padic.coefficientExtensionIntegers l E))) :=
    HasDerivedCategory.standard _;
  letI : HasDerivedCategory.{u + 2}
      (WeilConjectures.SemilinearSections.Mod.{u + 1, u, u + 1}
        (Scheme.ProEt.topology X) (coefficients l E X n)) :=
    HasDerivedCategory.standard _;
  QuotientChange.D (pointQuotient l E n) X ⋙
      (ModuleRingedComparison.equivalence
        (abelianPoint (Etale.FiniteProperQuotient.Ring l E n)) X).functor.mapDerivedCategory.{
        u + 1, u + 2} ≅
  (integralSections l E X).mapDerivedCategory.{u + 1, u + 2} ⋙
      ((reductionScalar l E X).levels n).T := by
  letI : HasDerivedCategory.{u + 2}
      (WeilConjectures.SemilinearSections.Mod.{u + 1, u, u + 1} (Scheme.ProEt.topology X)
        (sectionRing X (Padic.coefficientExtensionIntegers l E))) :=
    HasDerivedCategory.standard _
  letI : HasDerivedCategory.{u + 2}
      (WeilConjectures.SemilinearSections.Mod.{u + 1, u, u + 1}
        (Scheme.ProEt.topology X) (coefficients l E X n)) :=
    HasDerivedCategory.standard _
  let s := sectionScalarData l E X n
  let EO : DerivedCategory (QuotientChange.Modules
      (abelianPoint (Padic.coefficientExtensionIntegers l E)) X) ≌
      D (Scheme.ProEt.topology X)
        (sectionRing X (Padic.coefficientExtensionIntegers l E)) :=
    (ModuleRingedComparison.equivalence
      (abelianPoint (Padic.coefficientExtensionIntegers l E)) X).mapDerivedCategory.{
        u + 2, u + 2, u + 1, u + 1, u + 1, u + 2}
  let EA : DerivedCategory (QuotientChange.Modules
      (abelianPoint (Etale.FiniteProperQuotient.Ring l E n)) X) ≌
      D (Scheme.ProEt.topology X) (coefficients l E X n) :=
    (ModuleRingedComparison.equivalence
      (abelianPoint (Etale.FiniteProperQuotient.Ring l E n)) X).mapDerivedCategory.{
        u + 2, u + 2, u + 1, u + 1, u + 1, u + 2}
  let r : QuotientChange.V (pointQuotient l E n) X ⋙ EO.functor ≅
      EA.functor ⋙ resD (coefficientMap l E X n) :=
    (Functor.mapDerivedCategoryCompIso.{u + 2, u + 2, u + 2, u + 1, u + 1, u + 1,
      u + 1, u + 1, u + 2} _ _).symm ≪≫
      Functor.mapDerivedCategoryNatIso.{u + 2, u + 2, u + 1, u + 1, u + 1, u + 2}
        s.restriction ≪≫
      Functor.mapDerivedCategoryCompIso.{u + 2, u + 2, u + 2, u + 1, u + 1, u + 1,
        u + 1, u + 2, u + 2} _ _
  exact ((conjugateIsoEquiv
    ((QuotientChange.scalarAdj (pointQuotient l E n) X).comp EA.toAdjunction)
    (EO.toAdjunction.comp ((reductionScalar l E X).levels n).adjunction)).symm
      (Iso.inverseCompIso (Iso.isoCompInverse r ≪≫ Functor.associator _ _ _))).symm

set_option maxHeartbeats 1600000 in
-- The diagonal and scalar-evaluation comparisons have large instantiated types.
/-- Evaluate the simultaneous reduction, remove the actual diagonal, and use the
scalar section comparison. All legs are derived functor comparisons or adjunction mates.
Source: Zheng 4.1; Stacks 07A6
(blueprint: def-sfb-proper-integral-reduction-comparison). -/
def reductionInternalComparison (X : Scheme.{u}) (n : ℕ) :
    reduction l E X ⋙ fixedDerivedEvaluation l E X n ≅
      QuotientChange.D (pointQuotient l E n) X ⋙ finiteInternalPresentation l E X n := by
  letI : HasDerivedCategory.{u + 2}
      (WeilConjectures.SemilinearSections.Mod.{u + 1, u, u + 1} (Scheme.ProEt.topology X)
        (sectionRing X (Padic.coefficientExtensionIntegers l E))) :=
    HasDerivedCategory.standard _
  letI : HasDerivedCategory.{u + 2}
      (WeilConjectures.SemilinearSections.Mod.{u + 1, u, u + 1}
        (Scheme.ProEt.topology X) (coefficients l E X n)) :=
    HasDerivedCategory.standard _
  let diag := (constantSystem.{u + 1, u, u + 1} (Scheme.ProEt.topology X)
    (sectionRing X (Padic.coefficientExtensionIntegers l E))).mapDerivedCategory.{u + 2, u + 2}
  let e₀ := (evaluation.{u + 1, u, u + 1} (Scheme.ProEt.topology X)
    (constantCoefficients.{u + 1, u, u + 1} (Scheme.ProEt.topology X)
      (sectionRing X (Padic.coefficientExtensionIntegers l E)))
    (constantCoefficientTransitions.{u + 1, u, u + 1} (Scheme.ProEt.topology X)
      (sectionRing X (Padic.coefficientExtensionIntegers l E))) n).mapDerivedCategory.{u + 2, u + 2}
  let T := ((reductionScalar l E X).levels n).T
  let U := (finiteUnrealization X
    (Etale.FiniteProperQuotient.Ring l E n)).mapDerivedCategory.{u + 2, u + 1}
  let c := Functor.mapDerivedCategoryNatIso.{u + 2, u + 2, u + 1, u + 1, u + 2, u + 2}
    (eqToIso (constantEvaluation_eq l E X n))
  let d : diag ⋙ e₀ ≅ 𝟭 (D (Scheme.ProEt.topology X)
      (sectionRing X (Padic.coefficientExtensionIntegers l E))) :=
    (Functor.mapDerivedCategoryCompIso.{u + 2, u + 2, u + 2, u + 1, u + 1, u + 1,
      u + 2, u + 2, u + 2} _ _).symm ≪≫ c ≪≫
      Functor.mapDerivedCategoryIdIso.{u + 2, u + 1, u + 2} _
  let ε := Functor.isoWhiskerLeft diag ((reductionScalar l E X).evaluation n) ≪≫
    (Functor.associator diag e₀ T).symm ≪≫ Functor.isoWhiskerRight d T ≪≫
    Functor.leftUnitor T
  exact Functor.isoWhiskerLeft (integralSections l E X).mapDerivedCategory.{u + 1, u + 2}
      (Functor.isoWhiskerRight ε U) ≪≫
    Functor.isoWhiskerRight (scalarSectionComparison l E X n).symm U ≪≫
    Functor.isoWhiskerLeft _
      (Functor.mapDerivedCategoryCompIso.{u + 2, u + 2, u + 2, u + 1, u + 1, u + 1,
        u + 1, u + 2, u + 1} _ _).symm

/-- The balancing map is the inverse of the specified scalar pullback mate.
It is selected from a proved normalization theorem, with its inverse fixed.
Source: Stacks 07A6 (blueprint: def-sfb-proper-integral-reduction-comparison). -/
def normalizedScalarPull {Z Y : Scheme.{u}} (p : Z ⟶ Y) (n : ℕ) :=
  (DiagonalCoefficients.scalar_pullback_mate_inverse_normalized
    (pointQuotient l E n) p).choose

/-- Proper scalar projection, as an actual geometric mate between the fixed reductions.
The middle leg is rho. Restricting it to integral coefficients gives precisely
moduleObjectProjectionMap followed by scalarCoefficientPull, by
internal_scalar_mate_projection. Thus the construction retains the projection map.
Source: proper integral projection theorem, step 7
(blueprint: def-sfb-proper-integral-reduction-comparison). -/
def properReduction {Z Y : Scheme.{u}} (p : Z ⟶ Y) (n : ℕ)
    (M : DerivedCategory (QuotientChange.Modules
      (abelianPoint (Padic.coefficientExtensionIntegers l E)) Z)) :
    (fixedDerivedEvaluation l E Y n).obj
      ((reduction l E Y).obj ((integralPush l E p).obj M)) ⟶
    ((ProEtale.lowerStar
      (ModuleCat.{u + 1} (Etale.FiniteProperQuotient.Ring l E n)) p).rightDerivedFunctor).obj
      ((fixedDerivedEvaluation l E Z n).obj ((reduction l E Z).obj M)) := by
  let ρ : (QuotientChange.D (pointQuotient l E n) Y).obj
        ((integralPush l E p).obj M) ⟶
      (QuotientChange.F (abelianPoint (Etale.FiniteProperQuotient.Ring l E n)) p).obj
        ((QuotientChange.D (pointQuotient l E n) Z).obj M) := by
    simpa only [integralPush, QuotientChange.F, CondensedRing.moduleObjectDerivedPushforward,
      Functor.comp_obj] using
      (QuotientChange.rho (pointQuotient l E n) p (normalizedScalarPull l E p n)).app M
  exact (reductionInternalComparison l E Y n).hom.app ((integralPush l E p).obj M) ≫
    (finiteInternalPresentation l E Y n).map ρ ≫
    (finiteInternalPush l E p n).hom.app
      ((QuotientChange.D (pointQuotient l E n) Z).obj M) ≫
    ((ProEtale.lowerStar
      (ModuleCat.{u + 1} (Etale.FiniteProperQuotient.Ring l E n)) p).rightDerivedFunctor).map
      ((reductionInternalComparison l E Z n).inv.app M)

/-- The integral projection map with the finite quotient as second factor.
Its body is moduleObjectProjectionMap followed by the cartesian coefficient map.
Source: det-thm-sfb-proper-base-change-integral(3)
(blueprint: def-sfb-proper-integral-reduction-comparison). -/
def properIntegralProjectionMap {Z Y : Scheme.{u}} (p : Z ⟶ Y) (n : ℕ)
    (M : DerivedCategory (QuotientChange.Modules
      (abelianPoint (Padic.coefficientExtensionIntegers l E)) Z)) :=
  QuotientChange.scalarProjection (pointQuotient l E n) p M

/-- Exact specialization of the published scalar-mate/projection proof certificate.
The scalar leg used by properReduction is the scalar-adjunction presentation
of the specified integral projection map. This is an equality involving that
leg, rather than an independent invertibility condition.
Source: Stacks 07A6, 0B56; node proof step 7
(blueprint: def-sfb-proper-integral-reduction-comparison).
Definition: specialize internal_scalar_mate_projection to the normalized inverse of
the published scalar pullback mate and the canonical coefficient tensor
normalizations. Its third clause is exactly the displayed identity. -/
abbrev properReduction_projection_equation {Z Y : Scheme.{u}} (p : Z ⟶ Y) (n : ℕ)
    (M : DerivedCategory (QuotientChange.Modules
      (abelianPoint (Padic.coefficientExtensionIntegers l E)) Z)) :
    let a := pointQuotient l E n
    let tZ := QuotientChange.canonicalCoefficientTensorNormalization a Z
    let tY := QuotientChange.canonicalCoefficientTensorNormalization a Y
    (QuotientChange.V a Y).map
        ((QuotientChange.rho a p (normalizedScalarPull l E p n)).app M) ≫
      (QuotientChange.scalarRestrictionPush a p).app ((QuotientChange.D a Z).obj M) ≫
      (QuotientChange.F (abelianPoint (Padic.coefficientExtensionIntegers l E)) p).map
        (tZ.derived.hom.app M) =
    tY.derived.hom.app
        ((QuotientChange.F (abelianPoint (Padic.coefficientExtensionIntegers l E)) p).obj M) ≫
      properIntegralProjectionMap l E p n M := by
  exact (QuotientChange.internal_scalar_mate_projection (pointQuotient l E n) p
    (QuotientChange.canonicalCoefficientTensorNormalization (pointQuotient l E n) Z)
    (QuotientChange.canonicalCoefficientTensorNormalization (pointQuotient l E n) Y)
    (normalizedScalarPull l E p n)
    ((QuotientChange.canonicalCoefficientTensorNormalization_normalized
      (pointQuotient l E n)).1 Z)
    ((QuotientChange.canonicalCoefficientTensorNormalization_normalized
      (pointQuotient l E n)).1 Y)
    (DiagonalCoefficients.scalar_pullback_mate_inverse_normalized
      (pointQuotient l E n) p).choose_spec.2).2.2.1 M

/-- Invertibility of that map on bounded constructible inputs for proper finite-type
maps over the given field. There is no unbounded projection-formula assertion here.
Source: det-thm-sfb-proper-base-change-integral(3)
(blueprint: def-sfb-proper-integral-reduction-comparison).
Proof: the normalized internal scalar-mate/projection equality reduces the middle
leg to the integral proper projection formula with coefficient A_n. This coefficient
is bounded constructible. The other three legs are the displayed presentation
isomorphisms. -/
theorem properReduction_isIso {Z Y : Scheme.{u}} (p : Z ⟶ Y) [IsProper p]
    (p₀ : ℕ) [Fact p₀.Prime] (k : Type u) [Field k] [CharP k p₀]
    (hl : l ≠ p₀) [Z.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (Z ↘ Spec (.of k))] [QuasiCompact (Z ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Z ↘ Spec (.of k))] [IsSeparated (Y ↘ Spec (.of k))]
    [p.IsOver (Spec (.of k))] (n : ℕ) (M : Bc l E Z) :
    IsIso (properReduction l E p n
      ((boundedConstructible (internalRing Z
        (Padic.coefficientExtensionIntegers l E))).ι.obj M)) := by
  sorry

end AlgebraicGeometry.ProEtale.CoherentReduction
