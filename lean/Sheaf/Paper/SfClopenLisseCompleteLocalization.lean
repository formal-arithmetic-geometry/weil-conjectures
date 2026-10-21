/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q28
-/
module

public import Sheaf.Paper.ProEtaleLocallyConstantSheafOfUniverses
public import Sheaf.Paper.DerivedCompleteOnSlices
public import Sheaf.Paper.DerivedScalarExtensionRestrictionAdjunction
public import Sheaf.CategoryTheory.RingedDerivedRestrictionGeneral
public import Sheaf.AlgebraicGeometry.RingedProEtaleTorAmplitudeOfUniverses
public import Sheaf.Paper.IntegralReductionTowerCanonical
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.CategoryTheory.Preadditive.Projective.Basic
public import Sheaf.Paper.CompletedIntegralConstantMapOfUniverses
public import Sheaf.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Limits.HasLimits
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel
import Sheaf.Paper.IntegralReductionTowerWellDefinedUnrestricted
import Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients
import Sheaf.AlgebraicGeometry.ProEtaleClopenRingedModuleGluing
import Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
import Sheaf.AlgebraicGeometry.ProEtaleConstantModuleRestriction
import Sheaf.AlgebraicGeometry.Sites.ProEtaleFiniteCoproductEvaluation
import Sheaf.AlgebraicGeometry.ProEtaleWeaklyContractibleEvaluationExact
import Mathlib.CategoryTheory.Sites.LocallySurjective
import Mathlib.CategoryTheory.Yoneda
import Mathlib.AlgebraicGeometry.Limits

/-! # Simultaneous clopen trivialization and ordinary complete restriction

Source: Stacks Project, proetale.tex, Tags 09C3 and 098F; sites-cohomology.tex,
Tag 0946; derived.tex, Tag 08TC (blueprint: lem-sf-clopen-lisse-complete-localization).

The coefficient comparisons below are fixed by constant sections and the actual
inverse-limit projections. Restriction is sectionwise precomposition, descended
termwise to unbounded derived categories. Index n denotes the positive exponent n+1.

## Main declarations

- `SfClopenCoefficientRestriction`: the normalized coefficient and exact restriction data.
- `SfClopenCompleteRestriction`: canonical reduction, augmented tower and Tor compatibility.
- `sf_clopen_lisse_complete_localization`: existence of the common finite clopen partition.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe t u v w
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme
namespace WeilConjectures

/-- The site inclusion for an open subscheme, by composition of weakly etale maps.
Source: Stacks 00XZ and 09AE (blueprint: lem-sf-clopen-lisse-complete-localization). -/
abbrev sfClopenSiteInclusion {T : Scheme.{t}} (U : T.Opens) :
    U.toScheme.ProEt ⥤ T.ProEt :=
  MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale U.ι)

/-- The continuous site inclusion used for ordinary restriction.
Source: Stacks 09AE (blueprint: lem-sf-clopen-lisse-complete-localization). -/
instance sfClopenSiteInclusionContinuous {T : Scheme.{t}} (U : T.Opens) :
    (sfClopenSiteInclusion U).IsContinuous (Scheme.ProEt.topology U.toScheme)
      (Scheme.ProEt.topology T) :=
  Scheme.ProEt.isContinuous_overMap (inferInstance : WeaklyEtale U.ι)

/-- Restriction of a ring sheaf by precomposition, with unchanged section rings.
Source: Stacks 00Y0 (blueprint: lem-sf-clopen-lisse-complete-localization). -/
abbrev sfClopenRingRestriction {T : Scheme.{t}} (U : T.Opens)
    (R : Sheaf (Scheme.ProEt.topology T) RingCat.{v}) :=
  ((sfClopenSiteInclusion U).sheafPushforwardContinuous
    RingCat.{v} (Scheme.ProEt.topology U.toScheme) (Scheme.ProEt.topology T)).obj R

/-- Sectionwise restriction with scalars identified by the specified ring comparison.
Source: Stacks 03DH (blueprint: lem-sf-clopen-lisse-complete-localization). -/
abbrev sfClopenModuleRestriction {T : Scheme.{t}} (U : T.Opens)
    (R : Sheaf (Scheme.ProEt.topology T) RingCat.{v})
    (S : Sheaf (Scheme.ProEt.topology U.toScheme) RingCat.{v})
    (c : S ≅ sfClopenRingRestriction U R) : SheafOfModules.{v} R ⥤ SheafOfModules.{v} S :=
  SheafOfModules.pushforward (F := sfClopenSiteInclusion U) (𝟙 _) ⋙
    SheafOfModules.restrictScalars c.hom

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- Canonical coefficient identifications and exact ordinary restriction on a component.
The constant-section normalization fixes the finite comparisons; the projection squares
fix the completed comparison uniquely. Exactness is evidence, not extra hypotheses on T.
Source: Stacks 00Y0, 09C3, 015F (blueprint: lem-sf-clopen-lisse-complete-localization). -/
structure SfClopenCoefficientRestriction (T : Scheme.{t}) (U : T.Opens) where
  /-- Finite coefficients, oriented from local coefficients to restricted coefficients. -/
  finite : ∀ n : ℕ, integralCoefficientSheaf l E U.toScheme n ≅
    sfClopenRingRestriction U (integralCoefficientSheaf l E T n)
  /-- Constant sections are fixed, on every site object. -/
  finite_constant : ∀ (n : ℕ) (V : U.toScheme.ProEt)
      (x : ULift.{t + 1} (Padic.coefficientExtensionRing l E (n + 1))),
    (finite n).hom.hom.app (op V)
      ((toSheafify (Scheme.ProEt.topology U.toScheme)
        ((Functor.const U.toScheme.ProEtᵒᵖ).obj
          (CommRingCat.of (ULift.{t + 1} (Padic.coefficientExtensionRing l E (n + 1)))))).app
            (op V) x) =
    (toSheafify (Scheme.ProEt.topology T)
      ((Functor.const T.ProEtᵒᵖ).obj
        (CommRingCat.of (ULift.{t + 1} (Padic.coefficientExtensionRing l E (n + 1)))))).app
          (op ((sfClopenSiteInclusion U).obj V)) x
  /-- The completion comparison is the inverse-limit comparison. -/
  completion : completedIntegralCoefficientSheafUnrestricted l E U.toScheme ≅
    sfClopenRingRestriction U (completedIntegralCoefficientSheafUnrestricted l E T)
  /-- The completion comparison commutes with every quotient projection. -/
  projection : ∀ n : ℕ,
    completion.hom ≫
      ((sfClopenSiteInclusion U).sheafPushforwardContinuous _ _ _).map
        (limit.π (integralCoefficientSheafSystem l E T) (op n)) =
    limit.π (integralCoefficientSheafSystem l E U.toScheme) (op n) ≫ (finite n).hom
  /-- The finite identifications preserve the quotient transition maps. -/
  transition : ∀ n : ℕ,
    (finite (n + 1)).hom ≫
      ((sfClopenSiteInclusion U).sheafPushforwardContinuous _ _ _).map
        (integralCoefficientSheafTransition l E T n) =
    integralCoefficientSheafTransition l E U.toScheme n ≫ (finite n).hom
  /-- Ordinary completed-coefficient restriction is additive. -/
  [additive : (sfClopenModuleRestriction U _ _ completion).Additive]
  /-- It preserves kernels. -/
  [limits : PreservesFiniteLimits (sfClopenModuleRestriction U _ _ completion)]
  /-- It preserves cokernels. -/
  [colimits : PreservesFiniteColimits (sfClopenModuleRestriction U _ _ completion)]
  /-- Ordinary finite-coefficient restriction is additive. -/
  [finite_additive : ∀ n : ℕ, (sfClopenModuleRestriction U _ _ (finite n)).Additive]
  /-- Ordinary finite-coefficient restriction preserves kernels. -/
  [finite_limits : ∀ n : ℕ,
    PreservesFiniteLimits (sfClopenModuleRestriction U _ _ (finite n))]
  /-- Ordinary finite-coefficient restriction preserves cokernels. -/
  [finite_colimits : ∀ n : ℕ,
    PreservesFiniteColimits (sfClopenModuleRestriction U _ _ (finite n))]

/-- Standard localization on every localized ringed site used in the Tor test.
Source: Stacks 05RU (blueprint: lem-sf-clopen-lisse-complete-localization). -/
instance sfClopenSliceHasDerived (T : Scheme.{t})
    (R : Sheaf (Scheme.ProEt.topology T) RingCat.{v}) (V : T.ProEt)
    [HasSheafify ((Scheme.ProEt.topology T).over V) AddCommGrpCat.{v}]
    [((Scheme.ProEt.topology T).over V).WEqualsLocallyBijective AddCommGrpCat.{v}] :
    HasDerivedCategory (ringedSiteModules.{v} (R.over V)) :=
  HasDerivedCategory.standard _

attribute [instance] SfClopenCoefficientRestriction.additive
  SfClopenCoefficientRestriction.limits SfClopenCoefficientRestriction.colimits
  SfClopenCoefficientRestriction.finite_additive SfClopenCoefficientRestriction.finite_limits
  SfClopenCoefficientRestriction.finite_colimits

variable {l E}

/-- Ordinary restriction on the unbounded completed-coefficient derived category.
Source: Stacks 015F (blueprint: lem-sf-clopen-lisse-complete-localization). -/
def sfClopenDerivedRestriction {T : Scheme.{t}} {U : T.Opens}
    (d : SfClopenCoefficientRestriction l E T U) :
    DerivedCategory (scalarReductionSource l E T) ⥤
      DerivedCategory (scalarReductionSource l E U.toScheme) :=
  letI := integralCoefficientAbSheafify.{t, u} T
  letI := integralCoefficientAbLocallyBijective.{t, u} T
  letI := integralCoefficientAbSheafify.{t, u} U.toScheme
  letI := integralCoefficientAbLocallyBijective.{t, u} U.toScheme
  @Functor.mapDerivedCategory _ _ _ _ _ _ _ _
    (sfClopenModuleRestriction.{t, max u (t + 1)} U
      (completedIntegralCoefficientSheafUnrestricted l E T)
      (completedIntegralCoefficientSheafUnrestricted l E U.toScheme) d.completion)
    d.additive d.limits d.colimits

/-- The same ordinary restriction on a finite quotient, including exponent one.
Source: Stacks 015F (blueprint: lem-sf-clopen-lisse-complete-localization). -/
def sfClopenFiniteDerivedRestriction {T : Scheme.{t}} {U : T.Opens}
    (d : SfClopenCoefficientRestriction l E T U) (n : ℕ) :
    DerivedCategory (scalarReductionTarget l E T n) ⥤
      DerivedCategory (scalarReductionTarget l E U.toScheme n) :=
  letI := integralCoefficientAbSheafify.{t, u} T
  letI := integralCoefficientAbLocallyBijective.{t, u} T
  letI := integralCoefficientAbSheafify.{t, u} U.toScheme
  letI := integralCoefficientAbLocallyBijective.{t, u} U.toScheme
  @Functor.mapDerivedCategory _ _ _ _ _ _ _ _
    (sfClopenModuleRestriction.{t, max u (t + 1)} U
      (integralCoefficientSheaf l E T n)
      (integralCoefficientSheaf l E U.toScheme n) (d.finite n))
    (d.finite_additive n) (d.finite_limits n) (d.finite_colimits n)

/-- Restrict cochain complexes degreewise, with the same scalar action as module restriction.
Source: Stacks 015F (blueprint: lem-sf-clopen-lisse-complete-localization). -/
def sfClopenComplexRestriction {T : Scheme.{t}} {U : T.Opens}
    (d : SfClopenCoefficientRestriction l E T U) :
    CochainComplex (scalarReductionSource l E T) ℤ ⥤
      CochainComplex (scalarReductionSource l E U.toScheme) ℤ :=
  letI := d.additive
  (sfClopenModuleRestriction U _ _ d.completion).mapHomologicalComplex (.up ℤ)

/-- The canonical comparison of termwise restriction with unbounded localization.
Source: Stacks 015F (blueprint: lem-sf-clopen-lisse-complete-localization). -/
def sfClopenLocalizationIso {T : Scheme.{t}} {U : T.Opens}
    (d : SfClopenCoefficientRestriction l E T U)
    (P : CochainComplex (scalarReductionSource l E T) ℤ) :
    (sfClopenDerivedRestriction d).obj (DerivedCategory.Q.obj P) ≅
      DerivedCategory.Q.obj ((sfClopenComplexRestriction d).obj P) :=
  letI := d.additive
  letI := d.limits
  letI := d.colimits
  ((sfClopenModuleRestriction U _ _ d.completion).mapDerivedCategoryFactors).app P

/-- Finite-coefficient restriction on actual complexes.
Source: Stacks 015F (blueprint: lem-sf-clopen-lisse-complete-localization). -/
def sfClopenFiniteComplexRestriction {T : Scheme.{t}} {U : T.Opens}
    (d : SfClopenCoefficientRestriction l E T U) (n : ℕ) :=
  letI := d.finite_additive n
  (sfClopenModuleRestriction U _ _ (d.finite n)).mapHomologicalComplex (.up ℤ)

/-- The canonical localization comparison for finite-coefficient restriction.
Source: Stacks 015F (blueprint: lem-sf-clopen-lisse-complete-localization). -/
def sfClopenFiniteLocalizationIso {T : Scheme.{t}} {U : T.Opens}
    (d : SfClopenCoefficientRestriction l E T U) (n : ℕ)
    (P : CochainComplex (scalarReductionTarget l E T n) ℤ) :
    (sfClopenFiniteDerivedRestriction d n).obj (DerivedCategory.Q.obj P) ≅
      DerivedCategory.Q.obj ((sfClopenFiniteComplexRestriction d n).obj P) :=
  letI := d.finite_additive n
  letI := d.finite_limits n
  letI := d.finite_colimits n
  ((sfClopenModuleRestriction U _ _ (d.finite n)).mapDerivedCategoryFactors).app P

/-- The existing derived scalar-extension counit, transported from homotopy objects
by the canonical quotient comparisons. On K-flat complexes it computes reduction.
Source: Stacks 06YY (blueprint: lem-sf-clopen-lisse-complete-localization). -/
def sfClopenReductionCounit (T : Scheme.{t}) (n : ℕ)
    (P : CochainComplex (scalarReductionSource l E T) ℤ) :
    (scalarReductionDerivedExtension l E T n).obj (DerivedCategory.Q.obj P) ⟶
      DerivedCategory.Q.obj (unrestrictedTowerFiniteComplex l E T n P) :=
  (scalarReductionDerivedExtension l E T n).map
      ((DerivedCategory.quotientCompQhIso _).app P).inv ≫
    (scalarReductionCounit l E T n).app
      ((HomotopyCategory.quotient _ (.up ℤ)).obj P) ≫
    DerivedCategory.Qh.map
      (((scalarReductionExtension l E T n).mapHomotopyCategoryFactors (.up ℤ)).app P).hom ≫
    ((DerivedCategory.quotientCompQhIso _).app
      (unrestrictedTowerFiniteComplex l E T n P)).hom

/-- Test the same Tor interval after ordinary localization at every site object.
Source: Stacks 08FZ, 00Y0 (blueprint: lem-sf-clopen-lisse-complete-localization). -/
def SfResidueTorAmplitudeOnEveryObject (T : Scheme.{t})
    (K : DerivedCategory (scalarReductionTarget l E T 0)) (a b : ℤ) : Prop :=
  letI := integralCoefficientAbSheafify.{t, u} T
  letI := integralCoefficientAbLocallyBijective.{t, u} T
  ∀ V : T.ProEt,
    letI : HasDerivedCategory (ringedSiteModules.{max u (t + 1)}
        ((sheafCompose ((Scheme.ProEt.topology T).over V)
          (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).obj
            ((integralCoefficientCommRingSheaf l E T 0).over V))) :=
      HasDerivedCategory.standard _
    HasRingedSiteTorAmplitudeOfUniverses.{t + 1, t, max u (t + 1)}
      ((integralCoefficientCommRingSheaf l E T 0).over V)
      ((ringedDerivedRestrictionGeneral.{t + 1, t, max u (t + 1), max u (t + 1)}
        (integralCoefficientSheaf l E T 0) V).obj K) a b

/-- The complete restriction assertions, with normalized comparisons on actual tensors.
All fields are conclusions of the main existence theorem, not assumptions on the input.
Source: Stacks 09C3, 06YY and 08TC
(blueprint: lem-sf-clopen-lisse-complete-localization). -/
structure SfClopenCompleteRestriction {T : Scheme.{t}} {U : T.Opens}
    (d : SfClopenCoefficientRestriction l E T U) where
  /-- The natural derived reduction comparison at every positive exponent. -/
  reduction : ∀ n : ℕ,
    scalarReductionDerivedExtension l E T n ⋙ sfClopenFiniteDerivedRestriction d n ≅
      sfClopenDerivedRestriction d ⋙ scalarReductionDerivedExtension l E U.toScheme n
  /-- The finite-coefficient termwise tensor comparison. -/
  finite_quotient : ∀ (P : CochainComplex (scalarReductionSource l E T) ℤ) (n : ℕ),
    (sfClopenFiniteComplexRestriction d n).obj (unrestrictedTowerFiniteComplex l E T n P) ≅
      unrestrictedTowerFiniteComplex l E U.toScheme n ((sfClopenComplexRestriction d).obj P)
  /-- Its normalization on sheafified pure tensors fixes this comparison. -/
  finite_quotient_tensor : ∀ (P : CochainComplex (scalarReductionSource l E T) ℤ)
      (n : ℕ) (q : ℤ) (V : U.toScheme.ProEt)
      (s : (integralCoefficientCommRingSheaf l E U.toScheme n).obj.obj (op V))
      (x : (P.X q).val.obj (op ((sfClopenSiteInclusion U).obj V))),
    (((finite_quotient P n).hom.f q).val.app (op V))
      (unrestrictedTowerTensorSection l E T n (P.X q)
        (op ((sfClopenSiteInclusion U).obj V)) ((d.finite n).hom.hom.app (op V) s) x) =
    unrestrictedTowerTensorSection l E U.toScheme n
      (((sfClopenComplexRestriction d).obj P).X q) (op V) s x
  /-- The derived reduction is the comparison induced by these tensors and the counits. -/
  reduction_counit : ∀ (P : CochainComplex (scalarReductionSource l E T) ℤ) (n : ℕ),
    (sfClopenFiniteDerivedRestriction d n).map (sfClopenReductionCounit T n P) ≫
        (sfClopenFiniteLocalizationIso d n (unrestrictedTowerFiniteComplex l E T n P)).hom ≫
        DerivedCategory.Q.map (finite_quotient P n).hom =
      (reduction n).hom.app (DerivedCategory.Q.obj P) ≫
        (scalarReductionDerivedExtension l E U.toScheme n).map
          (sfClopenLocalizationIso d P).hom ≫
        sfClopenReductionCounit U.toScheme n ((sfClopenComplexRestriction d).obj P)
  /-- Restriction of the actual termwise quotients, with their restricted scalar actions. -/
  quotient : ∀ (P : CochainComplex (scalarReductionSource l E T) ℤ) (n : ℕ),
    (sfClopenComplexRestriction d).obj (unrestrictedTowerComplex l E T n P) ≅
      unrestrictedTowerComplex l E U.toScheme n ((sfClopenComplexRestriction d).obj P)
  /-- The quotient comparison is the sectionwise pure-tensor comparison. -/
  quotient_tensor : ∀ (P : CochainComplex (scalarReductionSource l E T) ℤ)
      (n : ℕ) (q : ℤ) (V : U.toScheme.ProEt)
      (s : (integralCoefficientCommRingSheaf l E U.toScheme n).obj.obj (op V))
      (x : (P.X q).val.obj (op ((sfClopenSiteInclusion U).obj V))),
    (((quotient P n).hom.f q).val.app (op V))
      (unrestrictedTowerTensorSection l E T n (P.X q)
        (op ((sfClopenSiteInclusion U).obj V)) ((d.finite n).hom.hom.app (op V) s) x) =
    unrestrictedTowerTensorSection l E U.toScheme n
      (((sfClopenComplexRestriction d).obj P).X q) (op V) s x
  /-- One isomorphism of towers retains every quotient transition. -/
  tower : ∀ P : CochainComplex (scalarReductionSource l E T) ℤ,
    canonicalIntegralReductionTower l E T P ⋙ sfClopenDerivedRestriction d ≅
      canonicalIntegralReductionTower l E U.toScheme ((sfClopenComplexRestriction d).obj P)
  /-- The tower comparison is induced by the preceding actual quotient comparisons. -/
  tower_quotient : ∀ (P : CochainComplex (scalarReductionSource l E T) ℤ) (n : ℕ),
    (tower P).hom.app (op n) =
      (sfClopenLocalizationIso d (unrestrictedTowerComplex l E T n P)).hom ≫
        DerivedCategory.Q.map (quotient P n).hom
  /-- The canonical quotient projections agree under this tower isomorphism. -/
  tower_unit : ∀ (P : CochainComplex (scalarReductionSource l E T) ℤ) (n : ℕ),
    (sfClopenDerivedRestriction d).map
        (DerivedCategory.Q.map (unrestrictedTowerUnit l E T P n)) ≫
      (tower P).hom.app (op n) =
    (sfClopenLocalizationIso d P).hom ≫
      DerivedCategory.Q.map
        (unrestrictedTowerUnit l E U.toScheme ((sfClopenComplexRestriction d).obj P) n)
  /-- Ordinary restriction preserves the canonically augmented Roos completeness condition. -/
  complete : ∀ M : DerivedCategory (scalarReductionSource l E T),
    IsDerivedCompleteUnrestricted l E T M →
      IsDerivedCompleteUnrestricted l E U.toScheme ((sfClopenDerivedRestriction d).obj M)
  /-- The bounds remain the same on every object of the component site. -/
  tor : ∀ (M : DerivedCategory (scalarReductionSource l E T)) (a b : ℤ),
    SfResidueTorAmplitudeOnEveryObject (l := l) (E := E) T
      ((scalarReductionDerivedExtension l E T 0).obj M) a b →
    SfResidueTorAmplitudeOnEveryObject (l := l) (E := E) U.toScheme
      ((scalarReductionDerivedExtension l E U.toScheme 0).obj
        ((sfClopenDerivedRestriction d).obj M)) a b

/-- A common finite clopen partition trivializes finitely many finite lisse residue sheaves,
and ordinary restriction preserves their completed coefficient and derived quotient data.

Source: Stacks Project, proetale.tex, Tags 09C3 and 098F; sites-cohomology.tex, Tag 0946;
derived.tex, Tags 015F and 08TC (blueprint: lem-sf-clopen-lisse-complete-localization).

Proof plan:
1. Intersect the finitely many trivializing coverings by fibre products and refine by
   finitely many affine covering members (sk-def-pe-site). Constant module restriction
   retains the local models (lem-pe-constant-module-restriction-universes).
2. Form the finite scheme coproduct. Subcanonicity and the locally-surjective epi
   criterion make its represented sheaf epic over the terminal sheaf. Weak contractibility
   gives a section. Its inverse images of the coproduct components form a finite clopen
   partition. Pull back the models, choose finite bases and discard empty pieces.
3. For a clopen U, extend a sheaf on U to T by evaluation on V times_T U. Along an epi,
   local lifts on U together with the complementary clopen give local lifts on T.
   The assumed evaluation property on T therefore implies it on U.
4. Apply lem-weil-pbc-proetale-weakly-contractible-evaluation-exact. Evaluation is exact;
   lift the finitely many images of basis sections to prove finite free projectivity.
5. Constant-section comparisons identify all finite coefficients. Limits are sectionwise,
   so compatible tuples give the completed ring comparison, with projection and transition
   squares. No invertibility assumption on ell is used.
6. Finite-clopen module gluing and finite-product derived tensor calculus identify exact
   ordinary restriction, termwise tensor, and scalar restriction. The pure-tensor formulas
   give the normalized quotient comparisons; they preserve all transitions and units.
7. Under the finite-product derived equivalence, insertion in the component is left
   adjoint to restriction. Thus restriction preserves the tower product. Applying it to
   the Roos triangle preserves 1-s and the canonical augmentation, hence completeness.
8. Relocalization identifies every V over U with the same object over T. The residue
   comparison from step 6 identifies their tensors with every degree-zero module. The
   given vanishing outside [a,b] is consequently unchanged. The empty scheme admits
   the empty partition, and all module and derived assertions there are zero cases. -/
theorem sf_clopen_lisse_complete_localization
    (T : Scheme.{t}) (hT : IsAffine T)
    (hweak : ∀ (F G : Sheaf (Scheme.ProEt.topology T) (Type (max u (t + 1))))
      (f : F ⟶ G), Epi f →
        Function.Surjective (f.hom.app (op (Scheme.ProEt.mk (𝟙 T)))))
    (J : Type v) [Finite J]
    (F : J → scalarReductionTarget l E T 0)
    (hF : ∀ j : J, IsLocallyConstantProEtaleModuleSheafWithModelsOfUniverses T
      (Padic.coefficientExtensionRing l E 1)
      (fun N ↦ Module.Finite (ULift.{t + 1} (Padic.coefficientExtensionRing l E 1)) N)
      (F j)) :
    ∃ (n : ℕ) (U : Fin n → T.Opens),
      (⨆ i, U i) = ⊤ ∧ Pairwise (fun i j ↦ Disjoint (U i) (U j)) ∧
      ∀ i : Fin n,
        IsClosed (U i : Set T) ∧ IsCompact (U i : Set T) ∧
        (∀ (A B : Sheaf (Scheme.ProEt.topology (U i).toScheme)
            (Type (max u (t + 1)))) (f : A ⟶ B), Epi f →
          Function.Surjective
            (f.hom.app (op (Scheme.ProEt.mk (𝟙 (U i).toScheme))))) ∧
        (∀ j : J, ∃ r : ℕ,
          Nonempty ((F j).over (Scheme.ProEt.mk (U i).ι) ≅
            proEtaleConstantModuleSheafOverOfUniverses T
              (Padic.coefficientExtensionRing l E 1) (Scheme.ProEt.mk (U i).ι)
              (ModuleCat.of (ULift.{t + 1} (Padic.coefficientExtensionRing l E 1))
                (Fin r → ULift.{t + 1} (Padic.coefficientExtensionRing l E 1))))) ∧
        (∀ C : Sheaf (Scheme.ProEt.topology (U i).toScheme)
            CommRingCat.{max w (t + 1)},
          (SheafOfModules.evaluation.{max w (t + 1)}
            ((sheafCompose _ (forget₂ CommRingCat.{max w (t + 1)}
              RingCat.{max w (t + 1)})).obj C)
            (op (Scheme.ProEt.mk (𝟙 (U i).toScheme)))).PreservesHomology ∧
          ∀ r : ℕ, Projective (∏ᶜ fun _ : Fin r ↦ SheafOfModules.unit
            ((sheafCompose _ (forget₂ CommRingCat.{max w (t + 1)}
              RingCat.{max w (t + 1)})).obj C))) ∧
        ∃ d : SfClopenCoefficientRestriction l E T (U i),
          Nonempty (SfClopenCompleteRestriction d) := by
  sorry

end WeilConjectures
