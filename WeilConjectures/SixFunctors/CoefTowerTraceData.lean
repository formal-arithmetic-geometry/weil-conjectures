/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.FiniteDualizing
public import WeilConjectures.AlgebraicGeometry.FiniteFieldFiberSupplement
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import WeilConjectures.AlgebraicGeometry.IntegralRationalQbarCompactSupport
public import WeilConjectures.AlgebraicGeometry.FixedFiniteExceptionalAt
public import WeilConjectures.CategoryTheory.DiagramSiteRealization
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.CategoryTheory.Sites.Limits
public import WeilConjectures.AlgebraicGeometry.NormalizedDVRTower
public import WeilConjectures.AlgebraicGeometry.CoefficientRingedSequenceSiteSupplement
public import WeilConjectures.AlgebraicGeometry.FiniteCoefficientPoint
public import WeilConjectures.AlgebraicGeometry.ProEtaleIntrinsicExtensionByZeroExact
public import WeilConjectures.AlgebraicGeometry.CompletedIntegralConstantMapOfUniverses
public import WeilConjectures.AlgebraicGeometry.CompletedIntegralCoefficientGerm
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Ordinary
public import WeilConjectures.SixFunctors.Etale.Derived.GeometricPoint

/-!
# Finite counits on the dualizing compact-support tower

Source: blueprint `sec-six-functors/sk-prop-sf-biduality-general`, proof paragraph 2
of `prop-coef-integral-dualizing` (blueprint: lem-coef-tower-trace-rectification).

The quotient-ring system is restricted by its actual constant scalar action.
Open extension, proper image and point sections are performed separately on strict
module towers before localization. No inverse limit occurs in this construction.

## Main definitions and statements

- `coefTraceDualizingTower`: the actual derived compact-support tower of Q.
- `coefTraceFiniteTransition`: the scalar-unit/projection-transpose transition.
- `coefTraceTargetIso`: the canonical identification of the target with A_n[0].
- `coefTowerTraceRectification`: evaluated transitions and finite counit squares.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048

universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- Constant integral scalars in the common section universe.
Source: blueprint finite counit tower (blueprint: lem-coef-tower-trace-rectification). -/
abbrev coefTraceRing := ULift.{u + 1, u} (Padic.coefficientExtensionIntegers l E)

/-- The constant-section map into the completed ring at the final object.
Source: blueprint finite counit tower (blueprint: lem-coef-tower-trace-rectification). -/
def coefTraceScalar (W : Scheme.{u}) :
    coefTraceRing l E →+*
      (completedIntegralCoefficientSheafUnrestricted l E W).obj.obj
        (op (ProEt.mk (𝟙 W))) :=
  (((integralConstantToCompletionOfUniverses l E W).hom.app
      (op (ProEt.mk (𝟙 W)))).hom).comp
    (((forget₂ CommRingCat RingCat).map
      ((toSheafify (ProEt.topology W)
        ((Functor.const W.ProEtᵒᵖ).obj (CommRingCat.of (coefTraceRing l E)))).app
          (op (ProEt.mk (𝟙 W))))).hom)

/-- Restrict completed modules to the actual constant integral scalar action.
The first functor uses the maps from the final object to every object, and the
second uses the constant-to-completion map at that final object.
Source: blueprint finite counit tower (blueprint: lem-coef-tower-trace-rectification). -/
def coefTraceConstantScalars (W : Scheme.{u}) :
    scalarReductionSource.{u, u} l E W ⥤
      Sheaf (ProEt.topology W) (ModuleCat.{u + 1} (coefTraceRing l E)) :=
  SheafOfModules.forgetToSheafModuleCat
      (completedIntegralCoefficientSheafUnrestricted l E W)
      (op (ProEt.mk (𝟙 W))) (MorphismProperty.Over.mkIdTerminal _ _).op ⋙
    sheafCompose (ProEt.topology W)
      (ModuleCat.restrictScalars
        (coefTraceScalar l E W))

/-- Exactness of constant scalar restriction, retaining unchanged abelian sheaves.
Source: blueprint finite counit tower (blueprint: lem-coef-tower-trace-rectification).
Proof: the maps from the final object give the same underlying abelian sheaf.
Restriction changes only the scalar action, hence preserves kernels and the
sheafified cokernels, and addition of maps is unchanged. -/
theorem coefTraceConstantScalars_exact (W : Scheme.{u}) :
    (coefTraceConstantScalars l E W).Additive ∧
      PreservesFiniteLimits (coefTraceConstantScalars l E W) ∧
      PreservesFiniteColimits (coefTraceConstantScalars l E W) := by
  let J := ProEt.topology W
  let V := forget₂ (ModuleCat.{u + 1} (coefTraceRing l E)) AddCommGrpCat.{u + 1}
  let U := sheafCompose J V
  have : PreservesFiniteLimits U := by
    have : PreservesFiniteLimits (U ⋙ sheafToPresheaf J AddCommGrpCat.{u + 1}) := by
      change PreservesFiniteLimits (sheafToPresheaf J _ ⋙
        (Functor.whiskeringRight W.ProEtᵒᵖ
          (ModuleCat.{u + 1} (coefTraceRing l E)) AddCommGrpCat.{u + 1}).obj V)
      have : PreservesFiniteLimits ((Functor.whiskeringRight W.ProEtᵒᵖ
          (ModuleCat.{u + 1} (coefTraceRing l E)) AddCommGrpCat.{u + 1}).obj V) :=
        ⟨fun _ _ _ ↦ inferInstance⟩
      infer_instance
    exact preservesFiniteLimits_of_reflects_of_preserves _
      (sheafToPresheaf J AddCommGrpCat.{u + 1})
  have : J.PreservesSheafification V := by
    constructor
    intro P Q f hf
    change J.W (Functor.whiskerRight f V)
    have : Presheaf.IsLocallyInjective J f := hf.isLocallyInjective
    have : Presheaf.IsLocallySurjective J f := hf.isLocallySurjective
    apply (J.W_iff_isLocallyBijective _).mpr
    constructor
    · exact ⟨fun x y h ↦ Presheaf.equalizerSieve_mem J f x y h⟩
    · exact ⟨fun x ↦ Presheaf.imageSieve_mem J f x⟩
  have : PreservesFiniteColimits U := by
    constructor
    intro K _ _
    rw [(sheafificationAdjunction J
      (ModuleCat.{u + 1} (coefTraceRing l E))).preservesColimitsOfShape_iff]
    have : PreservesColimitsOfShape K ((Functor.whiskeringRight W.ProEtᵒᵖ
          (ModuleCat.{u + 1} (coefTraceRing l E)) AddCommGrpCat.{u + 1}).obj V) :=
      inferInstance
    exact preservesColimitsOfShape_of_natIso
      (sheafComposeNatIso J V
        (sheafificationAdjunction J (ModuleCat.{u + 1} (coefTraceRing l E)))
        (sheafificationAdjunction J AddCommGrpCat.{u + 1}))
  have : U.ReflectsIsomorphisms := inferInstance
  have : ReflectsFiniteLimits U := ⟨fun _ _ _ ↦ inferInstance⟩
  have : ReflectsFiniteColimits U := reflectsFiniteColimitsOfReflectsIsomorphisms U
  have : PreservesFiniteLimits (coefTraceConstantScalars l E W ⋙ U) :=
    inferInstanceAs (PreservesFiniteLimits (SheafOfModules.toSheaf
      (completedIntegralCoefficientSheafUnrestricted l E W)))
  have : PreservesFiniteColimits (coefTraceConstantScalars l E W ⋙ U) :=
    inferInstanceAs (PreservesFiniteColimits (SheafOfModules.toSheaf
      (completedIntegralCoefficientSheafUnrestricted l E W)))
  refine ⟨?_, preservesFiniteLimits_of_reflects_of_preserves _ U,
    preservesFiniteColimits_of_reflects_of_preserves _ U⟩
  exact { map_add := by intros; rfl }

/-- Additive constant scalar restriction.
Source: blueprint finite counit tower (blueprint: lem-coef-tower-trace-rectification). -/
instance coefTraceConstantScalars_additive (W : Scheme.{u}) :
    (coefTraceConstantScalars l E W).Additive :=
  (coefTraceConstantScalars_exact l E W).1

/-- Left exact constant scalar restriction.
Source: blueprint finite counit tower (blueprint: lem-coef-tower-trace-rectification). -/
instance coefTraceConstantScalars_limits (W : Scheme.{u}) :
    PreservesFiniteLimits (coefTraceConstantScalars l E W) :=
  (coefTraceConstantScalars_exact l E W).2.1

/-- Right exact constant scalar restriction.
Source: blueprint finite counit tower (blueprint: lem-coef-tower-trace-rectification). -/
instance coefTraceConstantScalars_colimits (W : Scheme.{u}) :
    PreservesFiniteColimits (coefTraceConstantScalars l E W) :=
  (coefTraceConstantScalars_exact l E W).2.2

/-- Strict towers of ordinary module sheaves with the constant integral action.
Source: blueprint finite counit tower (blueprint: lem-coef-tower-trace-rectification). -/
abbrev coefTraceSheafTowers (W : Scheme.{u}) :=
  ℕᵒᵖ ⥤ Sheaf (ProEt.topology W) (ModuleCat.{u + 1} (coefTraceRing l E))

/-- Use the standard localization for strict sheaf towers.
Source: Stacks 0941 (blueprint: lem-coef-tower-trace-rectification). -/
instance coefTraceSheafTowers_derived (W : Scheme.{u}) :
    HasDerivedCategory (coefTraceSheafTowers l E W) := HasDerivedCategory.standard _

/-- Use the standard localization for strict module towers.
Source: Stacks 0941 (blueprint: lem-coef-tower-trace-rectification). -/
instance coefTraceModuleTowers_derived :
    HasDerivedCategory (ℕᵒᵖ ⥤ ModuleCat.{u + 1} (coefTraceRing l E)) :=
  HasDerivedCategory.standard _

/-- Actual quotient-ring systems, restricted to strict constant-scalar sheaf towers.
The recorded restriction keeps every horizontal quotient-semilinear arrow.
Source: blueprint finite counit tower (blueprint: lem-coef-tower-trace-rectification). -/
def coefTraceSystemRestriction (W : Scheme.{u}) :
    coefficientSequenceModules.{u, u} l E W ⥤ coefTraceSheafTowers l E W :=
  coefficientSequenceRestriction.{u, u} l E W ⋙
    (Functor.whiskeringRight ℕᵒᵖ _ _).obj (coefTraceConstantScalars l E W)

/-- The additive structure is inherited from the two exact restriction functors.
Source: blueprint finite counit tower (blueprint: lem-coef-tower-trace-rectification). -/
instance coefTraceSystemRestriction_additive (W : Scheme.{u}) :
    (coefTraceSystemRestriction l E W).Additive := inferInstanceAs (_ ⋙ _).Additive

/-- Exactness of the actual scalar restriction on systems.
Source: Stacks 0941 (blueprint: lem-coef-tower-trace-rectification).
Proof: the underlying sheaves and horizontal maps are unchanged. Kernels and
cokernels are computed on each vertical slice and restriction changes only actions. -/
theorem coefTraceSystemRestriction_exact (W : Scheme.{u}) :
    PreservesFiniteLimits (coefTraceSystemRestriction l E W) ∧
      PreservesFiniteColimits (coefTraceSystemRestriction l E W) := by
  have : PreservesFiniteLimits
      ((Functor.whiskeringRight ℕᵒᵖ _ _).obj (coefTraceConstantScalars l E W)) :=
    ⟨fun _ _ _ ↦ inferInstance⟩
  have : PreservesFiniteColimits
      ((Functor.whiskeringRight ℕᵒᵖ _ _).obj (coefTraceConstantScalars l E W)) :=
    ⟨fun _ _ _ ↦ inferInstance⟩
  unfold coefTraceSystemRestriction
  exact ⟨inferInstance, inferInstance⟩

/-- Left exactness follows levelwise from exact scalar restriction.
Source: blueprint finite counit tower (blueprint: lem-coef-tower-trace-rectification). -/
instance coefTraceSystemRestriction_limits (W : Scheme.{u}) :
    PreservesFiniteLimits (coefTraceSystemRestriction l E W) :=
  (coefTraceSystemRestriction_exact l E W).1

/-- Right exactness follows levelwise from exact scalar restriction.
Source: blueprint finite counit tower (blueprint: lem-coef-tower-trace-rectification). -/
instance coefTraceSystemRestriction_colimits (W : Scheme.{u}) :
    PreservesFiniteColimits (coefTraceSystemRestriction l E W) :=
  (coefTraceSystemRestriction_exact l E W).2

/-- Open extension on strict constant-scalar towers.
Source: blueprint finite counit tower (blueprint: lem-coef-tower-trace-rectification). -/
def coefTraceOpen {X Z : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j] :
    coefTraceSheafTowers l E X ⥤ coefTraceSheafTowers l E Z :=
  (Functor.whiskeringRight ℕᵒᵖ _ _).obj
    (ProEtale.openImmersionLowerShriek (ModuleCat.{u + 1} (coefTraceRing l E)) j)

/-- Proper direct image on strict towers, prior to deriving.
Source: blueprint finite counit tower (blueprint: lem-coef-tower-trace-rectification). -/
def coefTracePush {Z S : Scheme.{u}} (p : Z ⟶ S) :
    coefTraceSheafTowers l E Z ⥤ coefTraceSheafTowers l E S :=
  (Functor.whiskeringRight ℕᵒᵖ _ _).obj
    (ProEtale.lowerStar (ModuleCat.{u + 1} (coefTraceRing l E)) p)

/-- Point sections retain the tower index; they never take an inverse limit.
Source: blueprint finite counit tower (blueprint: lem-coef-tower-trace-rectification). -/
def coefTraceSections (S : Scheme.{u}) :
    coefTraceSheafTowers l E S ⥤ (ℕᵒᵖ ⥤ ModuleCat.{u + 1} (coefTraceRing l E)) :=
  (Functor.whiskeringRight ℕᵒᵖ _ _).obj
    ((sheafSections (ProEt.topology S) (ModuleCat.{u + 1} (coefTraceRing l E))).obj
      (op (ProEt.mk (𝟙 S))))

/-- Additivity of levelwise open extension.
Source: Stacks 0941 (blueprint: lem-coef-tower-trace-rectification). -/
instance coefTraceOpen_additive {X Z : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j] :
    (coefTraceOpen l E j).Additive :=
  inferInstanceAs ((Functor.whiskeringRight _ _ _).obj _).Additive

/-- Additivity of levelwise proper image.
Source: Stacks 0941 (blueprint: lem-coef-tower-trace-rectification). -/
instance coefTracePush_additive {Z S : Scheme.{u}} (p : Z ⟶ S) :
    (coefTracePush l E p).Additive :=
  inferInstanceAs ((Functor.whiskeringRight _ _ _).obj _).Additive

/-- Additivity of levelwise point sections.
Source: Stacks 0941 (blueprint: lem-coef-tower-trace-rectification).
Proof: sections and tower morphisms add componentwise. -/
@[instance] theorem coefTraceSections_additive (S : Scheme.{u}) :
    (coefTraceSections l E S).Additive := by
  have : ((sheafSections (ProEt.topology S)
      (ModuleCat.{u + 1} (coefTraceRing l E))).obj
        (op (ProEt.mk (𝟙 S)))).Additive := ⟨by intros; rfl⟩
  unfold coefTraceSections
  infer_instance

/-- Exactness of levelwise open extension.
Source: Stacks 0941 (blueprint: lem-coef-tower-trace-rectification).
Proof: open extension is exact on module sheaves and tower kernels and cokernels
are computed levelwise. -/
theorem coefTraceOpen_exact {X Z : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j] :
    PreservesFiniteLimits (coefTraceOpen l E j) ∧
      PreservesFiniteColimits (coefTraceOpen l E j) := by
  unfold coefTraceOpen
  exact ⟨⟨fun _ _ _ ↦ inferInstance⟩, ⟨fun _ _ _ ↦ inferInstance⟩⟩

/-- Left exact open extension on towers.
Source: Stacks 0941 (blueprint: lem-coef-tower-trace-rectification). -/
instance coefTraceOpen_limits {X Z : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j] :
    PreservesFiniteLimits (coefTraceOpen l E j) := (coefTraceOpen_exact l E j).1

/-- Right exact open extension on towers.
Source: Stacks 0941 (blueprint: lem-coef-tower-trace-rectification). -/
instance coefTraceOpen_colimits {X Z : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j] :
    PreservesFiniteColimits (coefTraceOpen l E j) := (coefTraceOpen_exact l E j).2

/-- Simultaneous resolutions for ordinary module-sheaf towers.
Source: Stacks 079P, 0941 (blueprint: lem-coef-tower-trace-rectification).
Proof: module sheaves on the pro-etale site form a Grothendieck abelian
category. The presheaf generator construction supplies a generator of strict
towers, and filtered colimits are exact levelwise. Thus the tower category is
Grothendieck abelian and admits K-injective resolutions. -/
@[instance] theorem coefTraceSheafTowers_kInjectives (W : Scheme.{u}) :
    Abelian.HasKInjectiveResolutions (coefTraceSheafTowers l E W) := by
  let A := Sheaf (ProEt.topology W) (ModuleCat.{u + 1} (coefTraceRing l E))
  have : IsGrothendieckAbelian.{u + 1} A := inferInstance
  have : AB5OfSize.{u + 1, u + 1} (ℕᵒᵖ ⥤ A) := ⟨fun _ _ _ ↦ inferInstance⟩
  have : IsGrothendieckAbelian.{u + 1} (ℕᵒᵖ ⥤ A) := {}
  exact Abelian.hasKInjectiveResolutions_of_isGrothendieckAbelian

/-- The sequence site in the single coefficient presentation used here.
Source: Stacks 0941 (blueprint: lem-coef-tower-trace-rectification). -/
instance coefTraceSequenceSmall (W : Scheme.{u}) :
    EssentiallySmall.{u + 1} (ℕ × W.ProEt) := essentiallySmallSelf.{0, u, u + 1} _

/-- The restricted ringed compact-support/point-section composite.
The proper image and point sections are derived separately. Exact scalar
restriction identifies this with restriction of the varying-ring construction:
both ordinary functors have the same underlying sheaves, and the canonical
right-derived composition comparisons fix the transport.
Source: blueprint finite counit tower (blueprint: lem-coef-tower-trace-rectification). -/
def coefTraceCompactSections {X S : Scheme.{u}} {a : X ⟶ S}
    (c : Compactification a) :
    coefficientSequenceDerived.{u, u} l E X ⥤
      DerivedCategory (ℕᵒᵖ ⥤ ModuleCat.{u + 1} (coefTraceRing l E)) :=
  letI := HasDerivedCategory.standard (coefficientSequenceModules.{u, u} l E X)
  (coefTraceSystemRestriction l E X).mapDerivedCategory ⋙
    (coefTraceOpen l E c.i).mapDerivedCategory ⋙
    (coefTracePush l E c.g).rightDerivedFunctor ⋙
    (coefTraceSections l E S).rightDerivedFunctor

/-- The actual quotient from the integral ring to positive level n+1.
Source: blueprint proof paragraph 2 (blueprint: lem-coef-tower-trace-rectification). -/
def coefTraceQuotient (n : ℕ) : coefTraceRing l E →+* finiteDualizingCoeff l E n :=
  RingHom.ulift.{u + 1, u + 1}
    (Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E (n + 1)))

/-- Integral quotient maps commute with every finite quotient transition.
Source: blueprint proof paragraph 2 (blueprint: lem-coef-tower-trace-rectification).
Proof: both sides send the lift of r to its residue class at level n+1. -/
theorem coefTraceQuotient_comp {m n : ℕ} (h : n ≤ m) :
    coefTraceQuotient l E n =
      (finiteDualizingQuotient l E h).comp (coefTraceQuotient l E m) := by
  apply RingHom.ext
  intro x
  rfl

/-- Derived evaluation from the derived category of strict module towers.
Source: Stacks 0941 (blueprint: lem-coef-tower-trace-rectification). -/
abbrev coefTraceEvaluation (n : ℕ) :
    DerivedCategory (ℕᵒᵖ ⥤ ModuleCat.{u + 1} (coefTraceRing l E)) ⥤
      DerivedCategory (ModuleCat.{u + 1} (coefTraceRing l E)) :=
  ((evaluation ℕᵒᵖ (ModuleCat.{u + 1} (coefTraceRing l E))).obj (op n)).mapDerivedCategory

/-- The actual transition of an evaluated derived tower, for any pair of levels.
Source: Stacks 0941 (blueprint: lem-coef-tower-trace-rectification). -/
def coefTraceTransition {m n : ℕ} (h : n ≤ m) :
    coefTraceEvaluation l E m ⟶ coefTraceEvaluation l E n :=
  Localization.liftNatTrans DerivedCategory.Q
    (HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ ModuleCat.{u + 1} (coefTraceRing l E))
      (ComplexShape.up ℤ)) _ _ (coefTraceEvaluation l E m) (coefTraceEvaluation l E n)
    (Functor.whiskerRight
      (NatTrans.mapHomologicalComplex
        ((evaluation ℕᵒᵖ (ModuleCat.{u + 1} (coefTraceRing l E))).map (homOfLE h).op)
        (ComplexShape.up ℤ)) DerivedCategory.Q)

variable (D : FiniteFieldDatum.{u})

/-- Exact point sections on the etale presentation, after restriction to R.
The etale presentation of the finite exceptional functor is the one used in
finiteDualizingOrigin; sections at the separably closed point are exact.
Source: blueprint proof paragraph 2 (blueprint: lem-coef-tower-trace-rectification). -/
def coefTracePointSections :
    DerivedCategory (Sheaf (Spec (.of D.k)).smallEtaleTopology
      (ModuleCat.{u + 1} (coefTraceRing l E))) ⥤
      DerivedCategory (ModuleCat.{u + 1} (coefTraceRing l E)) :=
  ((sheafSections (Spec (.of D.k)).smallEtaleTopology
    (ModuleCat.{u + 1} (coefTraceRing l E))).obj
      (op (etalePoint D.k))).mapDerivedCategory

/-- Restriction to R and then derived point sections at finite level.
Source: blueprint proof paragraph 2 (blueprint: lem-coef-tower-trace-rectification). -/
def coefTraceFiniteSections (n : ℕ) :
    Etale.DerivedCategoryModule (finiteDualizingCoeff l E n) (Spec (.of D.k)) ⥤
      DerivedCategory (ModuleCat.{u + 1} (coefTraceRing l E)) :=
  Sheaf.derivedRestrictScalars (Spec (.of D.k)).smallEtaleTopology
      (coefTraceQuotient l E n) ⋙ coefTracePointSections l E D

variable (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
  [QuasiCompact (X ↘ Spec (.of D.k))] [IsSeparated (X ↘ Spec (.of D.k))]

/-- The finite compact-support value in D(R), using its specified etale presentation.
Source: blueprint proof paragraph 2 (blueprint: lem-coef-tower-trace-rectification). -/
def coefTraceFiniteValue (n : ℕ) : DerivedCategory (ModuleCat.{u + 1} (coefTraceRing l E)) :=
  (coefTraceFiniteSections l E D n).obj
    ((finiteDualizingEtaleSupport l E D X n).obj (finiteDualizingEtaleTerm l E D X n))

/-- Point sections of the coefficient unit, before its canonical identification with A_n.
Source: blueprint proof paragraph 2 (blueprint: lem-coef-tower-trace-rectification). -/
def coefTraceFiniteTarget (n : ℕ) :
    DerivedCategory (ModuleCat.{u + 1} (coefTraceRing l E)) :=
  (coefTraceFiniteSections l E D n).obj
    (Etale.constantComplex (finiteDualizingCoeff l E n) (Spec (.of D.k)))

/-- The finite exceptional counit followed by point sections and restriction to R.
Source: blueprint proof paragraph 2 (blueprint: lem-coef-tower-trace-rectification). -/
def coefTraceFiniteCounit (n : ℕ) :
    coefTraceFiniteValue l E D X n ⟶ coefTraceFiniteTarget l E D n :=
  (coefTraceFiniteSections l E D n).map (finiteDualizingEtaleCounit l E D X n)

/-- Compact support of the semilinear adjunct, written with the scalar unit and
canonical compact-support coefficient comparison. This is the projection-transpose
formula; its finite counit is the same one defining the dualizing comparison.
Source: blueprint proof paragraph 2 (blueprint: lem-coef-tower-trace-rectification). -/
def coefTraceFiniteTransition {m n : ℕ} (h : n ≤ m) :
    coefTraceFiniteValue l E D X m ⟶ coefTraceFiniteValue l E D X n :=
  (coefTracePointSections l E D).map
    ((Sheaf.derivedRestrictScalars (Spec (.of D.k)).smallEtaleTopology
      (coefTraceQuotient l E m)).map
      ((Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars
        (Spec (.of D.k)).smallEtaleTopology (finiteDualizingQuotient l E h))).unit.app
          ((finiteDualizingEtaleSupport l E D X m).obj
            (finiteDualizingEtaleTerm l E D X m)) ≫
        (Sheaf.derivedRestrictScalars (Spec (.of D.k)).smallEtaleTopology
          (finiteDualizingQuotient l E h)).map
          (finiteDualizingCompactComparison l E D X h ≫
            (finiteDualizingEtaleSupport l E D X n).map
              (finiteDualizingEtaleComparison l E D X h))) ≫
      (Sheaf.derivedRestrictScalarsCompIso (Spec (.of D.k)).smallEtaleTopology
        (coefTraceQuotient_comp l E h)).hom.app
          ((finiteDualizingEtaleSupport l E D X n).obj
            (finiteDualizingEtaleTerm l E D X n)))

/-- The coefficient-unit transition: the tensor--restriction unit followed by
T(A_m)=A_n. Under sections this is the actual quotient A_m to A_n.
Source: blueprint proof paragraph 2 (blueprint: lem-coef-tower-trace-rectification). -/
def coefTraceTargetTransition {m n : ℕ} (h : n ≤ m) :
    coefTraceFiniteTarget l E D m ⟶ coefTraceFiniteTarget l E D n :=
  (coefTracePointSections l E D).map
    ((Sheaf.derivedRestrictScalars (Spec (.of D.k)).smallEtaleTopology
      (coefTraceQuotient l E m)).map
      ((Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars
        (Spec (.of D.k)).smallEtaleTopology (finiteDualizingQuotient l E h))).unit.app
          (Etale.constantComplex (finiteDualizingCoeff l E m) (Spec (.of D.k))) ≫
        (Sheaf.derivedRestrictScalars (Spec (.of D.k)).smallEtaleTopology
          (finiteDualizingQuotient l E h)).map
          (Etale.ExceptionalCoefficients.unitIso (finiteDualizingQuotient l E h)
            (Spec (.of D.k))).hom) ≫
      (Sheaf.derivedRestrictScalarsCompIso (Spec (.of D.k)).smallEtaleTopology
        (coefTraceQuotient_comp l E h)).hom.app
          (Etale.constantComplex (finiteDualizingCoeff l E n) (Spec (.of D.k))))

/-- The quotient module with its actual integral action.
Source: blueprint proof paragraph 2 (blueprint: lem-coef-tower-trace-rectification). -/
def coefTraceQuotientModule (n : ℕ) : ModuleCat.{u + 1} (coefTraceRing l E) :=
  (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} (coefTraceQuotient l E n)).obj
    (𝟙_ (ModuleCat.{u + 1} (finiteDualizingCoeff l E n)))

/-- The canonical ordinary sections identification for the coefficient unit.
It is restriction of the monoidal constant-sheaf unit, the actual constant-sheaf
scalar comparison, and the inverse unit of constant sheaf adjoint point sections.
Source: blueprint proof paragraph 2 (blueprint: lem-coef-tower-trace-rectification). -/
def coefTraceUnitSectionsIso (n : ℕ) :
    ((sheafSections (Spec (.of D.k)).smallEtaleTopology
      (ModuleCat.{u + 1} (coefTraceRing l E))).obj (op (etalePoint D.k))).obj
        ((Sheaf.restrictScalars (Spec (.of D.k)).smallEtaleTopology
          (coefTraceQuotient l E n)).obj
            (𝟙_ (Sheaf (Spec (.of D.k)).smallEtaleTopology
              (ModuleCat.{u + 1} (finiteDualizingCoeff l E n))))) ≅
      coefTraceQuotientModule l E n :=
  letI : (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1}
      (coefTraceQuotient l E n)).IsLeftAdjoint :=
    (ModuleCat.restrictCoextendScalarsAdj.{u + 1, u + 1, u + 1}
      (coefTraceQuotient l E n)).isLeftAdjoint
  ((sheafSections (Spec (.of D.k)).smallEtaleTopology
    (ModuleCat.{u + 1} (coefTraceRing l E))).obj (op (etalePoint D.k))).mapIso
      ((Sheaf.restrictScalars (Spec (.of D.k)).smallEtaleTopology
        (coefTraceQuotient l E n)).mapIso
          (Functor.Monoidal.εIso
            (constantSheaf (Spec (.of D.k)).smallEtaleTopology
              (ModuleCat.{u + 1} (finiteDualizingCoeff l E n)))) ≪≫
        (constantCommuteCompose (Spec (.of D.k)).smallEtaleTopology
          (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} (coefTraceQuotient l E n))).app
            (𝟙_ (ModuleCat.{u + 1} (finiteDualizingCoeff l E n)))) ≪≫
    (asIso ((constantSheafAdj (Spec (.of D.k)).smallEtaleTopology
      (ModuleCat.{u + 1} (coefTraceRing l E)) isTerminalEtalePoint).unit.app
        (coefTraceQuotientModule l E n))).symm

/-- Canonical identification of point sections of the coefficient unit with A_n[0].
Source: blueprint proof paragraph 2 (blueprint: lem-coef-tower-trace-rectification). -/
def coefTraceTargetIso (n : ℕ) :
    coefTraceFiniteTarget l E D n ≅
      (DerivedCategory.singleFunctor (ModuleCat.{u + 1} (coefTraceRing l E)) 0).obj
        (coefTraceQuotientModule l E n) :=
  (coefTraceFiniteSections l E D n).mapIso
    (Etale.constantComplexIsoSingleFunctor (finiteDualizingCoeff l E n)
      (Spec (.of D.k))) ≪≫
    (coefTracePointSections l E D).mapIso
      (((Sheaf.restrictScalars (Spec (.of D.k)).smallEtaleTopology
        (coefTraceQuotient l E n)).mapDerivedCategorySingleFunctor 0).app (𝟙_ _)) ≪≫
    (((sheafSections (Spec (.of D.k)).smallEtaleTopology
      (ModuleCat.{u + 1} (coefTraceRing l E))).obj
        (op (etalePoint D.k))).mapDerivedCategorySingleFunctor 0).app _ ≪≫
    (DerivedCategory.singleFunctor (ModuleCat.{u + 1} (coefTraceRing l E)) 0).mapIso
      (coefTraceUnitSectionsIso l E D n)

/-- Linearity of the actual finite quotient for the restricted integral actions.
Source: blueprint proof paragraph 2 (blueprint: lem-coef-tower-trace-rectification).
Proof: expand the restricted scalar actions. Quotient multiplicativity and
coefTraceQuotient_comp identify q(r x) with r q(x), including equal levels. -/
theorem coefTraceQuotient_linear {m n : ℕ} (h : n ≤ m)
    (r : coefTraceRing l E) (x : coefTraceQuotientModule l E m) :
    finiteDualizingQuotient l E h (r • x : coefTraceQuotientModule l E m) =
      r • (finiteDualizingQuotient l E h x : coefTraceQuotientModule l E n) := by
  rcases x with ⟨x⟩
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  rfl

/-- The genuine quotient A_m to A_n as an R-linear map.
Source: blueprint proof paragraph 2 (blueprint: lem-coef-tower-trace-rectification). -/
def coefTraceQuotientMap {m n : ℕ} (h : n ≤ m) :
    coefTraceQuotientModule l E m ⟶ coefTraceQuotientModule l E n :=
  ModuleCat.ofHom (R := coefTraceRing l E)
    (X := coefTraceQuotientModule l E m) (Y := coefTraceQuotientModule l E n)
    { toFun := finiteDualizingQuotient l E h
      map_add' := (finiteDualizingQuotient l E h).map_add
      map_smul' := coefTraceQuotient_linear l E h }

/-- Localization of the given strict quotient-ring complex.
Source: Stacks 0941 (blueprint: lem-coef-tower-trace-rectification). -/
abbrev coefTraceInput
    (Q : CochainComplex (coefficientSequenceModules.{u, u} l E X) ℤ) :
    coefficientSequenceDerived.{u, u} l E X :=
  letI := HasDerivedCategory.standard (coefficientSequenceModules.{u, u} l E X)
  DerivedCategory.Q.obj Q

/-- The compact-support derived tower B_omega, with no inverse limit or test object.
Source: blueprint proof paragraph 2 (blueprint: lem-coef-tower-trace-rectification). -/
def coefTraceDualizingTower
    (Q : CochainComplex (coefficientSequenceModules.{u, u} l E X) ℤ) :
    DerivedCategory (ℕᵒᵖ ⥤ ModuleCat.{u + 1} (coefTraceRing l E)) :=
  (coefTraceCompactSections l E (finiteDualizingCompactification D X)).obj
    (coefTraceInput l E X Q)

end WeilConjectures
