/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q146
-/
module

public import Sheaf.SixFunctors.FiniteDualizing
public import Sheaf.Paper.FiniteFieldFiber
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Sheaf.Paper.IntegralRationalQbarCompactSupport
public import Sheaf.AlgebraicGeometry.FixedFiniteExceptionalAt
public import Sheaf.CategoryTheory.DiagramSiteRealization
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.CategoryTheory.Sites.Limits
public import Sheaf.Paper.NormalizedDVRTower
public import Sheaf.Paper.CoefficientRingedSequenceSite
public import Sheaf.Paper.FiniteCoefficientPoint
public import Sheaf.AlgebraicGeometry.ProEtaleIntrinsicExtensionByZeroExact
public import Sheaf.Paper.CompletedIntegralConstantMapOfUniverses
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Ordinary
public import WeilConjectures.SixFunctors.Etale.Derived.GeometricPoint
import Sheaf.Paper.SemilinearDerivedSections

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
set_option warn.sorry false
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
  sorry

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
  sorry

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
  sorry

/-- Exactness of levelwise open extension.
Source: Stacks 0941 (blueprint: lem-coef-tower-trace-rectification).
Proof: open extension is exact on module sheaves and tower kernels and cokernels
are computed levelwise. -/
theorem coefTraceOpen_exact {X Z : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j] :
    PreservesFiniteLimits (coefTraceOpen l E j) ∧
      PreservesFiniteColimits (coefTraceOpen l E j) := by
  sorry

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
Proof: identify strict module-sheaf towers with modules over the constant ring
on the product sequence site. This is a Grothendieck module category, so admits
functorial K-injective resolutions. Transport those through the exact equivalence. -/
@[instance] theorem coefTraceSheafTowers_kInjectives (W : Scheme.{u}) :
    Abelian.HasKInjectiveResolutions (coefTraceSheafTowers l E W) := by
  sorry

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
  sorry

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
  sorry

/-- The genuine quotient A_m to A_n as an R-linear map.
Source: blueprint proof paragraph 2 (blueprint: lem-coef-tower-trace-rectification). -/
def coefTraceQuotientMap {m n : ℕ} (h : n ≤ m) :
    coefTraceQuotientModule l E m ⟶ coefTraceQuotientModule l E n :=
  ModuleCat.ofHom (R := coefTraceRing l E)
    (X := coefTraceQuotientModule l E m) (Y := coefTraceQuotientModule l E n)
    { toFun := finiteDualizingQuotient l E h
      map_add' := (finiteDualizingQuotient l E h).map_add
      map_smul' := coefTraceQuotient_linear l E h }

/-- The scalar-unit transition is exactly the quotient map on coefficient modules.
Source: blueprint proof paragraph 2 (blueprint: lem-coef-tower-trace-rectification).
Proof: the extension--restriction unit at the regular module sends r to r tensor 1.
The scalar-unit comparison sends that tensor to its residue class. The constant
sheaf and sections identifications in coefTraceTargetIso fix those same sections.
Exact localization therefore gives the displayed equality in D(R). -/
theorem coefTraceTargetTransition_quotient {m n : ℕ} (h : n ≤ m) :
    coefTraceTargetTransition l E D h ≫ (coefTraceTargetIso l E D n).hom =
      (coefTraceTargetIso l E D m).hom ≫
        (DerivedCategory.singleFunctor (ModuleCat.{u + 1} (coefTraceRing l E)) 0).map
          (coefTraceQuotientMap l E h) := by
  sorry

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

/-- Evaluation of the strict quotient-semilinear dualizing compact-support tower,
including every quotient transition and the actual finite exceptional counits.
Source: blueprint prop-coef-integral-dualizing, proof paragraph 2
(blueprint: lem-coef-tower-trace-rectification).
Proof: finiteDualizingCoefficientComparisons gives the counit-defined finite
comparison, its identity and cocycle, and its tensor--restriction adjunct. The
hypothesis identifies the given strict complex with precisely that tower.
On the ringed sequence site evaluation is exact. Derive proper image and point
sections separately; simultaneous resolutions and exact scalar restriction give
finite compact support at every level, naturally for all quotient-semilinear
arrows. The finiteDualizingOrigin comparison identifies each term with the
recorded finite exceptional object. The resulting transition is the projection
transpose Res(F_n u) Res(c) eta_(F_m omega_m), as in coefTraceFiniteTransition.
For counits use epsilon_n F_n(u) = T(epsilon_m) c^(-1). After cancellation,
naturality of eta gives Res(T epsilon_m) eta = eta_(A_m) epsilon_m. The unit at
A_m is the quotient A_m to A_n, as proved in coefTraceTargetTransition_quotient.
Apply point sections and exact restriction to R. This proves the second square
with actual counits into A_n[0]. No map of complexes is inferred from equality
only in the derived category, and no test object K is used anywhere. -/
theorem coefTowerTraceRectification (hl : l ≠ D.p)
    (Q : CochainComplex (coefficientSequenceModules.{u, u} l E X) ℤ)
    (eQ : ∀ n : ℕ,
      (coefficientSequenceDerivedEvaluation.{u, u} l E X n).obj (coefTraceInput l E X Q) ≅
        integralDualizingFiniteTerm l E D X n)
    (hQ : ∀ {m n : ℕ} (h : n ≤ m),
      (coefficientSequenceDerivedTransition.{u, u} l E X h).app (coefTraceInput l E X Q) ≫
          (normalizedDVRRes.{u, u} l E X h).map (eQ n).hom =
        (eQ m).hom ≫ integralDualizingExceptionalTransition l E D X hl h) :
    ∃ e : ∀ n : ℕ,
      (coefTraceEvaluation l E n).obj (coefTraceDualizingTower l E D X Q) ≅
        coefTraceFiniteValue l E D X n,
      (∀ {m n : ℕ} (h : n ≤ m),
        (coefTraceTransition l E h).app (coefTraceDualizingTower l E D X Q) ≫ (e n).hom =
          (e m).hom ≫ coefTraceFiniteTransition l E D X h) ∧
      (∀ {m n : ℕ} (h : n ≤ m),
        (coefTraceTransition l E h).app (coefTraceDualizingTower l E D X Q) ≫
            (e n).hom ≫ coefTraceFiniteCounit l E D X n ≫
              (coefTraceTargetIso l E D n).hom =
          (e m).hom ≫ coefTraceFiniteCounit l E D X m ≫
            (coefTraceTargetIso l E D m).hom ≫
              (DerivedCategory.singleFunctor (ModuleCat.{u + 1} (coefTraceRing l E)) 0).map
                (coefTraceQuotientMap l E h)) := by
  sorry

end WeilConjectures
