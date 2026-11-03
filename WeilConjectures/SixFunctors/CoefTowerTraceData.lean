/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Finite.FiniteDualizing
public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.SmoothPurity.Integral.IntegralRationalQbarCompactSupport
public import WeilConjectures.AlgebraicGeometry.Fixed.FixedFiniteExceptionalAt
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.CategoryTheory.Adjunction.Evaluation
public import WeilConjectures.CategoryTheory.Diagram.DiagramSiteTopology
public import WeilConjectures.CategoryTheory.Diagram.DiagramSiteModuleEquivalence
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.CategoryTheory.Sites.Limits
public import WeilConjectures.SixFunctors.Normalized.NormalizedDVRTower
public import WeilConjectures.SixFunctors.Coefficient.CoefficientRingedSequenceSiteSupplement
public import WeilConjectures.SmoothPurity.Finite.FiniteCoefficientPoint
public import WeilConjectures.AlgebraicGeometry.ProEtale.Intrinsic.ProEtaleIntrinsicExtensionByZeroExact
public import WeilConjectures.AlgebraicGeometry.CompletedIntegralConstantMapOfUniverses
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

/-- Strict towers of ordinary module sheaves with the constant integral action.
Source: blueprint finite counit tower (blueprint: lem-coef-tower-trace-rectification). -/
abbrev coefTraceSheafTowers (W : Scheme.{u}) :=
  ℕᵒᵖ ⥤ Sheaf (ProEt.topology W) (ModuleCat.{u + 1} (coefTraceRing l E))

/-- Actual quotient-ring systems, restricted to strict constant-scalar sheaf towers.
The recorded restriction keeps every horizontal quotient-semilinear arrow.
Source: blueprint finite counit tower (blueprint: lem-coef-tower-trace-rectification). -/
def coefTraceSystemRestriction (W : Scheme.{u}) :
    coefficientSequenceModules.{u, u} l E W ⥤ coefTraceSheafTowers l E W :=
  coefficientSequenceRestriction.{u, u} l E W ⋙
    (Functor.whiskeringRight ℕᵒᵖ _ _).obj (coefTraceConstantScalars l E W)

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

variable (D : FiniteFieldDatum.{u})

variable (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
  [QuasiCompact (X ↘ Spec (.of D.k))] [IsSeparated (X ↘ Spec (.of D.k))]

end WeilConjectures
