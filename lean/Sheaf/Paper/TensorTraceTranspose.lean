/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q117
-/
module

public import Sheaf.Paper.CohomologicalSmoothnessComparison
public import Sheaf.AlgebraicGeometry.ProEtaleFiniteModuleIntrinsicComparison
public import Sheaf.Paper.FiniteTorAmplitude
public import Sheaf.AlgebraicGeometry.ProEtaleTorAmplitude
public import Sheaf.Paper.IntrinsicFiniteTorsionConstructibility
public import Sheaf.Paper.SfIntegralConstructible
public import Sheaf.AlgebraicGeometry.ProEtaleCohomologicalSupport
public import Sheaf.Paper.SfDerivedComplete
public import WeilConjectures.SixFunctors.Etale.Derived.TensorStructure
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriekProjection
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.FlatModuleCat
import Sheaf.Paper.CohomologicalSmoothnessFiniteComparison
import Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients
import Sheaf.Paper.DerivedPullbackTensorHom
import Sheaf.Paper.ExchangeProjectionSuppliedDomains

/-!
# Tensoring a trace transpose and the exceptional tensor arrow

Source: blueprint main-20261015, def-pur-co-smoothness, clause 2, and
lem-pur-tensor-trace-transpose, the naturality calculation for the projection map
(blueprint: lem-pur-tensor-trace-transpose).

As in the recorded cohomological-smoothness definition, maps are written in canonical
etale comparison coordinates. Both arbitrary original pro-etale objects and their
representative isomorphisms are retained. The source coefficient is bounded constructible;
only the target coefficient is required to have finite Tor amplitude. The comparison
identifies pullback, tensor, compact supports and the exceptional Hom bijection with their
recorded pro-etale operations. Thus the equality below is the original equality after
these canonical identifications, with no ambient pro-etale adjunction assumed.
-/

@[expose] public section
set_option autoImplicit false
universe u uA
open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace AlgebraicGeometry.Etale

/-- The canonical Koszul symmetry, with its type expressed using derivedTensor.
Source: blueprint def-pur-co-smoothness, tensor ordering
(blueprint: lem-pur-tensor-trace-transpose). -/
noncomputable def tensorTraceSymmetry
    (A : Type uA) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A]
    [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
    [Abelian.HasFunctorialFlatResolution A] (X : Scheme.{u})
    (M N : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)) :
    ((derivedTensor A X).obj M).obj N ≅ ((derivedTensor A X).obj N).obj M :=
  letI := derivedBraidedCategory A X
  β_ M N

/-- The inverse projection map with both tensor symmetries inserted, followed by
1 tensor the trace and the right unit constraint. Its source is f^*K tensor L.
Source: blueprint def-pur-co-smoothness, clause 2; projection naturality calculation
(blueprint: lem-pur-tensor-trace-transpose). -/
noncomputable def tensorTraceProjection
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {V S : Scheme.{u}} (f : V ⟶ S) [HasCompactification f]
    (L : _root_.DerivedCategory (Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (K : _root_.DerivedCategory (Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (t : (rightDerivedLowerShriek (ModuleCat.{u + 1} Λ) f).obj L ⟶ 𝟙_ _) :
    (rightDerivedLowerShriek (ModuleCat.{u + 1} Λ) f).obj
      (((derivedTensor (ModuleCat.{u + 1} Λ) V).obj
        ((upperStar (ModuleCat.{u + 1} Λ) f).leftDerivedFunctor.obj K)).obj L) ⟶ K :=
  (rightDerivedLowerShriek (ModuleCat.{u + 1} Λ) f).map
      (tensorTraceSymmetry (ModuleCat.{u + 1} Λ) V _ L).hom ≫
    inv (((projectionMap (ModuleCat.{u + 1} Λ) f).app L).app K) ≫
    (tensorTraceSymmetry (ModuleCat.{u + 1} Λ) S _ K).hom ≫
    ((derivedTensor (ModuleCat.{u + 1} Λ) S).obj K).map t ≫
    (derivedTensorRightUnitor (ModuleCat.{u + 1} Λ) S K).hom

/-- Theta with the source ordering f^*K tensor omega, using the canonical tensor
mate of the recorded cohomological-smoothness interface and the Koszul symmetry.
Source: blueprint def-pur-co-smoothness, clause 2
(blueprint: lem-pur-tensor-trace-transpose). -/
noncomputable def tensorTraceTheta
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {V S : Scheme.{u}} (f : V ⟶ S) [HasCompactification f]
    (K : _root_.DerivedCategory (Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    ((derivedTensor (ModuleCat.{u + 1} Λ) V).obj
      ((upperStar (ModuleCat.{u + 1} Λ) f).leftDerivedFunctor.obj K)).obj
        (dualizingComplex (ModuleCat.{u + 1} Λ) f) ⟶
      (rightDerivedUpperShriek (ModuleCat.{u + 1} Λ) f).obj K :=
  (tensorTraceSymmetry (ModuleCat.{u + 1} Λ) V _ _).hom ≫
    dualizingComplexTensorMap Λ f K

/-- The exceptional transpose of coefficient integration, before comparison pullback.
Source: blueprint projection naturality calculation and exceptional Hom bijection
(blueprint: lem-pur-tensor-trace-transpose). -/
noncomputable def tensorTraceIntegrated
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {V S : Scheme.{u}} (f : V ⟶ S) [HasCompactification f]
    (L : _root_.DerivedCategory (Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (K : _root_.DerivedCategory (Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (t : (rightDerivedLowerShriek (ModuleCat.{u + 1} Λ) f).obj L ⟶ 𝟙_ _) :
    ((derivedTensor (ModuleCat.{u + 1} Λ) V).obj
      ((upperStar (ModuleCat.{u + 1} Λ) f).leftDerivedFunctor.obj K)).obj L ⟶
        (rightDerivedUpperShriek (ModuleCat.{u + 1} Λ) f).obj K :=
  (rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} Λ) f).homEquiv _ K
    (tensorTraceProjection Λ f L K t)

end AlgebraicGeometry.Etale

namespace AlgebraicGeometry.ProEtale

/-- The canonical coefficient realization, with quotient finiteness supplied internally.
Source: finite purity conventions and def-weil-derived-pullback-tensor-hom
(blueprint: lem-pur-tensor-trace-transpose). -/
noncomputable def tensorTraceRealization
    (P : WeilConjectures.PurityFiniteSetting.{u}) (T : Scheme.{u}) :
    _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology T)
      (ModuleCat.{u + 1} P.Coefficient)) ≌ Scheme.proEtaleDerivedCategory T P.Ring :=
  letI : Finite P.Ring :=
    Padic.finite_coefficientExtensionRing P.coefficients.l P.extension P.level P.level_pos
  letI := (finiteCoefficientIntrinsicRealization_exact T P.Ring).1
  letI : (finiteCoefficientIntrinsicRealization T P.Ring).asEquivalence.functor.Additive :=
    inferInstanceAs (finiteCoefficientIntrinsicRealization T P.Ring).Additive
  (finiteCoefficientIntrinsicRealization T P.Ring).asEquivalence.mapDerivedCategory

/-- Exactly the two projection-invertibility assumptions of the node, in canonical
fixed-scalar coordinates. The dualizing object is the unit-normalized comparison
model already used by the recorded cohomological-smoothness definition.
Source: blueprint def-exchange-projection and def-pur-co-smoothness
(blueprint: lem-pur-tensor-trace-transpose). -/
noncomputable def tensorTraceProjectionDomain
    (P : WeilConjectures.PurityFiniteSetting.{u}) {V S : Scheme.{u}}
    (f : V ⟶ S) (c : Compactification f)
    (L : Scheme.proEtaleDerivedCategory V P.Ring)
    (K : Scheme.proEtaleDerivedCategory S P.Ring) : Prop :=
  letI := c.hasCompactification
  IsIso (((projectionMap (ModuleCat.{u + 1} P.Coefficient) f).app
    ((tensorTraceRealization P V).inverse.obj L)).app
      ((tensorTraceRealization P S).inverse.obj K)) ∧
    IsIso (((projectionMap (ModuleCat.{u + 1} P.Coefficient) f).app
      (comparedDualizing P f)).app ((tensorTraceRealization P S).inverse.obj K))

/-- Tensoring a trace transpose agrees with the exceptional transpose of coefficient
integration, in the canonical comparison coordinates of def-pur-co-smoothness.
Here L and K are the original intrinsic pro-etale objects; eL and eK retain arbitrary
etale representatives. No smoothness, orientation, invertibility of the transpose,
or finite Tor amplitude of L is imposed.
Source: blueprint main-20261015, def-pur-co-smoothness clause 2 and the naturality
calculation in lem-pur-tensor-trace-transpose
(blueprint: lem-pur-tensor-trace-transpose).

Proof:
1. The exceptional Hom bijection identifies the transpose Q of t by the equation
Rf_!(Q) followed by the counit at the unit equals t (def-weil-exceptional-inverse-image).
2. Expand theta as the transpose of the inverse projection map, with the two tensor
symmetries, followed by 1 tensor the unit counit and the unit constraint
(def-pur-co-smoothness). Inverse-transposing (1 tensor Q) followed by theta gives
Rf_!(1 tensor Q) followed by this counit composite.
3. Naturality of projection in its source coefficient, and invertibility of its
components at (L,K) and (omega,K), move Q through the inverse projection map
(def-exchange-projection). Substitute Rf_!(Q) followed by the counit equals t.
The result is precisely tensorTraceProjection, including both symmetries and the unit.
4. Injectivity of the exceptional Hom bijection gives the equality. All factors are
natural in K. Apply the exact comparison pullback and the canonical intrinsic
realization; their pullback, tensor, compact-support and adjunction comparisons
identify this with the asserted pro-etale equation. -/
theorem tensorTraceTranspose
    (P : WeilConjectures.PurityFiniteSetting.{u}) {V S : Scheme.{u}}
    [V.Over (Spec (.of P.field.k))] [S.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (V ↘ Spec (.of P.field.k))]
    [QuasiCompact (V ↘ Spec (.of P.field.k))]
    [IsSeparated (V ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (S ↘ Spec (.of P.field.k))]
    [QuasiCompact (S ↘ Spec (.of P.field.k))]
    [IsSeparated (S ↘ Spec (.of P.field.k))]
    (f : V ⟶ S) [f.IsOver (Spec (.of P.field.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (c : Compactification f)
    (L : Scheme.proEtaleDerivedCategory V P.Ring)
    (K : Scheme.proEtaleDerivedCategory S P.Ring)
    (_hL : Scheme.intrinsicFiniteTorsionConstructible
      P.coefficients.l P.extension P.level P.level_pos V L)
    (_hK : WeilConjectures.finiteTorConstructible
      P.coefficients.l P.extension P.level P.level_pos S K)
    (L₀ : _root_.DerivedCategory
      (Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient)))
    (K₀ : _root_.DerivedCategory
      (Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient)))
    (_eL : (tensorTraceRealization P V).functor.obj
      ((comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) V).mapDerivedCategory.obj L₀) ≅ L)
    (_eK : (tensorTraceRealization P S).functor.obj
      ((comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) S).mapDerivedCategory.obj K₀) ≅ K)
    (_hPF : tensorTraceProjectionDomain P f c L K) :
    letI := c.hasCompactification
    ∀ (t : (Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} P.Coefficient) f).obj L₀ ⟶
        𝟙_ _),
      ((comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) V).mapDerivedCategory ⋙
          (tensorTraceRealization P V).functor).map
        (((Etale.derivedTensor (ModuleCat.{u + 1} P.Coefficient) V).obj
          ((Etale.upperStar (ModuleCat.{u + 1} P.Coefficient) f).leftDerivedFunctor.obj K₀)).map
            ((Etale.rightDerivedUpperShriekAdjunction
              (ModuleCat.{u + 1} P.Coefficient) f).homEquiv L₀ (𝟙_ _) t) ≫
          Etale.tensorTraceTheta P.Coefficient f K₀) =
        ((comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) V).mapDerivedCategory ⋙
          (tensorTraceRealization P V).functor).map
          (Etale.tensorTraceIntegrated P.Coefficient f L₀ K₀ t) ∧
      ∀ (K₁ : _root_.DerivedCategory
          (Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient)))
        (_hK₁ : WeilConjectures.finiteTorConstructible
          P.coefficients.l P.extension P.level P.level_pos S
            ((tensorTraceRealization P S).functor.obj
              ((comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) S).mapDerivedCategory.obj
                K₁)))
        (_hPF₁ : tensorTraceProjectionDomain P f c L
          ((tensorTraceRealization P S).functor.obj
            ((comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) S).mapDerivedCategory.obj
              K₁)))
        (a : K₀ ⟶ K₁),
        ((comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) V).mapDerivedCategory ⋙
          (tensorTraceRealization P V).functor).map
          (Etale.tensorTraceIntegrated P.Coefficient f L₀ K₀ t ≫
            (Etale.rightDerivedUpperShriek (ModuleCat.{u + 1} P.Coefficient) f).map a) =
          ((comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) V).mapDerivedCategory ⋙
          (tensorTraceRealization P V).functor).map
            (((Etale.derivedTensor (ModuleCat.{u + 1} P.Coefficient) V).map
              ((Etale.upperStar (ModuleCat.{u + 1} P.Coefficient) f).leftDerivedFunctor.map
                a)).app L₀ ≫ Etale.tensorTraceIntegrated P.Coefficient f L₀ K₁ t) := by
  sorry

end AlgebraicGeometry.ProEtale
