/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Cohomological.CohomologicalSmoothnessComparison
public import WeilConjectures.AlgebraicGeometry.ProEtale.Finite.ProEtaleFiniteModuleIntrinsicComparison
public import WeilConjectures.SixFunctors.Finite.FiniteTorAmplitude
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriekProjection
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.FlatModuleCat

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
  letI := _root_.DerivedCategory.braidedCategory' (Sheaf X.smallEtaleTopology A)
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
        (dualizingComplex Λ f) ⟶
      (rightDerivedUpperShriek Λ f).obj K :=
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
        (rightDerivedUpperShriek Λ f).obj K :=
  (rightDerivedUpperShriekAdjunction Λ f).homEquiv _ K
    (tensorTraceProjection Λ f L K t)

-- Keep the mate calculation abstract so rewriting does not unfold derived tensor.
end AlgebraicGeometry.Etale

namespace AlgebraicGeometry.ProEtale

end AlgebraicGeometry.ProEtale
