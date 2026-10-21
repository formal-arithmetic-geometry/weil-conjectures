/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P4
-/
module

public import Sheaf.AlgebraicGeometry.ProEtaleProjectiveLineTraceSystem
public import Sheaf.AlgebraicGeometry.CartierDerivedRealization
public import Sheaf.AlgebraicGeometry.ProjectiveLineDiagonalIntegrals
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerStarComp

/-! # Canonical maps in the pro-etale diagonal component calculation -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u uC vC wC uD vD wD
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
namespace AlgebraicGeometry.ProEtale

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [local irreducible] DerivedCategory HasDerivedCategory.ofIsGrothendieckAbelian
  HasDerivedCategory.ofHasKInjectiveResolutions Functor.rightDerivedFunctor
  Functor.mapDerivedCategory AlgebraicGeometry.ProjectiveSpace
  Etale.projectiveLineTraceTransport Etale.projectiveLineTraceDatum

/-- Exact comparison of the supported and Cartier Ext classes.
Source: det-sp-p1-trace, clause 3
(blueprint: lem-sp-p1-diagonal-comparison-components). -/
def SpP1CartierCompatibility {C : Type uC} [Category.{vC} C] [Abelian C]
    [HasExt.{wC} C] {D : Type uD} [Category.{vD} D] [Abelian D] [HasExt.{wD} D]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    {X L : C} {Y : D} (σ : F.obj X ⟶ Y) (κ : Ext X L 2) (c : Ext Y (F.obj L) 2) :
    Prop := (Ext.mk₀ σ).comp c (zero_add 2) = κ.mapExactFunctor F

/-- The composition isomorphism for a projection after the diagonal.
Source: det-sp-p1-trace, proof paragraph 3. -/
@[irreducible]
def geoP1DiagonalSourceIso (A : Type (u + 1)) [CommRing A] (S : Scheme.{u}) :
    ∀ a : Bool, geoP1Unit A (ProjectiveLine S) ≅
      (geoP1Pushforward A (Etale.projectiveLineDiagonalProjection S a)).obj
        ((geoP1Pushforward A (pullback.diagonal (ProjectiveLine S ↘ S))).obj
          (geoP1Unit A (ProjectiveLine S)))
  | false =>
      (((rightDerivedLowerStarFactor (ModuleCat.{u + 1} A)
          (pullback.diagonal_fst (ProjectiveLine S ↘ S))) ≪≫
        rightDerivedLowerStarId (ModuleCat.{u + 1} A) (ProjectiveLine S)).symm).app
          (geoP1Unit A (ProjectiveLine S))
  | true =>
      (((rightDerivedLowerStarFactor (ModuleCat.{u + 1} A)
          (pullback.diagonal_snd (ProjectiveLine S ↘ S))) ≪≫
        rightDerivedLowerStarId (ModuleCat.{u + 1} A) (ProjectiveLine S)).symm).app
          (geoP1Unit A (ProjectiveLine S))

/-- The canonical source arrow of the diagonal integral.
Source: det-sp-p1-trace, proof paragraph 3. -/
@[irreducible]
def geoP1DiagonalSource (A : Type (u + 1)) [CommRing A] (S : Scheme.{u}) (a : Bool) :=
  (geoP1DiagonalSourceIso A S a).hom

/-- Both canonical source identifications are invertible.
Source: det-sp-p1-trace, proof paragraph 3. -/
theorem geoP1DiagonalSource_isIso (A : Type (u + 1)) [CommRing A]
    (S : Scheme.{u}) (a : Bool) : IsIso (geoP1DiagonalSource A S a) := by
  unfold geoP1DiagonalSource
  infer_instance

/-- Realize a supported Ext class using specified source and target comparisons.
Source: det-sp-p1-trace, proof paragraph 3, exact derived realization. -/
@[irreducible]
def cartierDerivedArrow {C : Type uC} [Category.{vC} C] [Abelian C]
    [HasDerivedCategory.{wC} C] [HasKInjectiveResolutions C]
    {D : Type uD} [Category.{vD} D] [Abelian D] [HasDerivedCategory.{wD} D]
    [HasExt.{wD} D] (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F]
    [PreservesFiniteColimits F] (X : C) (Y : D)
    {Z : DerivedCategory C} {W : DerivedCategory D}
    (s : Z ≅ (DerivedCategory.singleFunctor C 0).obj X)
    (t : W ≅ ((DerivedCategory.singleFunctor D 0).obj Y)⟦(2 : ℤ)⟧)
    (c : Ext (F.obj X) Y 2) : F.rightDerivedFunctor.obj Z ⟶ W :=
  F.rightDerivedFunctor.map s.hom ≫ Etale.supportedExactDerivedMap F X Y c ≫ t.inv

/-- The exact-direct-image realization of the specified Cartier class.
Source: det-sp-p1-trace, proof paragraph 3. -/
@[irreducible]
def geoP1CartierDerivedArrow (A : Type (u + 1)) [CommRing A] (N : ℕ)
    (hA : (N : A) = 0) {D T : Scheme.{u}} (i : D ⟶ T)
    [PreservesFiniteColimits (lowerStar (ModuleCat.{u + 1} A) i)]
    (c : GeoCartierClass A N hA i) :=
  cartierDerivedArrow (lowerStar (ModuleCat.{u + 1} A) i)
    (geoCartierConstant A D) (geoCartierLine A N hA T) (cartierUnitSingleIso A D)
    (cartierShiftSingleIso (comparisonUpperStar (ModuleCat.{u + 1} A) T)
      (Scheme.finiteEtaleTateLine T N A hA)) c

/-- The canonical chart comparison, before applying the projective-line trace.
Source: det-sp-p1-trace, proof paragraph 3. -/
@[irreducible]
def geoP1DiagonalChartMap (A : Type (u + 1)) [CommRing A] (N : ℕ)
    (hN : 0 < N) (hA : (N : A) = 0) (S : Scheme.{u})
    (hS : IsUnit (N : Γ(S, ⊤))) (a : Bool) :=
  (geoP1Pushforward A (Etale.projectiveLineDiagonalProjection S a)).map
      ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A)
        (Etale.projectiveLineDiagonalChart S a).val.hom).unit.app
          (geoP1Twist A N hA
            (pullback (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S)) 1 2)) ≫
              (rightDerivedLowerStarFactor (ModuleCat.{u + 1} A)
                (Etale.projectiveLineDiagonalChart S a).property).hom.app
                  ((geoP1Pullback A (Etale.projectiveLineDiagonalChart S a).val.hom).obj
                    (geoP1Twist A N hA
                      (pullback (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S)) 1 2)) ≫
              (geoP1Pushforward A (ProjectiveLine (ProjectiveLine S) ↘ ProjectiveLine S)).map
                (geoP1TwistPullback A N hN hA (Etale.projectiveLineDiagonalChart S a).val.hom
                  ((map_natCast ((pullback.fst (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S)) ≫
                    (ProjectiveLine S ↘ S)).appTop.hom N) ▸
                      hS.map ((pullback.fst (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S)) ≫
                        (ProjectiveLine S ↘ S)).appTop.hom) 1 2).hom

/-- The canonical maps of a supported diagonal before its trace.
Source: det-sp-p1-trace, proof paragraph 3. -/
structure DiagonalKernelData (C : Type uC) [Category.{vC} C]
    (D : Type uD) [Category.{vD} D] where
  unit : C
  supported : D
  twist : D
  target : C
  push : Bool → D ⥤ C
  sourceType : Type vC
  source : sourceType
  diagonalType : Type vD
  diagonal : diagonalType
  chartType : Type vC
  chart : chartType

/-- Typed representatives of the exact canonical kernel maps.
HEq fixes every representative uniquely; the source is already an isomorphism.
Source: det-sp-p1-trace, clause 3. -/
structure DiagonalKernelRealization {C : Type uC} [Category.{vC} C]
    {D : Type uD} [Category.{vD} D] (d : DiagonalKernelData C D) where
  source : ∀ a, d.unit ≅ (d.push a).obj d.supported
  diagonal : d.supported ⟶ d.twist
  chart : ∀ a, (d.push a).obj d.twist ⟶ d.target
  source_eq : HEq d.source source
  diagonal_eq : HEq d.diagonal diagonal
  chart_eq : HEq d.chart chart

/-- The additional unit and Chern components of a diagonal kernel.
Source: det-sp-p1-trace, proof paragraph 3. -/
structure DiagonalComponentData (C : Type uC) [Category.{vC} C]
    (D : Type uD) [Category.{vD} D] extends DiagonalKernelData C D where
  line : C
  unitType : Type vC
  unitMap : unitType
  chernType : Type vC
  chernMap : chernType

/-- Both canonical source maps are invertible and both diagonal integrals are one.
Source: det-sp-p1-trace, clause 3. -/
def DiagonalIntegralFormula {C : Type uC} [Category.{vC} C]
    {D : Type uD} [Category.{vD} D] (d : DiagonalKernelData C D)
    (trace : d.target ⟶ d.unit) : Prop :=
  ∃ v : DiagonalKernelRealization d, ∀ a,
    (v.source a).hom ≫ (d.push a).map v.diagonal ≫ v.chart a ≫ trace = 𝟙 d.unit

/-- Transport a specified trace to the kernel's Hom type, retaining its exact value.
The witness is unique because its equality to the supplied trace is required.
Source: det-sp-p1-trace, clause 3. -/
def DiagonalIntegralCondition {C : Type uC} [Category.{vC} C]
    {D : Type uD} [Category.{vD} D] (d : DiagonalKernelData C D)
    {traceType : Type vC} (trace : traceType) : Prop :=
  ∃ t : d.target ⟶ d.unit, HEq trace t ∧ DiagonalIntegralFormula d t

/-- A supported diagonal decomposes into its base term and relative Chern term.
Source: det-sp-p1-trace, proof paragraph 3. -/
def DiagonalComponentFormula {C : Type uC} [Category.{vC} C] [Preadditive C]
    {D : Type uD} [Category.{vD} D] (d : DiagonalComponentData C D) : Prop :=
  ∃ v : DiagonalKernelRealization d.toDiagonalKernelData,
    ∃ (unitMap : d.line ⟶ d.target) (chernMap : d.unit ⟶ d.target),
      HEq d.unitMap unitMap ∧ HEq d.chernMap chernMap ∧
      ∀ a : Bool, ∃ β : d.unit ⟶ d.line,
        (v.source a).hom ≫ (d.push a).map v.diagonal ≫ v.chart a =
          β ≫ unitMap + chernMap

/-- The literal source, Cartier realization and chart maps of the diagonal.
Source: det-sp-p1-trace, proof paragraph 3. -/
def geoP1DiagonalKernelData (A : Type (u + 1)) [CommRing A] (N : ℕ)
    (hN : 0 < N) (hA : (N : A) = 0) (S : Scheme.{u})
    (hS : IsUnit (N : Γ(S, ⊤)))
    [PreservesFiniteColimits
      (lowerStar (ModuleCat.{u + 1} A) (pullback.diagonal (ProjectiveLine S ↘ S)))]
    (cΔ : GeoCartierClass A N hA (pullback.diagonal (ProjectiveLine S ↘ S))) :
    DiagonalKernelData
      (DerivedCategory (Sheaf (Scheme.ProEt.topology (ProjectiveLine S))
        (ModuleCat.{u + 1} A)))
      (DerivedCategory (Sheaf (Scheme.ProEt.topology
        (pullback (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S))) (ModuleCat.{u + 1} A))) where
  unit := geoP1Unit A (ProjectiveLine S)
  supported := (geoP1Pushforward A (pullback.diagonal (ProjectiveLine S ↘ S))).obj
    (geoP1Unit A (ProjectiveLine S))
  twist := geoP1Twist A N hA
    (pullback (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S)) 1 2
  target := (geoP1Pushforward A (ProjectiveLine (ProjectiveLine S) ↘ ProjectiveLine S)).obj
    (geoP1Twist A N hA (ProjectiveLine (ProjectiveLine S)) 1 2)
  push := fun a ↦ geoP1Pushforward A (Etale.projectiveLineDiagonalProjection S a)
  sourceType := _
  source := geoP1DiagonalSourceIso A S
  diagonalType := _
  diagonal := geoP1CartierDerivedArrow A N hA (pullback.diagonal (ProjectiveLine S ↘ S)) cΔ
  chartType := _
  chart := geoP1DiagonalChartMap A N hN hA S hS

/-- The literal canonical maps, shared by the component predicate.
Source: det-sp-p1-trace, proof paragraph 3. -/
def geoP1DiagonalComponentData (A : Type (u + 1)) [CommRing A] [Finite A] (N : ℕ)
    (hN : 0 < N) (hA : (N : A) = 0) (S : Scheme.{u})
    (hS : IsUnit (N : Γ(S, ⊤)))
    (c : Etale.ordinaryFiniteUnit A (ProjectiveLine (ProjectiveLine S)) ⟶
      (Etale.ordinaryFiniteLine A N hA (ProjectiveLine (ProjectiveLine S)))⟦(2 : ℤ)⟧)
    [PreservesFiniteColimits
      (lowerStar (ModuleCat.{u + 1} A) (pullback.diagonal (ProjectiveLine S ↘ S)))]
    (cΔ : GeoCartierClass A N hA (pullback.diagonal (ProjectiveLine S ↘ S))) :
    DiagonalComponentData
      (DerivedCategory (Sheaf (Scheme.ProEt.topology (ProjectiveLine S))
        (ModuleCat.{u + 1} A)))
      (DerivedCategory (Sheaf (Scheme.ProEt.topology
        (pullback (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S))) (ModuleCat.{u + 1} A))) where
  toDiagonalKernelData := geoP1DiagonalKernelData A N hN hA S hS cΔ
  line := geoP1Twist A N hA (ProjectiveLine S) 1 2
  unitType := _
  unitMap := geoP1TwistedUnit A N hN hA (ProjectiveLine S)
    ((map_natCast (ProjectiveLine S ↘ S).appTop.hom N) ▸
      hS.map (ProjectiveLine S ↘ S).appTop.hom)
  chernType := _
  chernMap := geoP1ChernPushforward A N hA (ProjectiveLine S) c

set_option linter.unusedVariables false in
/-- Comparison carries the supported diagonal class to a base component plus the
normalized relative Chern component. No trace or twisted splitting is assumed.
Source: det-sp-p1-trace, proof paragraph 3; the ordinary component identity of
lem-sp-finite-p1-diagonal-kummer-component-formula.
(blueprint: lem-sp-p1-diagonal-comparison-components)

Proof: realize the equality of Ext classes through Ext.homEquiv and the exact
comparison functor. Its source comparison is the canonical closed direct-image
mate composed with the constant-sheaf identification. Exactness of closed direct
image identifies this realization with geoP1CartierDerivedArrow. The mate of a
pasted inverse-image square is the paste of the mates; apply this to the diagonal
followed by either projection. This identifies the image of the ordinary alpha
with geoP1DiagonalSource followed by the two direct-image comparisons. Apply the
same pasting identity to the projective-line chart, and the normalized twist
pullback identity to its coefficient object. It identifies the ordinary chart
comparison with geoP1DiagonalChartMap after those direct-image comparisons.
Now apply exact comparison to the ordinary component formula for the supported
Kummer class, which is beta times the shifted twisted unit plus the relative
O(1) Chern pushforward. Additivity preserves its sum; the unit and Chern mate
identities identify the two resulting components with the displayed canonical
pro-etale arrows. The image of beta is the witness. Closed-source comparison is
invertible, so its cancellation gives the claimed formula. All classes retain
their Kummer sign. Empty bases and zero coefficients give the unique zero arrows. -/
theorem geoP1_diagonal_comparison_components
    (A : Type (u + 1)) [CommRing A] [Finite A] (N : ℕ) (hN : 0 < N)
    (hA : (N : A) = 0) (S : Scheme.{u}) [IsNoetherian S]
    (hS : IsUnit (N : Γ(S, ⊤)))
    (c : Etale.ordinaryFiniteUnit A (ProjectiveLine (ProjectiveLine S)) ⟶
      (Etale.ordinaryFiniteLine A N hA (ProjectiveLine (ProjectiveLine S)))⟦(2 : ℤ)⟧)
    (hc : Etale.ordinaryFiniteP1ChernSpec A N hA (ProjectiveLine S)
      ((map_natCast (ProjectiveLine (ProjectiveLine S) ↘ ProjectiveLine S).appTop.hom N) ▸
        ((map_natCast (ProjectiveLine S ↘ S).appTop.hom N) ▸
          hS.map (ProjectiveLine S ↘ S).appTop.hom).map
            (ProjectiveLine (ProjectiveLine S) ↘ ProjectiveLine S).appTop.hom) c)
    (hI : (pullback.diagonal (ProjectiveLine S ↘ S)).ker.IsInvertible)
    (κ : Ext
      ((Etale.lowerStar (ModuleCat.{u + 1} A) (pullback.diagonal (ProjectiveLine S ↘ S))).obj
        (Etale.ordinaryFiniteConstant A (ProjectiveLine S)))
      (Scheme.finiteEtaleTateLine
        (pullback (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S)) N A hA) 2)
    (hκ : Etale.SupportedKummerBoundary A N hA
      (pullback.diagonal (ProjectiveLine S ↘ S)) hI
      ((map_natCast ((pullback.fst (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S)) ≫
        (ProjectiveLine S ↘ S)).appTop.hom N) ▸
          hS.map ((pullback.fst (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S)) ≫
            (ProjectiveLine S ↘ S)).appTop.hom) κ)
    (cΔ : GeoCartierClass A N hA (pullback.diagonal (ProjectiveLine S ↘ S)))
    [hE : PreservesFiniteColimits
      (lowerStar (ModuleCat.{u + 1} A) (pullback.diagonal (ProjectiveLine S ↘ S)))]
    (hcompat : SpP1CartierCompatibility
      (comparisonUpperStar (ModuleCat.{u + 1} A)
        (pullback (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S)))
      (geoCartierSourceComparison A (pullback.diagonal (ProjectiveLine S ↘ S))) κ cΔ) :
    DiagonalComponentFormula (geoP1DiagonalComponentData A N hN hA S hS c cΔ) := by
  sorry

end AlgebraicGeometry.ProEtale
