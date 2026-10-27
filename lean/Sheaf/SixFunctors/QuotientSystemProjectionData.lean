module

public import Sheaf.SixFunctors.QuotientSystemScalarData

/-! # Normalized coefficient-system projection data

Source: Stacks 06YY, 07A4, 07A6, 0D6D and 0D6E on the small ringed diagram sites
(blueprint: def-sfb-quotient-system-projection-data).

This packages universal coefficient reduction and its canonical tensor/direct-image
comparisons. The predicate records the normalizations; no existence is assumed here.

## Main definitions and statements

* `pullback`: the actual exact coefficient pullback.
* `Lift` and `IsNormalizedLift`: the scalar and right-adjoint comparisons and their equations.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 512
set_option backward.isDefEq.respectTransparency false
universe uC vC uD vD r wY wX wTY wTX wQY wQX wLY wLX
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open scoped CategoryTheory.Obj
open CategoryTheory.CochainPullback CategoryTheory.StrictReduction
namespace CategoryTheory.QuotientProjection
universe o0 v0 o1 v1 o2 v2 o3 v3 o4 v4 o5 v5 o6 v6 o7 v7 o8 v8 o9 v9

/-- Generic categorical comparison data for scalar pullback and its right adjoint.
Keeping the categories as parameters avoids expanding sheaf constructions in projections.
Source: Stacks 0D6D and 0D6E
(blueprint: def-sfb-quotient-system-projection-data). -/
structure ComparisonData
    {A : Type o0} [Category.{v0} A]
    {B : Type o1} [Category.{v1} B]
    {CY : Type o2} [Category.{v2} CY]
    {CX : Type o3} [Category.{v3} CX]
    {DY : Type o4} [Category.{v4} DY]
    {DX : Type o5} [Category.{v5} DX]
    {QY : Type o6} [Category.{v6} QY]
    {QX : Type o7} [Category.{v7} QX]
    {TY : Type o8} [Category.{v8} TY]
    {TX : Type o9} [Category.{v9} TX]
    (OY : A ⥤ CY) (OX : B ⥤ CX) (F : A ⥤ B) (FQ : CY ⥤ CX)
    (SY : DY ⥤ QY) (SX : DX ⥤ QX) (FD : DY ⥤ DX) (FQD : QY ⥤ QX)
    (UY : QY ⥤ TY) (UX : QX ⥤ TX) (RT : TX ⥤ TY) where
  ordinaryTau : OY ⋙ FQ ≅ F ⋙ OX
  tau : SY ⋙ FQD ≅ FD ⋙ SX
  G : QX ⥤ QY
  adj : FQD ⊣ G
  d : G ⋙ UY ≅ UX ⋙ RT

variable {C : Type uC} [Category.{vC} C] [EssentiallySmall.{r} C]
  {D : Type uD} [Category.{vD} D] [EssentiallySmall.{r} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [K.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  {R : Sheaf J CommRingCat.{r}} {S : Sheaf K CommRingCat.{r}}
variable (Q : ℕᵒᵖ ⥤ Modules R) [MonObj Q]
  [HasDerivedCategory.{wY} (Modules R)]
  [HasDerivedCategory.{wTY} (ℕᵒᵖ ⥤ Modules R)]
  [HasDerivedCategory.{wQY} (Systems Q)]

variable (f : RingedPullback R S) [f.L.Monoidal]
  [PreservesFiniteLimits f.L] [PreservesFiniteColimits f.L]

/-- Additivity of the actual termwise pullback, retained as a reusable instance.
Source: Stacks 0D6D (blueprint: def-sfb-quotient-system-projection-data). -/
instance towerPullbackAdditive : (termwise f.L).Additive := inferInstance

/-- Left exactness of the actual termwise pullback.
Source: Stacks 0D6D (blueprint: def-sfb-quotient-system-projection-data). -/
instance towerPullbackLimits : PreservesFiniteLimits (termwise f.L) := inferInstance

/-- Right exactness of the actual termwise pullback.
Source: Stacks 0D6D (blueprint: def-sfb-quotient-system-projection-data). -/
instance towerPullbackColimits : PreservesFiniteColimits (termwise f.L) := inferInstance

/-- The coefficient pullback is induced on internal modules by exact inverse image.
Source: Stacks 07A4 (blueprint: def-sfb-quotient-system-projection-data). -/
abbrev pullback := (termwise f.L).mapMod Q

/-- Additivity of coefficient pullback, retained without repeating its instance proof.
Source: Stacks 07A4 (blueprint: def-sfb-quotient-system-projection-data). -/
instance pullbackAdditive : (pullback Q f).Additive := inferInstance

/-- Left exactness of coefficient pullback.
Source: Stacks 07A4 (blueprint: def-sfb-quotient-system-projection-data). -/
instance pullbackLimits : PreservesFiniteLimits (pullback Q f) := inferInstance

/-- Right exactness of coefficient pullback.
Source: Stacks 07A4 (blueprint: def-sfb-quotient-system-projection-data). -/
instance pullbackColimits : PreservesFiniteColimits (pullback Q f) := inferInstance

/-- Exact pullback commutes with exact restriction of coefficients, via the canonical
localization compositors of the equality of ordinary functors.
Source: Stacks 0D6D (blueprint: def-sfb-quotient-system-projection-data). -/
def pullbackRestriction
    [HasDerivedCategory.{wX} (Modules S)]
    [HasDerivedCategory.{wTX} (ℕᵒᵖ ⥤ Modules S)]
    [HasDerivedCategory.{wQX} (Systems ((termwise f.L).obj Q))] :
    (Mod.forget Q).mapDerivedCategory ⋙ (termwise f.L).mapDerivedCategory ≅
      (pullback Q f).mapDerivedCategory ⋙
        (Mod.forget ((termwise f.L).obj Q)).mapDerivedCategory :=
  (Functor.mapDerivedCategoryCompIso (Mod.forget Q) (termwise f.L)).symm ≪≫
    Functor.mapDerivedCategoryCompIso (pullback Q f) (Mod.forget ((termwise f.L).obj Q))

variable [HasDerivedCategory.{wX} (Modules S)]
  [HasDerivedCategory.{wTX} (ℕᵒᵖ ⥤ Modules S)]
  [HasDerivedCategory.{wQX} (Systems ((termwise f.L).obj Q))]

/-- Data for the coefficient lift. The scalar models are universal derived functors
and pullback is the actual exact functor on module objects. IsNormalizedLift below pins
the ordinary tensor comparison by k.mu and the direct-image comparison by its counit.
The categorical payload uses the generic ComparisonData to keep projections small.
Source: Stacks 07A4, 07A6, 0D6D, 0D6E and 0FPI
(blueprint: def-sfb-quotient-system-projection-data). -/
abbrev Lift (k : Comparison f)
    (MY : RingedModel Q (MonObj.one (X := Q)))
    (MX : RingedModel (Q ⋙ f.L)
      (pulledUnit f.L (moduleUnit f k) Q (MonObj.one (X := Q))))
    [f.V.Additive] (P : AugmentedProjectionDirectImage f.L f.V f.moduleAdj) :=
  Σ Y : ScalarModel Q (MonObj.one (X := Q)) MY,
  Σ X : ScalarModel ((termwise f.L).obj Q)
    (pulledUnit f.L (moduleUnit f k) Q (MonObj.one (X := Q))) MX,
  ComparisonData (scalar Q) (scalar ((termwise f.L).obj Q)) f.L (pullback Q f)
    Y.B X.B f.L.mapDerivedCategory (pullback Q f).mapDerivedCategory
    (Mod.forget Q).mapDerivedCategory
    (Mod.forget ((termwise f.L).obj Q)).mapDerivedCategory P.RT

variable [f.V.Additive] (k : Comparison f)
  (MY : RingedModel Q (MonObj.one (X := Q)))
  (MX : RingedModel (Q ⋙ f.L)
    (pulledUnit f.L (moduleUnit f k) Q (MonObj.one (X := Q))))
  (P : AugmentedProjectionDirectImage f.L f.V f.moduleAdj)

/-- Projection from the coefficient comparison presentation.
Source: Stacks 0D6D and 0D6E
(blueprint: def-sfb-quotient-system-projection-data). -/
abbrev Lift.Y (L : Lift Q f k MY MX P) := L.1

/-- Projection from the coefficient comparison presentation.
Source: Stacks 0D6D and 0D6E
(blueprint: def-sfb-quotient-system-projection-data). -/
abbrev Lift.X (L : Lift Q f k MY MX P) := L.2.1

/-- Projection from the coefficient comparison presentation.
Source: Stacks 0D6D and 0D6E
(blueprint: def-sfb-quotient-system-projection-data). -/
abbrev Lift.ordinaryTau (L : Lift Q f k MY MX P) := L.2.2.ordinaryTau

/-- Projection from the coefficient comparison presentation.
Source: Stacks 0D6D and 0D6E
(blueprint: def-sfb-quotient-system-projection-data). -/
abbrev Lift.tau (L : Lift Q f k MY MX P) := L.2.2.tau

/-- Projection from the coefficient comparison presentation.
Source: Stacks 0D6D and 0D6E
(blueprint: def-sfb-quotient-system-projection-data). -/
abbrev Lift.G (L : Lift Q f k MY MX P) := L.2.2.G

/-- Projection from the coefficient comparison presentation.
Source: Stacks 0D6D and 0D6E
(blueprint: def-sfb-quotient-system-projection-data). -/
abbrev Lift.adj (L : Lift Q f k MY MX P) := L.2.2.adj

/-- Projection from the coefficient comparison presentation.
Source: Stacks 0D6D and 0D6E
(blueprint: def-sfb-quotient-system-projection-data). -/
abbrev Lift.d (L : Lift Q f k MY MX P) := L.2.2.d

/-- Canonical representative and counit normalizations of the lift data.
These are conclusions of the existence assertion, not additional hypotheses on f or Q.
Source: Stacks 07A4, 0D6D, 0D6E and 0FPI
(blueprint: def-sfb-quotient-system-projection-data). -/
def IsNormalizedLift (L : Lift Q f k MY MX P) : Prop :=
  (∀ (M : Modules R) (n : ℕᵒᵖ),
    ((L.ordinaryTau.hom.app M).hom.app n) = (k.mu (Q.obj n) M).hom) ∧
  (∀ (P₀ : CochainComplex (Modules R) ℤ),
    flatRepresentatives R P₀ →
    (pullback Q f).mapDerivedCategory.map (L.Y.counit.app P₀) ≫
        (pullback Q f).mapDerivedCategoryFactors.hom.app
          (((scalar Q).mapHomologicalComplex (.up ℤ)).obj P₀) ≫
        DerivedCategory.Q.map
          ((NatIso.mapHomologicalComplex L.ordinaryTau (.up ℤ)).hom.app P₀) =
      L.tau.hom.app (DerivedCategory.Q.obj P₀) ≫
        L.X.B.map (f.L.mapDerivedCategoryFactors.hom.app P₀) ≫
        L.X.counit.app ((f.L.mapHomologicalComplex (.up ℤ)).obj P₀)) ∧
  (∀ N : DerivedCategory (Systems ((termwise f.L).obj Q)),
    (termwise f.L).mapDerivedCategory.map (L.d.hom.app N) ≫
        P.dT.counit.app ((Mod.forget ((termwise f.L).obj Q)).mapDerivedCategory.obj N) =
      (pullbackRestriction Q f).hom.app (L.G.obj N) ≫
        (Mod.forget ((termwise f.L).obj Q)).mapDerivedCategory.map (L.adj.counit.app N))

end CategoryTheory.QuotientProjection
