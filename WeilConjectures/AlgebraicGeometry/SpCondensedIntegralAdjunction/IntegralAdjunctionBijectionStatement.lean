/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.IntegralDirectImageTower.IntegralDirectImageTowerStatement
public import WeilConjectures.AlgebraicGeometry.IntegralDirectImageTower.IntegralComplexesAsNormalizedTowersCurrentStatement
public import WeilConjectures.AlgebraicGeometry.SpTowerGamma.SmoothPurityTowerGammaStatement
public import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicCoefficientTwistsUnrestricted

/-! # The integral adjunction from current condensed coefficient towers

Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/
sec-smooth-purity/sec-sp-grp-ladic-summary/sec-towers-and-integral-coefficients/
sk-prop-sp-integral-adjunction/sk-prop-sp-integral-adjunction-bijection.md and its .proof.md,
Normalization, Bijections and Purity
(blueprint: det-sp-integral-adjunction-bijection).
All integral objects below are ordinary derived internal modules over
`condensedRingObj (spIntegralCondensed l E) T`. Dbc has no completeness condition.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genCtorIdx false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry.Scheme
namespace AlgebraicGeometry.ProEtale.SpCondensedIntegralAdjunction
open IntegralDirectImageTower
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- Use the same coefficient towers and geometric operations as the tower adjunction.
Source: coefficient conventions (blueprint: det-sp-integral-adjunction-bijection). -/
def presentation (b : SpTowerShriek.Base l E) (o : SpTowerShriek.Operations l E b)
    (q : SpTowerCalculus.Coordinates l E b) (ex : SpTowerShriek.OpenExchange l E b o)
    (laws : SpTowerShriek.Laws l E b o ex) : Presentation l E :=
  Presentation.ofOperations l E q.abelian b o ex laws

/-- Restrict actual derived reduction to constructible towers using its output proof.
Source: Normalization (blueprint: det-sp-integral-adjunction-bijection). -/
def reduce (s : Presentation l E) (T : Scheme.{u})
    (h : ∀ K : Constructible l E T,
      spNormalizedConstructibleTorTowers l E T (s.towers T) ((red l E s T).obj K.obj)) :
    Constructible l E T ⥤ (spConstructibleTorTowers l E T (s.towers T)).FullSubcategory :=
  (spConstructibleTorTowers l E T (s.towers T)).lift
    ((constantModelBoundedConstructible (spIntegralCondensed l E) T).ι ⋙ red l E s T)
    (fun K ↦ (h K).1)

/-- Restrict the actual integral compactification composite.
Source: Bijections (blueprint: det-sp-integral-adjunction-bijection). -/
def support {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (h : ∀ M : Constructible l E X,
      constantModelBoundedConstructible (spIntegralCondensed l E) Y
        ((shriek l E c).obj M.obj)) : Constructible l E X ⥤ Constructible l E Y :=
  (constantModelBoundedConstructible (spIntegralCondensed l E) Y).lift
    ((constantModelBoundedConstructible (spIntegralCondensed l E) X).ι ⋙ shriek l E c) h

/-- The specified total inverse limit H = Rlim_X G red_Y, before restricting its range.
Source: Normalization (blueprint: det-sp-integral-adjunction-bijection). -/
def rightAmbient (s : Presentation l E) {X Y : Scheme.{u}} (L : Limit l E s X)
    (hY : ∀ K : Constructible l E Y,
      spNormalizedConstructibleTorTowers l E Y (s.towers Y) ((red l E s Y).obj K.obj))
    (G : (spConstructibleTorTowers l E Y (s.towers Y)).FullSubcategory ⥤
      (spConstructibleTorTowers l E X (s.towers X)).FullSubcategory) :
    Constructible l E Y ⥤ Integral l E X :=
  reduce l E s Y hY ⋙ G ⋙ (spConstructibleTorTowers l E X (s.towers X)).ι ⋙ lim l E s X L

/-- Restrict that total inverse limit using the theorem's constructibility conclusion.
Source: Normalization (blueprint: det-sp-integral-adjunction-bijection). -/
def right (s : Presentation l E) {X Y : Scheme.{u}} (L : Limit l E s X)
    (hY : ∀ K : Constructible l E Y,
      spNormalizedConstructibleTorTowers l E Y (s.towers Y) ((red l E s Y).obj K.obj))
    (G : (spConstructibleTorTowers l E Y (s.towers Y)).FullSubcategory ⥤
      (spConstructibleTorTowers l E X (s.towers X)).FullSubcategory)
    (h : ∀ K : Constructible l E Y,
      constantModelBoundedConstructible (spIntegralCondensed l E) X
        ((rightAmbient l E s L hY G).obj K)) :
    Constructible l E Y ⥤ Constructible l E X :=
  (constantModelBoundedConstructible (spIntegralCondensed l E) X).lift
    (rightAmbient l E s L hY G) h

/-- Ordinary integral derived pullback, followed by the existing Tate twist and shift.
Source: Purity (blueprint: det-sp-integral-adjunction-bijection). -/
def source {X Y : Scheme.{u}} (f : X ⟶ Y) (d : ℕ) :
    Constructible l E Y ⥤ Integral l E X :=
  (constantModelBoundedConstructible (spIntegralCondensed l E) Y).ι ⋙ pull l E f ⋙
    coefficientIntegralTwistFunctor l E X (d : ℤ) ⋙ shiftFunctor _ (2 * (d : ℤ))

/-- The displayed three bijections, with their canonical comparison directions.
Source: Bijections (blueprint: det-sp-integral-adjunction-bijection). -/
def homChain {X Y : Scheme.{u}} {CX CY : Type (u + 2)}
    [Category.{u + 2} CX] [Category.{u + 2} CY]
    (F : Constructible l E X ⥤ Constructible l E Y)
    (H : Constructible l E Y ⥤ Constructible l E X)
    (rX : Constructible l E X ⥤ CX) (rY : Constructible l E Y ⥤ CY)
    (iX : rX.FullyFaithful) (iY : rY.FullyFaithful)
    (Ft : CX ⥤ CY) (Gt : CY ⥤ CX) (a : Ft ⊣ Gt)
    (β : F ⋙ rY ≅ rX ⋙ Ft) (χ : H ⋙ rX ≅ rY ⋙ Gt)
    (M : Constructible l E X) (K : Constructible l E Y) :
    (F.obj M ⟶ K) ≃ (M ⟶ H.obj K) :=
  iY.homEquiv.trans
    ((Iso.homCongr (β.app M) (Iso.refl _)).trans
      ((a.homEquiv _ _).trans
        ((Iso.homCongr (Iso.refl _) (χ.app K).symm).trans iX.homEquiv.symm)))

/-- The actual completion unit, packaged as an isomorphism only after invertibility.
Source: Bijections (blueprint: det-sp-integral-adjunction-bijection). -/
def completionIso (s : Presentation l E) (T : Scheme.{u}) (L : Limit l E s T)
    (M : Constructible l E T)
    (h : IsIso ((redLimitAdjunction l E s T L).unit.app M.obj)) :=
  letI := h
  asIso ((redLimitAdjunction l E s T L).unit.app M.obj)

variable (b : SpTowerShriek.Base l E) (o : SpTowerShriek.Operations l E b)
  (q : SpTowerCalculus.Coordinates l E b) (ex : SpTowerShriek.OpenExchange l E b o)
  (laws : SpTowerShriek.Laws l E b o ex)

set_option maxHeartbeats 1600000 in
-- The dependent unit, counit and finite-level formulas share the full realization data.
end AlgebraicGeometry.ProEtale.SpCondensedIntegralAdjunction
