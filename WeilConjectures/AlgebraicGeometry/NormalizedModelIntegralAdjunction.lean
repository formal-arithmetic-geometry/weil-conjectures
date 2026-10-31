/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.IntegralDirectImageTowerData
public import WeilConjectures.AlgebraicGeometry.LocalizingExceptionalAdjoint
public import WeilConjectures.AlgebraicGeometry.SmoothPurityTowerGluing
public import WeilConjectures.AlgebraicGeometry.FiniteFieldFiberSupplement
public import WeilConjectures.AlgebraicGeometry.ProfiniteFiniteConstantLocalModel
public import WeilConjectures.AlgebraicGeometry.PurityFiniteSetting
public import Mathlib.CategoryTheory.Adjunction.Unique

/-! # The normalized model of the integral adjunction

Source: latest blueprint, sec-smooth-purity/sk-prop-sp-integral-adjunction,
statement and proof (blueprint: sk-prop-sp-integral-adjunction).

The integral category is bounded constructible cohomology over the pulled-back
condensed ring of integers. Completeness is not part of its definition. The helpers
only restrict the published functors to full subcategories. The limit is the total
right derived functor of inverse limit after restriction of finite scalar actions.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genCtorIdx false
universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.ProEtale.NormalizedIntegralAdjunction

open IntegralDirectImageTower

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- The original full constructible tower category, before imposing normalization.
Source: the tower adjunction (blueprint: sk-prop-sp-integral-adjunction). -/
abbrev Towers (s : Presentation l E) (T : Scheme.{u}) :=
  spConstructibleTorTowerCategory l E T (s.towers T)

/-- The given compact-support operation on full constructible towers.
Source: the tower adjunction (blueprint: sk-prop-sp-integral-adjunction). -/
def towerSupport (s : Presentation l E) {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f)
    (h : ∀ M : Towers l E s X, spConstructibleTorTowers l E Y (s.towers Y)
      ((towerShriek l E s c).obj M.obj)) : Towers l E s X ⥤ Towers l E s Y :=
  ObjectProperty.lift _
    ((spConstructibleTorTowers l E X (s.towers X)).ι ⋙ towerShriek l E s c) h

/-- Simultaneous derived reduction, retaining every quotient transition.
Source: red_T in the proof (blueprint: sk-prop-sp-integral-adjunction). -/
def reduction (s : Presentation l E) (T : Scheme.{u})
    (h : ∀ K : Constructible l E T, spConstructibleTorTowers l E T (s.towers T)
      ((red l E s T).obj K.obj)) : Constructible l E T ⥤ Towers l E s T :=
  ObjectProperty.lift _
    ((constantModelBoundedConstructible (spIntegralCondensed l E) T).ι ⋙ red l E s T) h

/-- The specified ambient model H = Rlim G red_Y, with finite scalars restricted first.
Source: the displayed definition of H (blueprint: sk-prop-sp-integral-adjunction). -/
def model (s : Presentation l E) {X Y : Scheme.{u}}
    (L : Limit l E s X)
    (hY : ∀ K : Constructible l E Y, spConstructibleTorTowers l E Y (s.towers Y)
      ((red l E s Y).obj K.obj))
    (G : Towers l E s Y ⥤ Towers l E s X) :
    Constructible l E Y ⥤ Integral l E X :=
  reduction l E s Y hY ⋙ G ⋙
    (spConstructibleTorTowers l E X (s.towers X)).ι ⋙ lim l E s X L

/-- Restriction of the very same limit functor, with no choice of its objects or maps.
Source: H takes values in Dbc (blueprint: sk-prop-sp-integral-adjunction). -/
def right (s : Presentation l E) {X Y : Scheme.{u}} (L : Limit l E s X)
    (hY : ∀ K : Constructible l E Y, spConstructibleTorTowers l E Y (s.towers Y)
      ((red l E s Y).obj K.obj))
    (G : Towers l E s Y ⥤ Towers l E s X)
    (h : ∀ K : Constructible l E Y,
      constantModelBoundedConstructible (spIntegralCondensed l E) X
        ((model l E s L hY G).obj K)) : Constructible l E Y ⥤ Constructible l E X :=
  ObjectProperty.lift _ (model l E s L hY G) h

/-- Integral compact support on Dbc is the actual compactification composite.
Source: Rf_! in the adjunction (blueprint: sk-prop-sp-integral-adjunction). -/
def support {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (h : ∀ M : Constructible l E X,
      constantModelBoundedConstructible (spIntegralCondensed l E) Y
        ((shriek l E c).obj M.obj)) : Constructible l E X ⥤ Constructible l E Y :=
  ObjectProperty.lift _
    ((constantModelBoundedConstructible (spIntegralCondensed l E) X).ι ⋙ shriek l E c) h

/-- The full inclusion of bounded constructible integral objects into Loc(Dctf).
Its membership proof is supplied in the conclusion, not assumed of the inputs.
Source: restriction of the Brown adjoint (blueprint: sk-prop-sp-integral-adjunction). -/
def closureInclusion (T : Scheme.{u})
    (h : ∀ K : Constructible l E T,
      localizingClosureProEtale (spIntegralCondensed l E) T K.obj) :
    Constructible l E T ⥤
      (localizingClosureProEtale (spIntegralCondensed l E) T).FullSubcategory :=
  ObjectProperty.lift _
    (constantModelBoundedConstructible (spIntegralCondensed l E) T).ι h

/-- Restriction of the supplied Brown right adjoint, preserving its objects and maps.
Source: f^! in the final sentence (blueprint: sk-prop-sp-integral-adjunction). -/
def brownRestriction {X Y : Scheme.{u}}
    (hY : ∀ K : Constructible l E Y,
      localizingClosureProEtale (spIntegralCondensed l E) Y K.obj)
    (J : (localizingClosureProEtale (spIntegralCondensed l E) Y).FullSubcategory ⥤
      (localizingClosureProEtale (spIntegralCondensed l E) X).FullSubcategory)
    (h : ∀ K : Constructible l E Y,
      constantModelBoundedConstructible (spIntegralCondensed l E) X
        (J.obj ((closureInclusion l E Y hY).obj K)).obj) :
    Constructible l E Y ⥤ Constructible l E X :=
  ObjectProperty.lift _
    (closureInclusion l E Y hY ⋙ J ⋙
      (localizingClosureProEtale (spIntegralCondensed l E) X).ι) h

/-- All clauses of the normalized integral model, including the exact tower counit
and the identification with each supplied Brown right adjoint. Scalar restriction
before total inverse limit is built into `Limit`; no product-limit substitute occurs.
Source: entire statement and proof (blueprint: sk-prop-sp-integral-adjunction). -/
structure Result (s : Presentation l E) {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f)
    (hF : ∀ M : Towers l E s X, spConstructibleTorTowers l E Y (s.towers Y)
      ((towerShriek l E s c).obj M.obj))
    (G : Towers l E s Y ⥤ Towers l E s X) (a : towerSupport l E s c hF ⊣ G) where
  limitX : Limit l E s X
  limitY : Limit l E s Y
  reductionX : ∀ M : Constructible l E X, spConstructibleTorTowers l E X (s.towers X)
    ((red l E s X).obj M.obj)
  reductionY : ∀ K : Constructible l E Y, spConstructibleTorTowers l E Y (s.towers Y)
    ((red l E s Y).obj K.obj)
  normalized : ∀ K : Constructible l E Y,
    IsSpNormalizedTower l E X (s.towers X)
      (G.obj ((reduction l E s Y reductionY).obj K)).obj
  closed : ∀ K : Constructible l E Y,
    constantModelBoundedConstructible (spIntegralCondensed l E) X
      ((model l E s limitX reductionY G).obj K)
  supportClosed : ∀ M : Constructible l E X,
    constantModelBoundedConstructible (spIntegralCondensed l E) Y
      ((shriek l E c).obj M.obj)
  geometry : ReductionGeometry l E s
  openIso : OpenReductionIsIso l E s geometry
  leftComparison : support l E c supportClosed ⋙ reduction l E s Y reductionY ≅
    reduction l E s X reductionX ⋙ towerSupport l E s c hF
  left_normalization : ∀ M : Constructible l E X,
    (leftComparison.hom.app M).hom = towerBaseChange l E s geometry openIso c M.obj
  rightComparison : right l E s limitX reductionY G closed ⋙ reduction l E s X reductionX ≅
    reduction l E s Y reductionY ⋙ G
  right_normalization : ∀ K : Constructible l E Y,
    (rightComparison.hom.app K).hom =
      (redLimitAdjunction l E s X limitX).counit.app
        (G.obj ((reduction l E s Y reductionY).obj K)).obj
  adjunction : support l E c supportClosed ⊣ right l E s limitX reductionY G closed
  unit_reduction : ∀ M : Constructible l E X,
    (reduction l E s X reductionX).map (adjunction.unit.app M) =
      a.unit.app ((reduction l E s X reductionX).obj M) ≫
        G.map (leftComparison.inv.app M) ≫ rightComparison.inv.app _
  counit_reduction : ∀ K : Constructible l E Y,
    (reduction l E s Y reductionY).map (adjunction.counit.app K) =
      leftComparison.hom.app _ ≫ (towerSupport l E s c hF).map
        (rightComparison.hom.app K) ≫ a.counit.app ((reduction l E s Y reductionY).obj K)
  closureX : ∀ M : Constructible l E X,
    localizingClosureProEtale (spIntegralCondensed l E) X M.obj
  closureY : ∀ K : Constructible l E Y,
    localizingClosureProEtale (spIntegralCondensed l E) Y K.obj
  brown : ∀
    (h : ∀ K, localizingClosureProEtale (spIntegralCondensed l E) X K →
      localizingClosureProEtale (spIntegralCondensed l E) Y ((shriek l E c).obj K))
    (J : (localizingClosureProEtale (spIntegralCondensed l E) Y).FullSubcategory ⥤
      (localizingClosureProEtale (spIntegralCondensed l E) X).FullSubcategory)
    (aJ : CondensedRing.localizingLowerShriek (spIntegralCondensed l E) c h ⊣ J),
    ∃ hJ : ∀ K : Constructible l E Y,
        constantModelBoundedConstructible (spIntegralCondensed l E) X
          (J.obj ((closureInclusion l E Y closureY).obj K)).obj,
    ∃ adjJ : support l E c supportClosed ⊣ brownRestriction l E closureY J hJ,
      (∀ K : Constructible l E Y, (adjJ.counit.app K).hom =
        (aJ.counit.app ((closureInclusion l E Y closureY).obj K)).hom) ∧
      ∃! e : right l E s limitX reductionY G closed ≅ brownRestriction l E closureY J hJ,
        ∀ K : Constructible l E Y,
          (support l E c supportClosed).map (e.hom.app K) ≫ adjJ.counit.app K =
            adjunction.counit.app K

/-- The normalized total-limit model is right adjoint to the integral compact-support
functor on bounded constructible complexes, uniquely identified with the Brown restriction.
Source: latest blueprint sk-prop-sp-integral-adjunction, all clauses
(blueprint: sk-prop-sp-integral-adjunction).

Proof, following the six DAG steps:
1. Finite type over the field makes X and Y Noetherian. Integral-models and the
normalized-tower equivalence give fully faithful reductions and reconstruction by
actual total inverse limit. Tower-gamma preserves normalized constructible towers,
so G red_Y K is normalized and its limit is bounded constructible.
2. The compactification direct-image theorem supplies supportClosed and the canonical
whole-tower left comparison, normalized by its actual proper/open mate.
3. Restrict the tower adjunction along the two fully faithful reductions and the two
comparison isomorphisms. This gives the stated integral adjunction and triangles.
4. The restriction formulas are unit_reduction and counit_reduction. Reconstruction
identifies them with inverse limits of the tower unit and counit; evaluation gives
the finite units and counits specified by the tower-geometric theorem.
5. The algebraically closed base has ell-cohomological dimension zero. Existence
restricts every Brown right adjoint to Dctf, which integral-models identifies with
Dbc. Restrict its actual counit and use uniqueness of right adjoints. This gives the
unique isomorphism with exactly the displayed counit equation.
6. The separate determinant bijection theorem supplies the further purity consequence
used in the source proof; it is not added to this proposition's conclusion. -/
theorem normalized_model_integral_adjunction
    (D : WeilConjectures.FiniteFieldDatum.{u}) (_hl : l ≠ D.p)
    {X Y : Scheme.{u}} [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [IsSeparated (X ↘ Spec (.of D.k))] [IsSeparated (Y ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of D.k))] [IsSeparated f]
    (d : ℕ) [SmoothOfRelativeDimension d f] (c : Compactification f)
    (s : Presentation l E)
    (hF : ∀ M : Towers l E s X, spConstructibleTorTowers l E Y (s.towers Y)
      ((towerShriek l E s c).obj M.obj))
    (G : Towers l E s Y ⥤ Towers l E s X) (a : towerSupport l E s c hF ⊣ G) :
    Nonempty (Result l E s c hF G a) := by
  sorry

end AlgebraicGeometry.ProEtale.NormalizedIntegralAdjunction
