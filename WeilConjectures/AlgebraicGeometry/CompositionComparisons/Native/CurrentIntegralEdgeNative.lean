/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.IntegralDirectImageTower.Current.IntegralTowerImageReconstructionCurrent

/-!
# Native integral realization of a smooth tower adjunction

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/sk-prop-sp-composition/
sk-prop-sp-composition-comparisons.proof.md, (3), final sentence; expanded by
sk-prop-sp-integral-adjunction/sk-prop-sp-integral-adjunction.proof.md, first paragraph
and displayed Hom chain (blueprint: lem-sp-current-composition-integral-edge).

All categories are the existing full subcategories of ordinary derived categories.
The right functor is the actual scalar-restricted total derived limit of G red.
The comparisons are specified as whole-tower arrows before finite evaluation.
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
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.ProEtale.CompositionComparisons.Native

open IntegralDirectImageTower.Current

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- The existing uniformly constructible finite-Tor full tower category.
Source: comparisons (3), tower adjunction
(blueprint: lem-sp-current-composition-integral-edge). -/
abbrev Towers (s : Coefficients l E) (T : Scheme.{u}) :=
  spConstructibleTorTowerCategory l E T (s.towers T)

/-- The restriction of the specified whole-tower compact-support functor.
Source: comparisons (3), supplied tower adjunction
(blueprint: lem-sp-current-composition-integral-edge). -/
def towerSupport (s : Coefficients l E) {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f)
    (hF : ∀ M : Towers l E s X, spConstructibleTorTowers l E Y (s.towers Y)
      ((towerShriek l E s c).obj M.obj)) : Towers l E s X ⥤ Towers l E s Y :=
  ObjectProperty.lift _
    ((spConstructibleTorTowers l E X (s.towers X)).ι ⋙ towerShriek l E s c) hF

/-- Full faithfulness, exact normalized image, and the actual inverse with its
reduction/limit unit and counit. No completeness is imposed on the source category.
Source: comparisons (3), normalized integral realization; sk-lem-sp-tower
(blueprint: lem-sp-current-composition-integral-edge). -/
structure ReductionRealization (s : Coefficients l E)
    (A : ∀ T : Scheme.{u}, DerivedLimit l E s T) (T : Scheme.{u}) where
  normalized : ∀ M : Constructible l E T,
    spNormalizedConstructibleTorTowers l E T (s.towers T) ((red l E s T).obj M.obj)
  fullyFaithful :
    ((constantModelBoundedConstructible (spIntegralCondensed l E) T).ι ⋙
      red l E s T).FullyFaithful
  image : ∀ C : spDerivedCoefficientTowers l E T (s.towers T),
    spNormalizedConstructibleTorTowers l E T (s.towers T) C ↔
      ∃ M : Constructible l E T, Nonempty ((red l E s T).obj M.obj ≅ C)
  limitClosed : ∀ C : spDerivedCoefficientTowers l E T (s.towers T),
    spNormalizedConstructibleTorTowers l E T (s.towers T) C →
      constantModelBoundedConstructible (spIntegralCondensed l E) T
        ((limit l E s A T).obj C)
  unitIsIso : ∀ M : Constructible l E T,
    IsIso ((adjunction l E s A T).unit.app M.obj)
  counitIsIso : ∀ C : spDerivedCoefficientTowers l E T (s.towers T),
    spNormalizedConstructibleTorTowers l E T (s.towers T) C →
      IsIso ((adjunction l E s A T).counit.app C)

/-- Restrict the canonical reduction using its proved normalized-image assertion.
Source: integral-adjunction Hom chain
(blueprint: lem-sp-current-composition-integral-edge). -/
def reduction (s : Coefficients l E)
    (A : ∀ T : Scheme.{u}, DerivedLimit l E s T) (T : Scheme.{u})
    (r : ReductionRealization l E s A T) : Constructible l E T ⥤ Towers l E s T :=
  ObjectProperty.lift _
    ((constantModelBoundedConstructible (spIntegralCondensed l E) T).ι ⋙ red l E s T)
    (fun M ↦ (r.normalized M).1)

/-- The actual integral compact-support functor restricted to Dbc.
Source: integral-adjunction Hom chain
(blueprint: lem-sp-current-composition-integral-edge). -/
def support {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (hF : ∀ M : Constructible l E X,
      constantModelBoundedConstructible (spIntegralCondensed l E) Y
        ((shriek l E c).obj M.obj)) : Constructible l E X ⥤ Constructible l E Y :=
  ObjectProperty.lift _
    ((constantModelBoundedConstructible (spIntegralCondensed l E) X).ι ⋙ shriek l E c) hF

/-- The actual total-limit composite, with finite scalar actions restricted first.
Source: integral-adjunction, definition of H
(blueprint: lem-sp-current-composition-integral-edge). -/
def model (s : Coefficients l E)
    (A : ∀ T : Scheme.{u}, DerivedLimit l E s T) {X Y : Scheme.{u}}
    (rY : ReductionRealization l E s A Y)
    (G : Towers l E s Y ⥤ Towers l E s X) : Constructible l E Y ⥤ Integral l E X :=
  reduction l E s A Y rY ⋙ G ⋙
    (spConstructibleTorTowers l E X (s.towers X)).ι ⋙ limit l E s A X

/-- Restriction of the same total-limit composite to constructible objects.
Source: integral-adjunction, definition of H
(blueprint: lem-sp-current-composition-integral-edge). -/
def right (s : Coefficients l E)
    (A : ∀ T : Scheme.{u}, DerivedLimit l E s T) {X Y : Scheme.{u}}
    (rY : ReductionRealization l E s A Y)
    (G : Towers l E s Y ⥤ Towers l E s X)
    (h : ∀ K : Constructible l E Y,
      constantModelBoundedConstructible (spIntegralCondensed l E) X
        ((model l E s A rY G).obj K)) : Constructible l E Y ⥤ Constructible l E X :=
  ObjectProperty.lift _ (model l E s A rY G) h

/-- The clauses of the native realization, retaining the specified reconstruction
transpose, proper/open mate, actual reduction/limit counit, and both adjunction equations.
Source: comparisons (3), integral realization; integral-adjunction Hom chain
(blueprint: lem-sp-current-composition-integral-edge). -/
structure Edge (s : Coefficients l E) (q : ScalarCompatibility l E s)
    (hq : OpenScalarIsIso l E s q) (A : ∀ T : Scheme.{u}, DerivedLimit l E s T)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (hF : ∀ M : Towers l E s X, spConstructibleTorTowers l E Y (s.towers Y)
      ((towerShriek l E s c).obj M.obj))
    (G : Towers l E s Y ⥤ Towers l E s X) (a : towerSupport l E s c hF ⊣ G) where
  realizationX : ReductionRealization l E s A X
  realizationY : ReductionRealization l E s A Y
  normalized : ∀ K : Constructible l E Y,
    IsSpNormalizedTower l E X (s.towers X)
      (G.obj ((reduction l E s A Y realizationY).obj K)).obj
  closed : ∀ K : Constructible l E Y,
    constantModelBoundedConstructible (spIntegralCondensed l E) X
      ((model l E s A realizationY G).obj K)
  supportClosed : ∀ M : Constructible l E X,
    constantModelBoundedConstructible (spIntegralCondensed l E) Y
      ((shriek l E c).obj M.obj)
  reconstructionIsIso : ∀ M : Constructible l E X,
    IsIso (reconstruction l E s q hq A c M.obj)
  leftComparison : support l E c supportClosed ⋙ reduction l E s A Y realizationY ≅
    reduction l E s A X realizationX ⋙ towerSupport l E s c hF
  left_transpose : ∀ M : Constructible l E X,
    (leftComparison.hom.app M).hom = towerComparison l E s q hq A c M.obj
  left_mate : ∀ M : Constructible l E X,
    (leftComparison.hom.app M).hom = towerBaseChange l E s q hq c M.obj
  left_finite : ∀ (M : Constructible l E X) (n : ℕ),
    (spDerivedCoefficientEvaluation l E Y (s.towers Y) n).map
        (leftComparison.hom.app M).hom ≫
      (finiteComparison l E s q.evaluation c n).hom.app ((red l E s X).obj M.obj) =
        finiteBaseChange l E s q hq c M.obj n
  rightComparison : right l E s A realizationY G closed ⋙
      reduction l E s A X realizationX ≅ reduction l E s A Y realizationY ⋙ G
  right_counit : ∀ K : Constructible l E Y,
    (rightComparison.hom.app K).hom = (adjunction l E s A X).counit.app
      (G.obj ((reduction l E s A Y realizationY).obj K)).obj
  integralAdjunction : support l E c supportClosed ⊣ right l E s A realizationY G closed
  unit_reduction : ∀ M : Constructible l E X,
    (reduction l E s A X realizationX).map (integralAdjunction.unit.app M) =
      a.unit.app ((reduction l E s A X realizationX).obj M) ≫
        G.map (leftComparison.inv.app M) ≫ rightComparison.inv.app _
  counit_reduction : ∀ K : Constructible l E Y,
    (reduction l E s A Y realizationY).map (integralAdjunction.counit.app K) =
      leftComparison.hom.app _ ≫ (towerSupport l E s c hF).map
        (rightComparison.hom.app K) ≫
          a.counit.app ((reduction l E s A Y realizationY).obj K)

/-- A supplied smooth tower adjunction has the native integral realization specified
in `Edge`, including full faithfulness with precisely normalized image and actual inverse.
Source: comparisons proof (3), final sentence; integral-adjunction proof, first paragraph
and displayed Hom chain (blueprint: lem-sp-current-composition-integral-edge).

Proof in words:
1. Finite type over a field makes X and Y Noetherian. Apply sk-lem-sp-tower to their
native integral coefficients: reduction is fully faithful with normalized image and
inverse the actual scalar-restricted total derived limit. The source category has no
completeness hypothesis; its completion unit is a conclusion.
2. Choose the normalized scalar comparisons and derived-limit presentations of
lem-sp-integral-tower-image-reconstruction. Its reconstruction is invertible and its
whole-tower adjoint transpose equals the proper-counit/open-unit mate. Its closure
assertion restricts compact support to Dbc and gives the left comparison.
3. The supplied right adjoint is counit-preservingly isomorphic to the geometric tower
right adjoint by uniqueness. The tower-gluing transition formula and the invertible
finite exceptional coefficient comparisons preserve normalization. Its uniform
constructibility and Tor bounds are retained under this isomorphism.
4. Hence G red_Y has normalized values. The normalized inverse-limit equivalence makes
its actual total limit constructible, and the actual reduction/limit counit there is
invertible. This counit, naturally in K, is the right comparison.
5. Restrict the supplied adjunction along the two fully faithful reductions using
these specified comparisons. The fully faithful adjunction-restriction formulas give
exactly the displayed unit and counit equations, with both triangle identities.
Everything is formed in whole derived tower categories before finite evaluation.
The argument allows empty schemes, zero objects, d=0, and arbitrary positive-
characteristic fields of characteristic different from l. -/
theorem integralEdge
    (s : Coefficients l E)
    (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (hpl : p ≠ l)
    {X Y : Scheme.{u}}
    [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))] [LocallyOfFiniteType (Y ↘ Spec (.of k))]
    [QuasiCompact (Y ↘ Spec (.of k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))] (d : ℕ) [SmoothOfRelativeDimension d f]
    (c : Compactification f)
    (hF : ∀ M : Towers l E s X, spConstructibleTorTowers l E Y (s.towers Y)
      ((towerShriek l E s c).obj M.obj))
    (G : Towers l E s Y ⥤ Towers l E s X) (a : towerSupport l E s c hF ⊣ G) :
    ∃ q : ScalarCompatibility l E s, ∃ hq : OpenScalarIsIso l E s q,
      ∃ A : ∀ T : Scheme.{u}, DerivedLimit l E s T,
        Nonempty (Edge l E s q hq A c hF G a) := by
  sorry

end AlgebraicGeometry.ProEtale.CompositionComparisons.Native
