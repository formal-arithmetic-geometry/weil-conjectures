/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q31
-/
module

public import Sheaf.Paper.SmoothPurityCoordinateRightComparisons
public import Sheaf.Paper.SmoothPurityTowerChartAdmissibility
public import Sheaf.Paper.SmoothPurityTowerP1Adjunction
public import Sheaf.Paper.CoefficientTowerShriekCalculus
public import Sheaf.Paper.IntrinsicCoefficientTwistsUnrestricted
public import Sheaf.AlgebraicGeometry.AffineTraceTower
import Sheaf.Paper.SmoothPurityTowerCoordinateAdjunctionModels

/-! # Ordered coordinate adjunctions on ordinary derived towers

Source: blueprint latest, sec-smooth-purity/sk-prop-sp-tower-geometric,
`sk-prop-sp-tower-geometric-gluing.proof.md`, Local pairs and Levels
(blueprint: lem-sp-tower-coordinate-adjunction).

All levels n denote exponent n+1. The full subcategories below have uniform bounds,
without normalization. Every arrow belongs to an ordinary derived tower category.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOfSpec false
set_option genCtorIdx false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe u v v' w w' z z'
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme WeilConjectures

namespace AlgebraicGeometry.ProEtale.SpCoordinateAdjunction

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- A property and functor presentation of the tower chart theorem. Every comparison
in this proposition is constrained below by its ordinary or Hom formula.
Source: Local pairs and Levels (blueprint: lem-sp-tower-coordinate-adjunction). -/
def Construction (k : Type u) [Field k] (b : SpTowerShriek.Base l E)
    (o : SpTowerShriek.Operations l E b) (q : SpTowerCalculus.Coordinates l E b)
    (z : SpTowerCalculus.FiniteCoordinates l E)
    (h : SpTowerCalculus.Preservation l E k b o q)
    (cal : SpTowerCalculus.Calculus l E k b o q z h) (w : TwistFamily l E) : Prop :=
  /- All finite-type bases admit the dependency's normalized P1 presentation. -/
  ∃ (projective : ∀ Y : Bases k, ProjectivePresentation l E b o Y.val.left),
  /- The finite line is the root-projection normalized Kummer line. -/
  ∃ (roots : ∀ Y : Bases k, RootLines l E Y.val.left),
  /- Shift comparisons use the signed total-complex convention. -/
  ∃ (shifts : ∀ Y : Bases k, TensorShifts l E b Y.val.left),
  /- Multiplication is specified on local tensors and K-flat representatives. -/
  ∃ (products : ∀ Y : Bases k, Products l E b (w Y.val.left)),
  /- The Tate factors are pulled back before being multiplied. -/
  ∃ (pulled : ∀ (Y U : Bases k) (d : ℕ) (e : U.val.left ⟶ space Y.val.left d) (r : ℕ),
    PullTwist l E b o e (proj Y.val.left d) (w (space Y.val.left d)) (w U.val.left) r),
  /- The degree-zero line comparison sends each coefficient section to its pullback. -/
  ∃ (_pulled_zero : ∀ (Y U : Bases k) (d n : ℕ)
    (e : U.val.left ⟶ space Y.val.left d) (V : (space Y.val.left d).ProEtᵒᵖ)
    (a : (SpTowerShriek.B l E (space Y.val.left d) n).obj.obj V),
    pullSection l E (pulled Y U d e 0) n V a =
      (Scheme.proEtaleConstantDirectImageMap.{u, u + 2} e CommRingCat.{u + 1}
        (CommRingCat.of (SpTowerClasses.FiniteRing l E n))).hom.app V a),
  /- The positive generator is pulled back by restriction of the actual finite root. -/
  ∃ (_pulled_one : ∀ (Y U : Bases k) (d n : ℕ)
    (e : U.val.left ⟶ space Y.val.left d) (V : (space Y.val.left d).ProEtᵒᵖ)
    (a : (SpTowerShriek.B l E (space Y.val.left d) n).obj.obj V)
    (z : (Scheme.proEtaleRootsOfUnitySheaf (space Y.val.left d) (l ^ (n + 1))).obj.obj V),
    ((roots U).iso n).hom.val.app (SpTowerClasses.chart e V)
      (pullSection l E (pulled Y U d e 1) n V
        (((roots (coordinateBase Y d)).iso n).inv.val.app V
          (Scheme.tateFiniteTensor (space Y.val.left d) l (SpTowerClasses.FiniteRing l E n) n
            (SpTowerClasses.finiteScalar l E n) V.unop a z))) =
      Scheme.tateFiniteTensor U.val.left l (SpTowerClasses.FiniteRing l E n) n
        (SpTowerClasses.finiteScalar l E n) (SpTowerClasses.chart e V).unop
        ((Scheme.proEtaleConstantDirectImageMap.{u, u + 2} e CommRingCat.{u + 1}
          (CommRingCat.of (SpTowerClasses.FiniteRing l E n))).hom.app V a)
        (SpTowerClasses.restrictRoot l e n V z)),
  /- Higher positive powers are the same ordinary tensor pullback on local tensors. -/
  ∃ (_pulled_product : ∀ (Y U : Bases k) (d n r : ℕ)
    (e : U.val.left ⟶ space Y.val.left d) (V : (space Y.val.left d).ProEtᵒᵖ)
    (x : (spEllTwistLine l E (space Y.val.left d) n (r + 1 : ℕ)).val.obj V)
    (y : (spEllTwistOne l E (space Y.val.left d) n).val.obj V),
    pullSection l E (pulled Y U d e (r + 2)) n V
      (SheafOfModules.siteSheafTensorTmul
        (spEllTwistLine l E (space Y.val.left d) n (r + 1 : ℕ))
        (spEllTwistOne l E (space Y.val.left d) n) V x y) =
      SheafOfModules.siteSheafTensorTmul
        (spEllTwistLine l E U.val.left n (r + 1 : ℕ)) (spEllTwistOne l E U.val.left n)
        (SpTowerClasses.chart e V)
        (pullSection l E (pulled Y U d e (r + 1)) n V x)
        (pullSection l E (pulled Y U d e 1) n V y)),
  /- Root-normalized restriction of the projective right factor. -/
  ∃ (affine : ∀ Y : Bases k, AffineRestriction l E (projective Y)
    (w (space Y.val.left 1)) (roots (coordinateBase Y 1)) (shifts (coordinateBase Y 1))),
  /- Extension by zero has the etale-origin bounded-below domain needed by P1. -/
  ∃ (affine_source : ∀ (Y : Bases k) (M : (P l E b q (space Y.val.left 1)).FullSubcategory),
    SpTowerP1.domain l E (projective Y).presentation.classes.base (ProjectiveLine Y.val.left)
      ((SpTowerShriek.openD l E b (o.openOp (ProjectiveLine.affineChart Y.val.left))).obj
        ((SpTowerCalculus.realization l E b (space Y.val.left 1)
          (q.abelian (space Y.val.left 1))).functor.obj M.obj))),
  /- The input on the base has the same domain. -/
  ∃ (affine_target : ∀ (Y : Bases k) (K : (P l E b q Y.val.left).FullSubcategory),
    SpTowerP1.domain l E (projective Y).presentation.classes.base Y.val.left
      ((SpTowerCalculus.realization l E b Y.val.left (q.abelian Y.val.left)).functor.obj K.obj)),
  /- Separate level origins and bounded-below domains, without normalization. -/
  ∃ (_domains : ∀ (Y : Bases k) (K : (P l E b q Y.val.left).FullSubcategory),
    SpChartAdmissibility.domain l E b Y.val.left
      ((SpTowerCalculus.realization l E b Y.val.left (q.abelian Y.val.left)).functor.obj K.obj)),
  /- Projection adjunction for every coefficient-independent compactification. -/
  ∃ (projection : ∀ (Y : Bases k) (d : ℕ) (c : Compactification (proj Y.val.left d)),
    ProjectionPair l E b o q (proj Y.val.left d) c (w (space Y.val.left d)) d),
  /- Ordered tensor/shift identification, constructed on actual strict towers. -/
  ∃ (iteration : ∀ (Y : Bases k) (d : ℕ),
    orderedRight l E b o w Y.val.left d ≅
      projectionRight l E b o (proj Y.val.left d) (w (space Y.val.left d)) d),
  /- The successor comparison is the explicit pull/tensor/shift component. -/
  ∃ (step : ∀ (Y : Bases k) (d : ℕ),
    projectionRight l E b o (proj Y.val.left d) (w (space Y.val.left d)) d ⋙
      projectionRight l E b o
        (AffineSpace PUnit.{u + 1} (space Y.val.left d) ↘ space Y.val.left d)
        (w (space Y.val.left (d + 1))) 1 ≅
      projectionRight l E b o (proj Y.val.left (d + 1))
        (w (space Y.val.left (d + 1))) (d + 1)),
  ∃ (_step_normalized : ∀ (Y : Bases k) (d : ℕ) (K : SpTowerShriek.D l E Y.val.left),
    (step Y d).app K = stepComponent l E b o w Y.val.left d
      (pulled Y (coordinateBase Y (d + 1)) d
        (AffineSpace PUnit.{u + 1} (space Y.val.left d) ↘ space Y.val.left d) d)
      (products (coordinateBase Y (d + 1))) (shifts (coordinateBase Y (d + 1))) K),
  ∃ (_iteration_successor : ∀ (Y : Bases k) (d : ℕ),
    iteration Y (d + 1) =
      Functor.isoWhiskerRight (iteration Y d)
        (projectionRight l E b o
          (AffineSpace PUnit.{u + 1} (space Y.val.left d) ↘ space Y.val.left d)
          (w (space Y.val.left (d + 1))) 1) ≪≫ step Y d),
  /- The affine Hom map is the P1 Hom map followed by the actual open adjunction. -/
  ∃ (_affine_hom : ∀ (Y : Bases k)
    (M : (P l E b q (space Y.val.left 1)).FullSubcategory)
    (K : (P l E b q Y.val.left).FullSubcategory)
    (f : (SpTowerCalculus.F l E b o q (affineTraceLineCompactification Y.val.left)).obj
      M.obj ⟶ K.obj),
    realizedTranspose l E b q
      (projectionRight l E b o (proj Y.val.left 1) (w (space Y.val.left 1)) 1)
      M.obj K.obj ((projection Y 1 (affineTraceLineCompactification Y.val.left)).homEquiv
        M K f) =
      openHom l E b o Y.val.left
        ((SpTowerCalculus.realization l E b (space Y.val.left 1)
          (q.abelian (space Y.val.left 1))).functor.obj M.obj)
        (((projective Y).presentation.G l E).obj
          ((SpTowerCalculus.realization l E b Y.val.left (q.abelian Y.val.left)).functor.obj
            K.obj))
        (projectiveHom l E (projective Y)
          ⟨_, affine_source Y M⟩ ⟨_, affine_target Y K⟩
          ((projectivePush l E (projective Y)).hom.app _ ≫
            (supportRealization l E b o q (affineTraceLineCompactification Y.val.left)).inv.app
              M.obj ≫
            (SpTowerCalculus.realization l E b Y.val.left (q.abelian Y.val.left)).functor.map f)) ≫
      (affine Y).comparison.hom.app
        ((SpTowerCalculus.realization l E b Y.val.left (q.abelian Y.val.left)).functor.obj K.obj)),
  /- Every ordered projection is the composite of the preceding projection and line. -/
  ∃ (_projection_successor : ∀ (Y : Bases k) (d : ℕ)
    (cl : Compactification
      (AffineSpace PUnit.{u + 1} (space Y.val.left d) ↘ space Y.val.left d))
    (cp : Compactification (proj Y.val.left d))
    (cc : Compactification (proj Y.val.left (d + 1))),
    CompositeEquation (P l E b q (space Y.val.left (d + 1)))
      (P l E b q (space Y.val.left d)) (P l E b q Y.val.left)
      _ _ _ _ _ _
      (projection (coordinateBase Y d) 1 cl) (projection Y d cp)
      (projection Y (d + 1) cc)
      (cal.composition.composition
        (AffineSpace PUnit.{u + 1} (space Y.val.left d) ↘ space Y.val.left d)
        (proj Y.val.left d) (proj Y.val.left (d + 1)) rfl cl cp cc)
      (composeRight l E b q _ _ _ (step Y d))),
  /- The identity factor is fixed before deriving, including the coefficient unit. -/
  ∃ (zeroComparison : ∀ Y : Bases k, ZeroComparison l E b o Y.val.left (w Y.val.left)),
  ∃ (_iteration_zero : ∀ (Y : Bases k) (K : SpTowerShriek.D l E Y.val.left),
    (iteration Y 0).app K = ((zeroComparison Y).component l E K).symm),
  /- The zero-coordinate identification transports the identity adjunction. -/
  ∃ (_zero : ∀ (Y : Bases k) (c : Compactification (𝟙 Y.val.left))
    (M : (P l E b q Y.val.left).FullSubcategory)
    (K : (P l E b q Y.val.left).FullSubcategory)
    (f : (SpTowerCalculus.F l E b o q c).obj M.obj ⟶ K.obj),
    (projection Y 0 c).homEquiv M K f ≫
      (SpTowerCalculus.realization l E b Y.val.left (q.abelian Y.val.left)).inverse.map
        ((iteration Y 0).inv.app
          ((SpTowerCalculus.realization l E b Y.val.left (q.abelian Y.val.left)).functor.obj
            K.obj)) ≫
      (SpTowerCalculus.realization l E b Y.val.left (q.abelian Y.val.left)).unitIso.inv.app
        K.obj = (cal.composition.identity c).inv.app M ≫ f),
  /- A chart includes its k-structure, separated finite type etale map, and fixed
  compactification. No normalization is imposed on its input. -/
  ∃ (chart : ∀ (Y U : Bases k) (d : ℕ) (e : U.val.left ⟶ space Y.val.left d)
    (_over : e ≫ proj Y.val.left d ≫ Y.val.hom = U.val.hom)
    [Etale e] [IsSeparated e] [LocallyOfFiniteType e] [QuasiCompact e]
    (c : Compactification (e ≫ proj Y.val.left d)),
    ChartPair l E b o q e (proj Y.val.left d) c (w U.val.left) d),
  /- Finite projection adjunction and evaluation of all units, counits and Hom maps. -/
  ∃ (projection_levels : ∀ (Y : Bases k) (d : ℕ)
    (c : Compactification (proj Y.val.left d)) (n : ℕ),
    LevelCompatibility l E b q (projection Y d c) n (SpTowerShriek.finiteF l E b c n)
      (finiteProjectionRight l E b (proj Y.val.left d) (w (space Y.val.left d)) d n)),
  /- The finite chart adjunction is asserted for every finite object. -/
  ∃ (chart_levels : ∀ (Y U : Bases k) (d : ℕ) (e : U.val.left ⟶ space Y.val.left d)
    (hOver : e ≫ proj Y.val.left d ≫ Y.val.hom = U.val.hom)
    [Etale e] [IsSeparated e] [LocallyOfFiniteType e] [QuasiCompact e]
    (c : Compactification (e ≫ proj Y.val.left d)) (n : ℕ),
    LevelCompatibility l E b q (chart Y U d e hOver c) n
      (SpTowerShriek.finiteF l E b c n)
      (finiteChartRight l E b e (proj Y.val.left d) (w U.val.left) d n)),
  /- The finite left coordinate change is the specified compactification evaluation. -/
  ∃ (_projection_left_normalization : ∀ (Y : Bases k) (d : ℕ)
    (c : Compactification (proj Y.val.left d)) (n : ℕ),
    (projection_levels Y d c n).left = supportEvaluation l E b o q c n),
  /- The same fixed evaluation for the chart's compact support. -/
  ∃ (_chart_left_normalization : ∀ (Y U : Bases k) (d : ℕ)
    (e : U.val.left ⟶ space Y.val.left d)
    (hOver : e ≫ proj Y.val.left d ≫ Y.val.hom = U.val.hom)
    [Etale e] [IsSeparated e] [LocallyOfFiniteType e] [QuasiCompact e]
    (c : Compactification (e ≫ proj Y.val.left d)) (n : ℕ),
    (chart_levels Y U d e hOver c n).left = supportEvaluation l E b o q c n),
  /- Right evaluation has the canonical section/shift/tensor normalization. -/
  ∃ (_projection_right_normalization : ∀ (Y : Bases k) (d : ℕ)
    (c : Compactification (proj Y.val.left d)) (n : ℕ)
    (K : spDerivedCoefficientTowers l E Y.val.left (q.abelian Y.val.left)),
    (projection_levels Y d c n).right.hom.app K =
      projectionEvaluation l E b o q (proj Y.val.left d) (w (space Y.val.left d)) d n K),
  /- The chart uses the same fixed evaluation for both pullbacks. -/
  ∃ (_chart_right_normalization : ∀ (Y U : Bases k) (d : ℕ)
    (e : U.val.left ⟶ space Y.val.left d)
    (hOver : e ≫ proj Y.val.left d ≫ Y.val.hom = U.val.hom)
    [Etale e] [IsSeparated e] [LocallyOfFiniteType e] [QuasiCompact e]
    (c : Compactification (e ≫ proj Y.val.left d)) (n : ℕ)
    (K : spDerivedCoefficientTowers l E Y.val.left (q.abelian Y.val.left)),
    (chart_levels Y U d e hOver c n).right.hom.app K =
      rightEvaluation l E b o q e (proj Y.val.left d) (w U.val.left) d n K),
  /- The chart counit is the counit of the etale pair followed by integration,
  transported by the calculus composition and the preceding right comparison. -/
  ∀ (Y U : Bases k) (d : ℕ) (e : U.val.left ⟶ space Y.val.left d)
    [e.IsOver (Spec (.of k))] [Etale e] [IsSeparated e]
    [LocallyOfFiniteType e] [QuasiCompact e]
    (hOver : e ≫ proj Y.val.left d ≫ Y.val.hom = U.val.hom)
    (ce : Compactification e) (cp : Compactification (proj Y.val.left d))
    (ch : Compactification (e ≫ proj Y.val.left d))
    (K : (P l E b q Y.val.left).FullSubcategory),
    (chart Y U d e hOver ch).counit K =
      (SpTowerCalculus.F l E b o q ch).map
        ((composeRight l E b q _ _ _ (pulled Y U d e d).comparison).inv.app K.obj) ≫
      (cal.composition.composition e (proj Y.val.left d)
        (e ≫ proj Y.val.left d) rfl ce cp ch).inv.app
          ⟨(SpTowerCalculus.etalePullback l E b o q e).obj
              ((originalProjectionRight l E b o q (proj Y.val.left d)
                (w (space Y.val.left d)) d).obj K.obj),
            (etalePair l E k b o q z h cal U (coordinateBase Y d) e).right_closed
              ⟨_, (projection Y d cp).right_closed K⟩⟩ ≫
      (SpTowerCalculus.F l E b o q cp).map
        ((cal.etale.etale_shriek e ce).hom.app
          ⟨(SpTowerCalculus.etalePullback l E b o q e).obj
              ((originalProjectionRight l E b o q (proj Y.val.left d)
                (w (space Y.val.left d)) d).obj K.obj),
            (etalePair l E k b o q z h cal U (coordinateBase Y d) e).right_closed
              ⟨_, (projection Y d cp).right_closed K⟩⟩ ≫
          (etalePair l E k b o q z h cal U (coordinateBase Y d) e).counit
            ⟨_, (projection Y d cp).right_closed K⟩) ≫
      (projection Y d cp).counit K

/-- Ordered coordinate-chart adjunction on the unnormalized uniform constructible
finite-Tor subcategories of ordinary derived strict varying-coefficient towers.
Source: blueprint latest, Local pairs and Levels
(blueprint: lem-sp-tower-coordinate-adjunction).

Proof. Apply chart admissibility to all intermediate objects; their common bounds
and separate finite etale-origin witnesses place them in the P1 and open domains.
For one coordinate compose the normalized projective-line Hom bijection with the
open adjunction. Its counit is the projective trace after extension by zero.
Write ell = unit times uniformizer^e and use Base.ideals at exponent e(n+1).
The root projection p_(n+1) identifies the quotient line with the finite Kummer
line, and root restriction fixes its pullback. The equation
p_(n+2)(x)^ell = p_(n+1)(x) makes these ordinary maps strict tower maps.
Tensor reassociation, normalized on local pure tensors and K-flat representatives,
and the signed total-complex shift maps identify successive factors with (d)[2d].
Induct on the ordered coordinates, starting with the literal identity in degree
zero, using the compact-support composition isomorphism at each successor.
Compose with the canonical etale sum-extension adjunction. The composite-adjunction
counit formula gives fibre summation followed by ordered integration; its Hom
bijection determines both unit and counit and supplies the triangle identities.
Finally evaluate these actual constructions. Exact evaluation preserves each
composition and the fixed P1/open/etale adjunction formulas, giving both finite
transposes, units and counits. The finite construction applies to every finite
constructible finite-Tor object. No faithfulness of derived evaluation is used. -/
theorem tower_coordinate_adjunction
    (pchar : ℕ) [Fact pchar.Prime] (k : Type u) [Field k] [CharP k pchar]
    (_hl : l ≠ pchar) (b : SpTowerShriek.Base l E) (o : SpTowerShriek.Operations l E b)
    (q : SpTowerCalculus.Coordinates l E b) (z : SpTowerCalculus.FiniteCoordinates l E)
    (h : SpTowerCalculus.Preservation l E k b o q)
    (cal : SpTowerCalculus.Calculus l E k b o q z h) (w : TwistFamily l E) :
    Construction l E k b o q z h cal w := by
  obtain ⟨model⟩ := tower_coordinate_adjunction_models l E pchar k _hl b o q z h cal w
  exact ⟨model.projective,
    model.roots,
    model.shifts,
    model.products,
    model.pulled,
    model._pulled_zero,
    model._pulled_one,
    model._pulled_product,
    model.affine,
    model.affine_source,
    model.affine_target,
    model._domains,
    model.projection,
    model.iteration,
    model.step,
    model._step_normalized,
    model._iteration_successor,
    model._affine_hom,
    model._projection_successor,
    model.zeroComparison,
    model._iteration_zero,
    model._zero,
    model.chart,
    model.projection_levels,
    model.chart_levels,
    model._projection_left_normalization,
    model._chart_left_normalization,
    model._projection_right_normalization,
    model._chart_right_normalization,
    model.chart_counit⟩


end AlgebraicGeometry.ProEtale.SpCoordinateAdjunction
