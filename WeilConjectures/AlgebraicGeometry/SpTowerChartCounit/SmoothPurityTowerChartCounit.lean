/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpTowerShriek.SmoothPurityTowerShriekData
public import WeilConjectures.AlgebraicGeometry.SpTowerGluing.SmoothPurityEtaleNormalization
public import WeilConjectures.AlgebraicGeometry.VaryingRingGraph.VaryingRingGraphSummand
public import WeilConjectures.Algebra.Homology.OpenTensorNormalization.ExactDerivedAdjunctionSupplement
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.AlgebraicGeometry.SpTowerCalculus.CoefficientTowerShriekInterfaces
public import WeilConjectures.Compactification.Triangle
public import WeilConjectures.Compactification.CommonRefinement
public import WeilConjectures.AlgebraicGeometry.SpChartAdmissibility.SmoothPurityTowerChartData
public import WeilConjectures.AlgebraicGeometry.Semilinear.SemilinearDerivedSections
public import Mathlib.CategoryTheory.Functor.OfSequence
public import WeilConjectures.AlgebraicGeometry.Semilinear.SemilinearDerivedCalculusSupplement
public import WeilConjectures.Algebra.Homology.SmoothPurity.InvertibleTensorScalarExtensionDefinitionsSupplement
public import WeilConjectures.SmoothPurity.Coefficient.CoefficientTwistsDetailed
public import WeilConjectures.AlgebraicGeometry.SpCoordinateAdjunction.SmoothPurityCoordinateCategories
public import WeilConjectures.AlgebraicGeometry.SpTowerP1.SmoothPurityTowerP1Data

/-! # The specified local chart counit of the smooth tower adjunction

Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/sec-smooth-purity/
sec-sp-grp-ladic-summary/sec-towers-and-integral-coefficients/sk-prop-sp-tower-geometric/
sk-prop-sp-tower-geometric-gluing.proof.md, paragraph Local pairs
(blueprint: def-sp-tower-chart-counit).

For a separated finite-type etale chart `e : U → A^d_Y` the local counit
`ε_(U,K) : F_(e ≫ p_d)(e^* p_d^* K (d)[2d]) → K` is built from actual arrows only:

* the restriction of the projective-line counit of det-sp-tower-p1-adjunction to the affine
  line through the open adjunction of `a : A^1_S ⊆ P^1_S`
  (`Rq_*(a_! a^* G K) → Rq_*(G K) → K`), where the compactification of `A^1_S → S` is the
  canonical one `A^1_S ⊆ P^1_S → S` (`affineCompactification`), so `F = Rq_* a_!` literally;
* the ordered `d`-fold iteration of these counits along the coordinate tower
  `affineTraceTower Y d` (`orderedCounit`, the identity for `d = 0`);
* the etale fibre sum, the counit of `e_! ⊣ e^*` (def-sp-tower-etale-extension);
* the comparison of `F_(e ≫ p_d)` with the iterated composite `F_(A^1) ∘ ⋯ ∘ F_(A^1) ∘ e_!`:
  the compositors of def-sp-tower-shriek-compositor, with the canonical restricted
  compactifications (`restrictCompact`, from the canonical projective-line tower
  compactification `towerCompactification` of `p_r`), and the etale comparison
  `e_! → F_e` of def-sp-tower-etale-extension, inverted on the chart object.

Existence-only inputs are parameters, never chosen: the tower operations `b o x laws`, the
coordinates `q`, the graph coordinates `g` (C), the normalized projective-line presentations
`t r` of det-sp-tower-p1-adjunction over each `A^r_Y` (their Chern classes, tensor models and
the line comparisons exist only through existence theorems), and the identification `β` of the
canonical chart functor `e^* p_d^* (-)(d)[2d]` (canonical Tate twist, def-sp-tower-tate-twist)
with the ordered right composite. All invertibility and domain facts are theorems.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option genInjectivity false
set_option genSizeOfSpec false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme WeilConjectures


namespace AlgebraicGeometry.ProEtale.SpTowerChartCounit

/-! ## Geometry of the ordered coordinate tower -/

/-- The canonical compactification `A^1_S ⊆ P^1_S → S` of the affine-line projection: open
immersion the standard affine chart, proper map the projective line.
Source: Local pairs, `a : A^1_S ⊆ P^1_S` (blueprint: def-sp-tower-chart-counit). -/
def affineCompactification (S : Scheme.{u}) :
    Compactification (AffineSpace PUnit.{u + 1} S ↘ S) where
  Z := ProjectiveLine S
  g := ProjectiveLine S ↘ S
  i := ProjectiveLine.affineChart S
  comm := (ProjectiveLine.affineChart_over S).symm
  isProper := inferInstance
  isOpenImmersion := inferInstance

/-- Affine-line base change of an open immersion is an open immersion.
Source: Local pairs, coordinatewise compactification (blueprint: def-sp-tower-chart-counit).
Proof: `A^1_S → A^1_T` is the base change of `S → T` along `A^1_T → T`
(`AffineSpace.isPullback_map`), and open immersions are stable under base change. -/
theorem affineMap_isOpenImmersion {S T : Scheme.{u}} (i : S ⟶ T) [IsOpenImmersion i] :
    IsOpenImmersion (AffineSpace.map PUnit.{u + 1} i) := by
  sorry

/-- The commutation `p_(r+1) = (A^1(i) ≫ a) ≫ (q ≫ g)` for the next tower compactification.
Source: Local pairs, coordinatewise compactification (blueprint: def-sp-tower-chart-counit).
Proof: `a ≫ q` is the affine-line projection, `A^1(i)` lies over `i`, and `i ≫ g = p_r`. -/
theorem towerStep_comm (Y : Scheme.{u}) (r : ℕ) (c : Compactification (affineTraceProjection Y r)) :
    affineTraceProjection Y (r + 1) =
      (AffineSpace.map PUnit.{u + 1} c.i ≫ ProjectiveLine.affineChart c.Z) ≫
        ((ProjectiveLine c.Z ↘ c.Z) ≫ c.g) := by
  sorry

/-- The canonical projective-line tower compactification of the coordinate projection
`p_r : A^r_Y → Y`: `Y` itself for `r = 0`; for `r + 1`, the affine line over the previous
compactification inside its projective line.
Source: Local pairs, the compactification `A^1 ⊆ P^1` in each coordinate
(blueprint: def-sp-tower-chart-counit). -/
def towerCompactification (Y : Scheme.{u}) :
    (r : ℕ) → Compactification (affineTraceProjection Y r)
  | 0 =>
    { Z := Y
      g := 𝟙 Y
      i := 𝟙 Y
      comm := (Category.comp_id (𝟙 Y)).symm
      isProper := inferInstance
      isOpenImmersion := show IsOpenImmersion (𝟙 Y) from inferInstance }
  | r + 1 =>
    haveI := affineMap_isOpenImmersion (towerCompactification Y r).i
    { Z := ProjectiveLine (towerCompactification Y r).Z
      g := (ProjectiveLine (towerCompactification Y r).Z ↘ (towerCompactification Y r).Z) ≫
        (towerCompactification Y r).g
      i := AffineSpace.map PUnit.{u + 1} (towerCompactification Y r).i ≫
        ProjectiveLine.affineChart (towerCompactification Y r).Z
      comm := towerStep_comm Y r (towerCompactification Y r)
      isProper := inferInstance
      isOpenImmersion := inferInstance }

/-- The coordinate projections are quasi-compact.
Source: Local pairs (blueprint: def-sp-tower-chart-counit).
Proof: induction on `r`; identities and affine-line projections are quasi-compact, and
quasi-compactness is stable under composition. -/
theorem proj_quasiCompact (Y : Scheme.{u}) (r : ℕ) :
    QuasiCompact (affineTraceProjection Y r) := by
  sorry

/-- The canonical compactification of `h` restricted from one of `h ≫ p_r`: the first
compactification of the canonical triangle of def-sp-tower-shriek-compositor built from the
tower compactification of `p_r` (closure of `V` in the fibre product).
Source: Local pairs; Stacks 0F7J (blueprint: def-sp-tower-chart-counit). -/
def restrictCompact (Y : Scheme.{u}) (r : ℕ) {V : Scheme.{u}}
    (h : V ⟶ affineTraceTower Y r) [QuasiCompact h]
    (c : Compactification (h ≫ affineTraceProjection Y r)) : Compactification h :=
  haveI := proj_quasiCompact Y r
  (SpTowerShriek.canonicalTriangle (towerCompactification Y r) c).cf

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-! ## The ordered right composite and its left composite -/

/-- The projective-line right functor `q^*(-) ⊗ L_P[2]` of a normalized presentation, in the
common calculus `b`, `o` (the right-hand side of `projectiveTensor`).
Source: Local pairs; displayed adjunction of det-sp-tower-p1-adjunction
(blueprint: def-sp-tower-chart-counit). -/
def projectiveRightFunctor (b : SpTowerShriek.Base l E) (o : SpTowerShriek.Operations l E b)
    {S : Scheme.{u}} (t : SpCoordinateAdjunction.ProjectivePresentation l E b o S) :
    SpTowerShriek.D l E S ⥤ SpTowerShriek.D l E (ProjectiveLine S) :=
  SpTowerShriek.pull l E b (o.geometry (ProjectiveLine S ↘ S)) ⋙
    Prod.sectL (SpTowerShriek.D l E (ProjectiveLine S))
      ((SpTowerClasses.line l E t.presentation.classes.chernP)⟦(2 : ℤ)⟧) ⋙
      SpTowerShriek.tensor l E b (ProjectiveLine S)

/-- The affine-line right factor `a^*(q^*(-) ⊗ L_P[2])`.
Source: Local pairs, restriction to `A^1` (blueprint: def-sp-tower-chart-counit). -/
def affineRight (b : SpTowerShriek.Base l E) (o : SpTowerShriek.Operations l E b)
    {S : Scheme.{u}} (t : SpCoordinateAdjunction.ProjectivePresentation l E b o S) :
    SpTowerShriek.D l E S ⥤ SpTowerShriek.D l E (AffineSpace PUnit.{u + 1} S) :=
  projectiveRightFunctor l E b o t ⋙
    SpTowerShriek.pull l E b (o.geometry (ProjectiveLine.affineChart S))

/-- The ordered right composite `R_r : D(Y) → D(A^r_Y)`, the identity for `r = 0` and
`R_(r+1) = R_r ⋙ a^*(q^*(-) ⊗ L_P[2])` over `A^r_Y`.
Source: Local pairs, ordered iteration (blueprint: def-sp-tower-chart-counit). -/
def orderedRight (b : SpTowerShriek.Base l E) (o : SpTowerShriek.Operations l E b)
    (Y : Scheme.{u})
    (t : ∀ r : ℕ, SpCoordinateAdjunction.ProjectivePresentation l E b o (affineTraceTower Y r)) :
    (r : ℕ) → SpTowerShriek.D l E Y ⥤ SpTowerShriek.D l E (affineTraceTower Y r)
  | 0 => 𝟭 _
  | r + 1 => orderedRight b o Y t r ⋙ affineRight l E b o (t r)

/-- The ordered left composite `F_(A^1) ∘ ⋯ ∘ F_(A^1)` of the actual compact-support functors
of the canonical affine-line compactifications, the identity for `r = 0`.
Source: Local pairs, ordered iteration (blueprint: def-sp-tower-chart-counit). -/
def orderedLeft (b : SpTowerShriek.Base l E) (o : SpTowerShriek.Operations l E b)
    (Y : Scheme.{u}) :
    (r : ℕ) → SpTowerShriek.D l E (affineTraceTower Y r) ⥤ SpTowerShriek.D l E Y
  | 0 => 𝟭 _
  | r + 1 => SpTowerShriek.F l E b o (affineCompactification (affineTraceTower Y r)) ⋙
      orderedLeft b o Y r

/-! ## The ordered integrations -/

/-- The projective-line counit `ε = (id ⊗ Tr_q) ∘ projection⁻¹` of det-sp-tower-p1-adjunction
(`SpTowerP1.epsilon`), transported along the presentation's equalities `base = b` and
`operations = o`.
Source: Local pairs; displayed epsilon of det-sp-tower-p1-adjunction
(blueprint: def-sp-tower-chart-counit). -/
def projectiveCounit (b : SpTowerShriek.Base l E) (o : SpTowerShriek.Operations l E b)
    {S : Scheme.{u}} (t : SpCoordinateAdjunction.ProjectivePresentation l E b o S)
    (M : SpTowerShriek.D l E S)
    (hM : SpTowerP1.domain l E b S M) :
    (SpTowerShriek.push l E b (o.geometry (ProjectiveLine S ↘ S))).obj
      ((projectiveRightFunctor l E b o t).obj M) ⟶ M := by
  rcases t with ⟨hinv, p, hb, ho, m, a⟩
  cases hb
  cases ho
  exact SpTowerP1.epsilon l E m ⟨M, hM⟩

/-- The affine-line counit `Rq_*(a_! a^* G M) → Rq_*(G M) → M`: the direct image of the
open counit of `a_! ⊣ a^*`, followed by the projective-line counit. Its source is literally
`F_(A^1)(a^* G M)` for the canonical compactification.
Source: Local pairs, `Hom(N, a^*q^*K(1)[2]) ≃ Hom(a_!N, q^*K(1)[2]) ≃ Hom(Rq_*a_!N, K)`
(blueprint: def-sp-tower-chart-counit). -/
def affineCounit (b : SpTowerShriek.Base l E) (o : SpTowerShriek.Operations l E b)
    {S : Scheme.{u}} (t : SpCoordinateAdjunction.ProjectivePresentation l E b o S)
    (M : SpTowerShriek.D l E S)
    (hM : SpTowerP1.domain l E b S M) :
    (SpTowerShriek.F l E b o (affineCompactification S)).obj
      ((affineRight l E b o t).obj M) ⟶ M :=
  (SpTowerShriek.push l E b (o.geometry (ProjectiveLine S ↘ S))).map
      ((o.openOp (ProjectiveLine.affineChart S)).derivedAdjunction.counit.app
        ((projectiveRightFunctor l E b o t).obj M)) ≫
    projectiveCounit l E b o t M hM

/-- The ordered integrations `ι_r : F_(A^1) ⋯ F_(A^1)(R_r K) → K`: the identity for `r = 0`,
and `ι_(r+1) = ι_r ∘ (F_(A^1) ⋯ F_(A^1))(affine counit at R_r K)`; the first applied
integration is in the last coordinate.
Source: Local pairs, "ordered projective-line integrations", identity for `d = 0`
(blueprint: def-sp-tower-chart-counit). -/
def orderedCounit (b : SpTowerShriek.Base l E) (o : SpTowerShriek.Operations l E b)
    (Y : Scheme.{u})
    (t : ∀ r : ℕ, SpCoordinateAdjunction.ProjectivePresentation l E b o (affineTraceTower Y r))
    (K : SpTowerShriek.D l E Y)
    (hK : ∀ r : ℕ, SpTowerP1.domain l E b (affineTraceTower Y r)
      ((orderedRight l E b o Y t r).obj K)) :
    (r : ℕ) → (orderedLeft l E b o Y r).obj ((orderedRight l E b o Y t r).obj K) ⟶ K
  | 0 => 𝟙 K
  | r + 1 => (orderedLeft l E b o Y r).map
      (affineCounit l E b o (t r) ((orderedRight l E b o Y t r).obj K) (hK r)) ≫
    orderedCounit b o Y t K hK r

/-! ## Comparison of compact supports along the chart -/

/-- The comparison `F_c(M) → (F_(A^1) ⋯ F_(A^1))(F_(c_h)(M))` for a good `M` on `V`, a
quasi-compact `h : V → A^r_Y` and a compactification `c` of `h ≫ p_r`, where `c_h` is the
canonical restricted compactification. For `r = 0` it is the refinement comparison of
`c` (as compactification of `h`) with `c_h`; for `r + 1` it is the case `r` for
`h ≫ (A^1 → A^r)` followed by the inverse compositor `F_(h ≫ π) ≅ F_(A^1) ∘ F_h` of
def-sp-tower-shriek-compositor.
Source: Local pairs, "composition identifies Rq_*a_! with F_(p_1)", iterated
(blueprint: def-sp-tower-chart-counit). -/
def splitting (b : SpTowerShriek.Base l E) (o : SpTowerShriek.Operations l E b)
    (x : SpTowerShriek.OpenExchange l E b o) (laws : SpTowerShriek.Laws l E b o x)
    (Y : Scheme.{u}) {V : Scheme.{u}} (M : SpTowerShriek.D l E V)
    (hM : SpTowerShriek.Good l E b V M) :
    (r : ℕ) → (h : V ⟶ affineTraceTower Y r) → [QuasiCompact h] →
      (c : Compactification (h ≫ affineTraceProjection Y r)) →
      ((SpTowerShriek.F l E b o c).obj M ⟶
        (orderedLeft l E b o Y r).obj
          ((SpTowerShriek.F l E b o (restrictCompact Y r h c)).obj M))
  | 0, h, _, c =>
    (SpTowerShriek.compactificationIso l E b o x laws
      (c.copy (Category.comp_id h).symm) (restrictCompact Y 0 h c)).hom.app ⟨M, hM⟩
  | r + 1, h, _, c =>
    splitting b o x laws Y M hM r
        (h ≫ (AffineSpace PUnit.{u + 1} (affineTraceTower Y r) ↘ affineTraceTower Y r))
        (c.copy (Category.assoc _ _ _)) ≫
      (orderedLeft l E b o Y r).map
        ((SpTowerShriek.compositor l E b o x laws (restrictCompact Y (r + 1) h c)
          (affineCompactification (affineTraceTower Y r))
          (restrictCompact Y r
            (h ≫ (AffineSpace PUnit.{u + 1} (affineTraceTower Y r) ↘ affineTraceTower Y r))
            (c.copy (Category.assoc _ _ _)))).inv.app ⟨M, hM⟩)

/-! ## The chart functor and the chart counit -/

/-- The canonical chart right functor `e^* p_d^* (-)(d)[2d]` on system towers, with the
canonical tower Tate twist of def-sp-tower-tate-twist on `U`.
Source: Local pairs, `L_U = e^*p_d^*(-)(d)[2d]` (blueprint: def-sp-tower-chart-counit). -/
def chartRight (b : SpTowerShriek.Base l E) (o : SpTowerShriek.Operations l E b)
    {U T Y : Scheme.{u}} (e : U ⟶ T) (p : T ⟶ Y) (d : ℕ) :
    SpTowerShriek.D l E Y ⥤ SpTowerShriek.D l E U :=
  SpTowerShriek.pull l E b (o.geometry p) ⋙ SpTowerShriek.pull l E b (o.geometry e) ⋙
    SpTowerTateTwist.twistShift l E b U d

/-- The canonical chart right functor in the original tower coordinates.
Source: Local pairs (blueprint: def-sp-tower-chart-counit). -/
def originalChartRight (b : SpTowerShriek.Base l E) (o : SpTowerShriek.Operations l E b)
    (q : SpTowerCalculus.Coordinates l E b) {U T Y : Scheme.{u}} (e : U ⟶ T) (p : T ⟶ Y)
    (d : ℕ) :=
  (SpTowerCalculus.realization l E b Y (q.abelian Y)).functor ⋙
    chartRight l E b o e p d ⋙ (SpTowerCalculus.realization l E b U (q.abelian U)).inverse

/-- Constructible finite-Tor towers on a base have all ordered right composites in the
bounded-below etale-origin domain of the projective-line adjunction.
Source: Local pairs and Uniformity; lem-sp-tower-chart-admissibility
(blueprint: def-sp-tower-chart-counit).
Proof: the realization of a constructible tower lies in the domain
(AdjunctionData.constructible_restriction of each presentation); the projective right
functor preserves the domain (Maps.pull_closed), and so does open restriction. Induct on `r`. -/
theorem ordered_domain (pchar : ℕ) [Fact pchar.Prime] (hne : pchar ≠ l)
    (k : Type u) [Field k] [CharP k pchar]
    (b : SpTowerShriek.Base l E) (o : SpTowerShriek.Operations l E b)
    (q : SpTowerCalculus.Coordinates l E b) (Y : SpCoordinateAdjunction.Bases k)
    (t : ∀ r : ℕ,
      SpCoordinateAdjunction.ProjectivePresentation l E b o (affineTraceTower Y.val.left r))
    (K : SpTowerCalculus.C l E b q Y.val.left) (r : ℕ) :
    SpTowerP1.domain l E b (affineTraceTower Y.val.left r)
      ((orderedRight l E b o Y.val.left t r).obj
        ((SpTowerCalculus.realization l E b Y.val.left (q.abelian Y.val.left)).functor.obj
          K.obj)) := by
  sorry

/-- The chart object `e^* R_d K` is bounded below with etale-origin levels.
Source: Local pairs; lem-sp-tower-chart-admissibility (blueprint: def-sp-tower-chart-counit).
Proof: `ordered_domain` at `r = d`, and exact etale inverse image preserves lower bounds and
pulls etale-origin witnesses back levelwise. -/
theorem chart_good (pchar : ℕ) [Fact pchar.Prime] (hne : pchar ≠ l)
    (k : Type u) [Field k] [CharP k pchar]
    (b : SpTowerShriek.Base l E) (o : SpTowerShriek.Operations l E b)
    (q : SpTowerCalculus.Coordinates l E b) (Y U : SpCoordinateAdjunction.Bases k) (d : ℕ)
    (t : ∀ r : ℕ,
      SpCoordinateAdjunction.ProjectivePresentation l E b o (affineTraceTower Y.val.left r))
    (e : U.val.left ⟶ affineTraceTower Y.val.left d) [Etale e]
    (K : SpTowerCalculus.C l E b q Y.val.left) :
    SpTowerShriek.Good l E b U.val.left
      ((SpTowerShriek.pull l E b (o.geometry e)).obj
        ((orderedRight l E b o Y.val.left t d).obj
          ((SpTowerCalculus.realization l E b Y.val.left (q.abelian Y.val.left)).functor.obj
            K.obj))) := by
  sorry

/-- The etale comparison `e_! → F_c` is invertible at the chart object.
Source: Local pairs; def-sp-tower-etale-extension (blueprint: def-sp-tower-chart-counit).
Proof: `SpTowerEtale.comparison_isIso`, with the bounded-below representative and the
level origins supplied by `chart_good`. -/
theorem chart_comparison_isIso (pchar : ℕ) [Fact pchar.Prime] (hne : pchar ≠ l)
    (k : Type u) [Field k] [CharP k pchar]
    (b : SpTowerShriek.Base l E) (o : SpTowerShriek.Operations l E b)
    (x : SpTowerShriek.OpenExchange l E b o) (laws : SpTowerShriek.Laws l E b o x)
    (q : SpTowerCalculus.Coordinates l E b)
    (g : SpTowerGluing.GraphCoordinates l E b o) (Y U : SpCoordinateAdjunction.Bases k) (d : ℕ)
    (t : ∀ r : ℕ,
      SpCoordinateAdjunction.ProjectivePresentation l E b o (affineTraceTower Y.val.left r))
    (e : U.val.left ⟶ affineTraceTower Y.val.left d)
    (_over : e ≫ affineTraceProjection Y.val.left d ≫ Y.val.hom = U.val.hom)
    [Etale e] [IsSeparated e] [LocallyOfFiniteType e] [QuasiCompact e]
    (c : Compactification e) (K : SpTowerCalculus.C l E b q Y.val.left) :
    IsIso ((SpTowerEtale.comparison l E b o g e c).app
      ((SpTowerShriek.pull l E b (o.geometry e)).obj
        ((orderedRight l E b o Y.val.left t d).obj
          ((SpTowerCalculus.realization l E b Y.val.left (q.abelian Y.val.left)).functor.obj
            K.obj)))) := by
  sorry

/-- **The specified local chart counit**, in system coordinates, on the ordered right
composite: `F_c(e^* R_d K) → (F_(A^1))^d(F_(c_e)(e^* R_d K)) → (F_(A^1))^d(e_! e^* R_d K)
→ (F_(A^1))^d(R_d K) → K`, i.e. compactification splitting, inverse etale comparison,
the etale fibre sum, and the ordered projective-line integrations. For `d = 0` the
integrations are the identity.
Source: Local pairs, "the composite counit is fibre sum then ordered integrations"
(blueprint: def-sp-tower-chart-counit). -/
def orderedChartCounit (pchar : ℕ) [Fact pchar.Prime] (hne : pchar ≠ l)
    (k : Type u) [Field k] [CharP k pchar]
    (b : SpTowerShriek.Base l E) (o : SpTowerShriek.Operations l E b)
    (x : SpTowerShriek.OpenExchange l E b o) (laws : SpTowerShriek.Laws l E b o x)
    (q : SpTowerCalculus.Coordinates l E b)
    (g : SpTowerGluing.GraphCoordinates l E b o) (Y U : SpCoordinateAdjunction.Bases k) (d : ℕ)
    (t : ∀ r : ℕ,
      SpCoordinateAdjunction.ProjectivePresentation l E b o (affineTraceTower Y.val.left r))
    (e : U.val.left ⟶ affineTraceTower Y.val.left d)
    (hover : e ≫ affineTraceProjection Y.val.left d ≫ Y.val.hom = U.val.hom)
    [Etale e] [IsSeparated e] [LocallyOfFiniteType e] [QuasiCompact e]
    (c : Compactification (e ≫ affineTraceProjection Y.val.left d))
    (K : SpTowerCalculus.C l E b q Y.val.left) :
    (SpTowerShriek.F l E b o c).obj
        ((SpTowerShriek.pull l E b (o.geometry e)).obj
          ((orderedRight l E b o Y.val.left t d).obj
            ((SpTowerCalculus.realization l E b Y.val.left (q.abelian Y.val.left)).functor.obj
              K.obj))) ⟶
      (SpTowerCalculus.realization l E b Y.val.left (q.abelian Y.val.left)).functor.obj
        K.obj :=
  haveI := chart_comparison_isIso l E pchar hne k b o x laws q g Y U d t e hover
    (restrictCompact Y.val.left d e c) K
  splitting l E b o x laws Y.val.left _ (chart_good l E pchar hne k b o q Y U d t e K) d e c ≫
    (orderedLeft l E b o Y.val.left d).map
      (inv ((SpTowerEtale.comparison l E b o g e (restrictCompact Y.val.left d e c)).app
          ((SpTowerShriek.pull l E b (o.geometry e)).obj
            ((orderedRight l E b o Y.val.left t d).obj
              ((SpTowerCalculus.realization l E b Y.val.left (q.abelian Y.val.left)).functor.obj
                K.obj)))) ≫
        (SpTowerEtale.derivedCounit l E b o g e).app
          ((orderedRight l E b o Y.val.left t d).obj
            ((SpTowerCalculus.realization l E b Y.val.left (q.abelian Y.val.left)).functor.obj
              K.obj))) ≫
    orderedCounit l E b o Y.val.left t _ (ordered_domain l E pchar hne k b o q Y t K) d

/-- **The specified local chart counit** `ε_(U,K) : F_c(e^* p_d^* K (d)[2d]) → K` in the
original tower coordinates, for the canonical chart functor: the identification `β` of the
canonical chart functor with the ordered right composite, followed by
`orderedChartCounit`, transported through the section-preserving realizations.
Source: Local pairs (blueprint: def-sp-tower-chart-counit). -/
def chartCounit (pchar : ℕ) [Fact pchar.Prime] (hne : pchar ≠ l)
    (k : Type u) [Field k] [CharP k pchar]
    (b : SpTowerShriek.Base l E) (o : SpTowerShriek.Operations l E b)
    (x : SpTowerShriek.OpenExchange l E b o) (laws : SpTowerShriek.Laws l E b o x)
    (q : SpTowerCalculus.Coordinates l E b)
    (g : SpTowerGluing.GraphCoordinates l E b o) (Y U : SpCoordinateAdjunction.Bases k) (d : ℕ)
    (t : ∀ r : ℕ,
      SpCoordinateAdjunction.ProjectivePresentation l E b o (affineTraceTower Y.val.left r))
    (e : U.val.left ⟶ affineTraceTower Y.val.left d)
    (hover : e ≫ affineTraceProjection Y.val.left d ≫ Y.val.hom = U.val.hom)
    [Etale e] [IsSeparated e] [LocallyOfFiniteType e] [QuasiCompact e]
    (c : Compactification (e ≫ affineTraceProjection Y.val.left d))
    (β : chartRight l E b o e (affineTraceProjection Y.val.left d) d ≅
      orderedRight l E b o Y.val.left t d ⋙ SpTowerShriek.pull l E b (o.geometry e))
    (K : SpTowerCalculus.C l E b q Y.val.left) :
    (SpTowerCalculus.F l E b o q c).obj
        ((originalChartRight l E b o q e (affineTraceProjection Y.val.left d) d).obj K.obj) ⟶
      K.obj :=
  (SpTowerCalculus.realization l E b Y.val.left (q.abelian Y.val.left)).inverse.map
      ((SpTowerShriek.F l E b o c).map
          ((SpTowerCalculus.realization l E b U.val.left (q.abelian U.val.left)).counitIso.hom.app
              ((chartRight l E b o e (affineTraceProjection Y.val.left d) d).obj
                ((SpTowerCalculus.realization l E b Y.val.left (q.abelian Y.val.left)).functor.obj
                  K.obj)) ≫
            β.hom.app
              ((SpTowerCalculus.realization l E b Y.val.left (q.abelian Y.val.left)).functor.obj
                K.obj)) ≫
        orderedChartCounit l E pchar hne k b o x laws q g Y U d t e hover c K) ≫
    (SpTowerCalculus.realization l E b Y.val.left (q.abelian Y.val.left)).unitIso.inv.app K.obj

end AlgebraicGeometry.ProEtale.SpTowerChartCounit

attribute [instance high] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
