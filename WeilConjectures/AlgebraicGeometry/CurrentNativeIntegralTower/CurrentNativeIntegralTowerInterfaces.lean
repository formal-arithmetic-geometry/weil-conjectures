/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.IntegralDirectImageTower.IntegralDirectImageTowerData
public import WeilConjectures.AlgebraicGeometry.SpTowerGluing.SmoothPurityTowerGluingData
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-! # Current native reduction, geometric towers and integral adjunction interfaces

Source: latest blueprint, sk-lem-sp-tower, Proposition 10.17
(sk-prop-sp-tower-geometric), and the native integral realization in
sk-prop-sp-composition-comparisons.proof.md (3).
The three withdrawn theorem attachments are not used. The definitions here restrict
actual condensed-module functors; the equivalence uses their actual unit and counit.
(blueprint: def-pur-current-native-tower-interfaces).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genCtorIdx false
attribute [instance high] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale.CurrentNativeIntegralTower
open IntegralDirectImageTower

variable (ell : ℕ) [Fact ell.Prime] (E : Type u) [Field E]
  [Algebra (Padic ell) E] [FiniteDimensional (Padic ell) E]

/-- The full uniformly constructible finite-Tor category, without normalization.
Source: current Proposition 10.17 (blueprint: def-pur-current-native-tower-interfaces). -/
abbrev Towers (s : Presentation ell E) (T : Scheme.{u}) :=
  spConstructibleTorTowerCategory ell E T (s.towers T)

/-- Restrict the actual compactification tower functor.
Source: current Proposition 10.17 (blueprint: def-pur-current-native-tower-interfaces). -/
def towerSupport (s : Presentation ell E) {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f)
    (h : ∀ M : Towers ell E s X, spConstructibleTorTowers ell E Y (s.towers Y)
      ((towerShriek ell E s c).obj M.obj)) : Towers ell E s X ⥤ Towers ell E s Y :=
  ObjectProperty.lift _
    ((spConstructibleTorTowers ell E X (s.towers X)).ι ⋙ towerShriek ell E s c) h

/-- Restrict simultaneous derived reduction, retaining its quotient transitions.
Source: current sk-lem-sp-tower (blueprint: def-pur-current-native-tower-interfaces). -/
def reduction (s : Presentation ell E) (T : Scheme.{u})
    (h : ∀ K : Constructible ell E T, spConstructibleTorTowers ell E T (s.towers T)
      ((red ell E s T).obj K.obj)) : Constructible ell E T ⥤ Towers ell E s T :=
  ObjectProperty.lift _
    ((constantModelBoundedConstructible (spIntegralCondensed ell E) T).ι ⋙ red ell E s T) h

/-- The ambient functor is literally L_X J red_Y.
Source: current integral-edge statement (blueprint: def-pur-current-native-tower-interfaces). -/
def model (s : Presentation ell E) {X Y : Scheme.{u}} (L : Limit ell E s X)
    (hY : ∀ K : Constructible ell E Y, spConstructibleTorTowers ell E Y (s.towers Y)
      ((red ell E s Y).obj K.obj))
    (G : Towers ell E s Y ⥤ Towers ell E s X) :
    Constructible ell E Y ⥤ Integral ell E X :=
  reduction ell E s Y hY ⋙ G ⋙
    (spConstructibleTorTowers ell E X (s.towers X)).ι ⋙ lim ell E s X L

/-- Restrict that same functor, without changing objects or morphisms.
Source: current integral-edge statement (blueprint: def-pur-current-native-tower-interfaces). -/
def right (s : Presentation ell E) {X Y : Scheme.{u}} (L : Limit ell E s X)
    (hY : ∀ K : Constructible ell E Y, spConstructibleTorTowers ell E Y (s.towers Y)
      ((red ell E s Y).obj K.obj))
    (G : Towers ell E s Y ⥤ Towers ell E s X)
    (h : ∀ K : Constructible ell E Y,
      constantModelBoundedConstructible (spIntegralCondensed ell E) X
        ((model ell E s L hY G).obj K)) : Constructible ell E Y ⥤ Constructible ell E X :=
  ObjectProperty.lift _ (model ell E s L hY G) h

/-- The separately derived native compactification composite on Dbc.
Source: current integral-edge statement (blueprint: def-pur-current-native-tower-interfaces). -/
def support {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (h : ∀ M : Constructible ell E X,
      constantModelBoundedConstructible (spIntegralCondensed ell E) Y
        ((shriek ell E c).obj M.obj)) : Constructible ell E X ⥤ Constructible ell E Y :=
  ObjectProperty.lift _
    ((constantModelBoundedConstructible (spIntegralCondensed ell E) X).ι ⋙ shriek ell E c) h

/-- Both restrictions of red and actual total limit, and invertibility of their
ACTUAL unit and counit. These four assertions exhibit the restricted adjunction
as an equivalence; they do not choose unrelated equivalence functors.
Source: current sk-lem-sp-tower, Noetherian clause
(blueprint: def-pur-current-native-tower-interfaces). -/
structure ReductionEquivalence (s : Presentation ell E) (T : Scheme.{u})
    (L : Limit ell E s T) : Prop where
  normalized : ∀ M : Constructible ell E T,
    spNormalizedConstructibleTorTowers ell E T (s.towers T) ((red ell E s T).obj M.obj)
  constructible : ∀ C : spNormalizedConstructibleTorTowerCategory ell E T (s.towers T),
    constantModelBoundedConstructible (spIntegralCondensed ell E) T
      ((lim ell E s T L).obj C.obj)
  unit : ∀ M : Constructible ell E T,
    IsIso ((redLimitAdjunction ell E s T L).unit.app M.obj)
  counit : ∀ C : spNormalizedConstructibleTorTowerCategory ell E T (s.towers T),
    IsIso ((redLimitAdjunction ell E s T L).counit.app C.obj)

/-- Ordinary tensor/limit and derived representative normalization are part of Limit.
Only the equivalence clause assumes Noetherianity; Dbc itself contains no
completeness assumption. Source: current sk-lem-sp-tower
(blueprint: def-pur-current-native-tower-interfaces). -/
structure ReductionLimit (s : Presentation ell E) (T : Scheme.{u}) where
  total : Limit ell E s T
  equivalence : IsNoetherian T → ReductionEquivalence ell E s T total

/-- Current sk-lem-sp-tower, with the actual native ring and quotient transitions.
Source: latest blueprint, sk-lem-sp-tower, statement and proof.
Proof: (1) The ringed quotient-diagram adjunction tensors with each quotient;
its right adjoint first restricts finite actions and then takes total inverse limit.
The ordinary tensor unit and the cochain adjunction equation in Limit identify its
unit with derived completion. (2) On a Noetherian scheme, the condensed integral
criterion and the power-torsion limit comparison make this unit invertible on Dbc.
(3) Normalized towers have constructible total limit and their actual projection
adjoints are invertible by integral-constructible-completed-transport. (4) Exact
evaluations detect isomorphisms, so the whole counit is invertible. Restrict the
same adjunction using these four assertions to obtain the claimed equivalence. -/
theorem currentReductionLimit (s : Presentation ell E) (T : Scheme.{u}) :
    Nonempty (ReductionLimit ell E s T) := by
  sorry

/-- Section-normalized evaluation and scalar coordinates of the given presentation.
The existing coordinate notion is reused, with its abelian data definitionally
fixed to s.towers. Source: Proposition 10.17 finite evaluations
(blueprint: def-pur-current-native-tower-interfaces). -/
structure Coordinates (s : Presentation ell E) where
  ordinaryEvaluation : ∀ (T : Scheme.{u}) (n : ℕ),
    (s.base.realization T).functor ⋙ SpTowerShriek.ev ell E T n ≅
      spCoefficientEvaluation ell E T (s.towers T).equivalence n
  sections : ∀ (T : Scheme.{u}) (n : ℕ) (M : spCoefficientTowers ell E T)
    (U : T.ProEtᵒᵖ)
    (x : ((SpTowerShriek.ev ell E T n).obj ((s.base.realization T).functor.obj M)).val.obj U),
    HEq (((ordinaryEvaluation T n).hom.app M).val.app U x) x
  scalar : ∀ (T : Scheme.{u}) {m n : ℕ} (h : m ≤ n),
    SpTowerCalculus.ScalarCoordinates ell E T (s.towers T) h

/-- Insert the specified abelian coordinates into the existing calculus interface.
Source: Proposition 10.17 (blueprint: def-pur-current-native-tower-interfaces). -/
def Coordinates.calculus (s : Presentation ell E) (q : Coordinates ell E s) :
    SpTowerCalculus.Coordinates ell E s.base :=
  ⟨s.towers, q.ordinaryEvaluation, q.sections, q.scalar⟩

/-- The actual unnormalized tower adjunction, with all finite unit/counit equations
and the exceptional reduction formula c followed by J(r). Levels is the active
interface of det-sp-tower-gluing (not the withdrawn theorem attachment).
Source: current Proposition 10.17 (blueprint: def-pur-current-native-tower-interfaces). -/
structure GeometricAdjunction (s : Presentation ell E) {X Y : Scheme.{u}}
    {f : X ⟶ Y} (c : Compactification f) where
  support_closed : ∀ M : Towers ell E s X,
    spConstructibleTorTowers ell E Y (s.towers Y) ((towerShriek ell E s c).obj M.obj)
  right : Towers ell E s Y ⥤ Towers ell E s X
  adjunction : towerSupport ell E s c support_closed ⊣ right
  coordinates : Coordinates ell E s
  levels : SpTowerGluing.Levels ell E s.base s.operations
    (coordinates.calculus ell E s) c support_closed right adjunction

/-- Current Proposition 10.17, on all uniformly bounded constructible towers,
including nonnormalized ones. Source: latest blueprint sk-prop-sp-tower-geometric.
Proof: (1) Tower-bound restricts compact support to the stated full categories.
(2) Construct the projective-line unit and counit using the tower Kummer sequence,
Chern and diagonal classes and projective-line splitting; their triangles hold as
whole tower equations. (3) On a finite smooth coordinate cover, glue their
representing pairs by the binary fibre construction, retaining uniform bounds.
Representability defines the right-adjoint maps and proves naturality and triangles.
(4) Evaluated representability identifies finite units and counits. The counit
transpose defining c identifies each reduction as J(r) after c, including equal
indices and composites. These are precisely the equations in Levels. -/
theorem currentTowerGeometric (s : Presentation ell E)
    (p : ℕ) (hp : 0 < p) (hne : p ≠ ell) (k : Type u) [Field k] [CharP k p]
    (X Y : Over (Spec (.of k)))
    [IsSeparated X.hom] [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [IsSeparated Y.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
    (f : X ⟶ Y) (d : ℕ) [SmoothOfRelativeDimension d f.left]
    (c : Compactification f.left) : Nonempty (GeometricAdjunction ell E s c) := by
  sorry

/-- Canonical reconstruction: apply F to the INPUT completion unit, then the
right mate of the specified whole-tower proper/open reduction map. The expanded
mate uses the actual limit units/counits and thus fixes the whole derived arrow.
Source: current integral-edge and image-reconstruction, clause (2)
(blueprint: def-pur-current-native-tower-interfaces). -/
def reconstructionMap (s : Presentation ell E) {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f) (LX : Limit ell E s X) (LY : Limit ell E s Y)
    (q : ReductionGeometry ell E s) (hq : OpenReductionIsIso ell E s q)
    (M : Integral ell E X) :
    (shriek ell E c).obj M ⟶ (lim ell E s Y LY).obj (imageTower ell E s c M) :=
  (shriek ell E c).map ((redLimitAdjunction ell E s X LX).unit.app M) ≫
    (redLimitAdjunction ell E s Y LY).unit.app
      ((shriek ell E c).obj ((lim ell E s X LX).obj ((red ell E s X).obj M))) ≫
    (lim ell E s Y LY).map
      (towerBaseChange ell E s q hq c
          ((lim ell E s X LX).obj ((red ell E s X).obj M)) ≫
        (towerShriek ell E s c).map
          ((redLimitAdjunction ell E s X LX).counit.app ((red ell E s X).obj M)))

/-- Current native integral-edge interface: reduction is an equivalence onto the
normalized category; the left map is the reconstruction transpose; the right map
is the actual counit. Every adjunction map has its required whole-tower equation.
Source: current lem-sp-current-composition-integral-edge, all clauses
(blueprint: def-pur-current-native-tower-interfaces). -/
structure IntegralEdge (s : Presentation ell E) {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f)
    (hF : ∀ M : Towers ell E s X, spConstructibleTorTowers ell E Y (s.towers Y)
      ((towerShriek ell E s c).obj M.obj))
    (G : Towers ell E s Y ⥤ Towers ell E s X) (a : towerSupport ell E s c hF ⊣ G) where
  limitX : Limit ell E s X
  limitY : Limit ell E s Y
  equivalenceX : ReductionEquivalence ell E s X limitX
  equivalenceY : ReductionEquivalence ell E s Y limitY
  reductionX : ∀ M : Constructible ell E X, spConstructibleTorTowers ell E X (s.towers X)
    ((red ell E s X).obj M.obj)
  reductionY : ∀ K : Constructible ell E Y, spConstructibleTorTowers ell E Y (s.towers Y)
    ((red ell E s Y).obj K.obj)
  normalized : ∀ K : Constructible ell E Y,
    IsSpNormalizedTower ell E X (s.towers X)
      (G.obj ((reduction ell E s Y reductionY).obj K)).obj
  closed : ∀ K : Constructible ell E Y,
    constantModelBoundedConstructible (spIntegralCondensed ell E) X
      ((model ell E s limitX reductionY G).obj K)
  supportClosed : ∀ M : Constructible ell E X,
    constantModelBoundedConstructible (spIntegralCondensed ell E) Y
      ((shriek ell E c).obj M.obj)
  geometry : ReductionGeometry ell E s
  openIso : OpenReductionIsIso ell E s geometry
  reconstruction_iso : ∀ M : Constructible ell E X,
    IsIso (reconstructionMap ell E s c limitX limitY geometry openIso M.obj)
  leftComparison : support ell E c supportClosed ⋙ reduction ell E s Y reductionY ≅
    reduction ell E s X reductionX ⋙ towerSupport ell E s c hF
  left_normalization : ∀ M : Constructible ell E X,
    (leftComparison.hom.app M).hom =
      (red ell E s Y).map
          (reconstructionMap ell E s c limitX limitY geometry openIso M.obj) ≫
        (redLimitAdjunction ell E s Y limitY).counit.app (imageTower ell E s c M.obj)
  left_proper_open : ∀ M : Constructible ell E X,
    (leftComparison.hom.app M).hom = towerBaseChange ell E s geometry openIso c M.obj
  rightComparison : right ell E s limitX reductionY G closed ⋙ reduction ell E s X reductionX ≅
    reduction ell E s Y reductionY ⋙ G
  right_normalization : ∀ K : Constructible ell E Y,
    (rightComparison.hom.app K).hom =
      (redLimitAdjunction ell E s X limitX).counit.app
        (G.obj ((reduction ell E s Y reductionY).obj K)).obj
  adjunction : support ell E c supportClosed ⊣ right ell E s limitX reductionY G closed
  unit_reduction : ∀ M : Constructible ell E X,
    (reduction ell E s X reductionX).map (adjunction.unit.app M) =
      a.unit.app ((reduction ell E s X reductionX).obj M) ≫
        G.map (leftComparison.inv.app M) ≫ rightComparison.inv.app _
  counit_reduction : ∀ K : Constructible ell E Y,
    (reduction ell E s Y reductionY).map (adjunction.counit.app K) =
      leftComparison.hom.app _ ≫ (towerSupport ell E s c hF).map
        (rightComparison.hom.app K) ≫ a.counit.app ((reduction ell E s Y reductionY).obj K)

/-- Current native integral-edge assertion, for ANY supplied tower adjunction.
Source: current lem-sp-current-composition-integral-edge and its five proof steps.
Proof: (1) Finite type over a field makes X,Y Noetherian. Apply currentReductionLimit
and its equivalence clause to their native condensed module categories.
(2) Image-reconstruction gives constructible compact support and the canonical
reconstruction iso, whose transpose is the whole proper/open mate.
(3) currentTowerGeometric supplies a geometric adjoint. Uniqueness identifies any
supplied G with it preserving counits. Its reduction formula and the invertible
finite c maps show that G preserves normalized inputs; uniform bounds remain.
(4) The inverse in the reduction equivalence makes L_X G red_Y constructible,
and its actual counit supplies rightComparison. (5) Restrict the supplied
adjunction along the two fully faithful reductions. The restriction formulas
are exactly unit_reduction and counit_reduction; the triangles follow from
full faithfulness and the tower triangles. -/
theorem currentIntegralEdge (s : Presentation ell E)
    (p : ℕ) (hp : 0 < p) (hne : p ≠ ell) (k : Type u) [Field k] [CharP k p]
    (X Y : Over (Spec (.of k)))
    [IsSeparated X.hom] [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [IsSeparated Y.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
    (f : X ⟶ Y) (d : ℕ) [SmoothOfRelativeDimension d f.left]
    (c : Compactification f.left)
    (hF : ∀ M : Towers ell E s X.left,
      spConstructibleTorTowers ell E Y.left (s.towers Y.left)
        ((towerShriek ell E s c).obj M.obj))
    (G : Towers ell E s Y.left ⥤ Towers ell E s X.left)
    (a : towerSupport ell E s c hF ⊣ G) :
    Nonempty (IntegralEdge ell E s c hF G a) := by
  sorry

end AlgebraicGeometry.ProEtale.CurrentNativeIntegralTower
