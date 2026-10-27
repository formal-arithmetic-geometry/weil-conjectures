/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P4
-/
module

public import Sheaf.Paper.SmoothPurityTowerGamma
public import Sheaf.Paper.SmoothPurityTowerExceptionalBaseChange
public import Sheaf.Paper.FrobeniusCoefficientTwistsCanonical
public import Sheaf.Paper.CoefficientTowerShriekInterfaces
public import Sheaf.Paper.PurityFiniteSetting
public import Sheaf.SixFunctors.SchemeGeometricFrobenius
public import Sheaf.Paper.SmoothPurityCoefficientTowers
public import Sheaf.Paper.SmoothPurityNormalizedTowers
public import Sheaf.Paper.SmoothPurityTowerGluing
public import Sheaf.Paper.SmoothPurityTowerGammaData
public import Sheaf.Paper.SmoothPurityCoordinateRightComparisons
public import Sheaf.Paper.TowerClassDiagonal
public import Sheaf.Paper.TowerClassPullback
public import Sheaf.Paper.SmoothPurityTowerChartData
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Proper

/-! # Data for the geometric Frobenius purity mate

Source: literature/blueprint/latest/blueprint/sec-six-functors/sk-thm-sf-package/
thm-pur-weil-equivariance-of-purity-and-trace.proof.md, Steps 1 and 5; and
sec-smooth-purity/sk-prop-sp-purity-bc/sk-prop-sp-purity-bc-factors.md, (1)--(2)
(blueprint: def-pur-tower-geometric-purity-data).

The root comparison is specified before localization. The compact-support arrow is
proper/open exchange followed by the recorded compactification refinement. All Hom
identities below are whole-tower identities, in section-preserving derived coordinates.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall


universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry.Scheme WeilConjectures
namespace AlgebraicGeometry.ProEtale.SpGeometricPurity

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (b : SpTowerShriek.Base l E) (o : SpTowerShriek.Operations l E b)
  (q : SpTowerCalculus.Coordinates l E b)

/-- A strict root-line comparison: the ordinary adjoint acts on every scalar/root
section by coefficient restriction and restriction of the actual root. Thus all power
and quotient transitions are retained before deriving. The unit uses the recorded
constant-section comparison, including the zero-fold twist.
Source: equivariance Step 1, tau_d (blueprint: def-pur-tower-geometric-purity-data). -/
structure Roots {X : Scheme.{u}} (g : X ⟶ X)
    (w : SpChartAdmissibility.Twists l E X)
    (r : SpCoordinateAdjunction.RootLines l E X) where
  unit : SpTowerClasses.CoefficientPullback l E b g (o.geometry g)
  line : (o.geometry g).pull.obj (w.tower 1) ≅ w.tower 1
  normalized : ∀ (n : ℕ) (U : X.ProEtᵒᵖ)
    (a : (SpTowerShriek.B l E X n).obj.obj U)
    (z : (proEtaleRootsOfUnitySheaf X (l ^ (n + 1))).obj.obj U),
    ((proEtaleConstantRingPushforward (SpTowerShriek.R l E n) g).map
      ((w.level n 1).hom ≫ (r.iso n).hom)).val.app U
        (SpTowerClasses.adjointSection l E (o.geometry g) line.hom n U
          ((w.level n 1 ≪≫ r.iso n).inv.val.app U
            (tateFiniteTensor X l (SpTowerClasses.FiniteRing l E n) n
              (SpTowerClasses.finiteScalar l E n) U.unop a z))) =
      tateFiniteTensor X l (SpTowerClasses.FiniteRing l E n) n
        (SpTowerClasses.finiteScalar l E n) (SpTowerClasses.chart g U).unop
        ((proEtaleConstantDirectImageMap.{u, u + 2} g CommRingCat.{u + 1}
          (CommRingCat.of (SpTowerClasses.FiniteRing l E n))).hom.app U a)
        (SpTowerClasses.restrictRoot l g n U z)

/-- Pull the ordered Tate line through the tensor and shift comparisons. The
successor is an actual tensor of whole-tower maps, starting with the strict root
comparison above; no map is chosen from a family of derived evaluations.
Source: equivariance Step 1, tau_d (blueprint: def-pur-tower-geometric-purity-data). -/
def orderedRoots {X : Scheme.{u}} {g : X ⟶ X}
    {w : SpChartAdmissibility.Twists l E X}
    {r : SpCoordinateAdjunction.RootLines l E X} (t : Roots l E b o g w r) :
    ∀ d : ℕ, (SpTowerShriek.pull l E b (o.geometry g)).obj
      (SpTowerGamma.orderedLine l E b X w d) ≅ SpTowerGamma.orderedLine l E b X w d
  | 0 => t.unit.derivedIso l E
  | d + 1 => (o.geometry g).tensorPullback.app _ ≪≫
      (SpTowerShriek.tensor l E b X).mapIso (Iso.prod (orderedRoots t d)
        (((SpTowerShriek.pull l E b (o.geometry g)).commShiftIso (2 : ℤ)).app _ ≪≫
          (shiftFunctor _ (2 : ℤ)).mapIso
            (((o.geometry g).pull.mapDerivedCategorySingleFunctor 0).app _ ≪≫
              (DerivedCategory.singleFunctor _ 0).mapIso t.line)))

/-- Cancellation of the inverse realization after exact tower pullback. This is the
specified equivalence counit, rather than a free comparison of functors.
Source: equivariance Step 1, underlying sites
(blueprint: def-pur-tower-geometric-purity-data). -/
def pullRealization {X Y : Scheme.{u}} (g : X ⟶ Y)
    (h : ∀ K : SpTowerCalculus.C l E b q Y,
      spConstructibleTorTowers l E X (q.abelian X)
        ((SpTowerCalculus.etalePullback l E b o q g).obj K.obj))
    (K : SpTowerCalculus.C l E b q Y) :
    (SpTowerGamma.realization l E b q X).obj
        ((ObjectProperty.lift _ (SpTowerCalculus.inclusion l E b q Y ⋙
          SpTowerCalculus.etalePullback l E b o q g) h).obj K) ≅
      (SpTowerShriek.pull l E b (o.geometry g)).obj
        ((SpTowerGamma.realization l E b q Y).obj K) :=
  (SpTowerCalculus.realization l E b X (q.abelian X)).counitIso.app _

section Square
variable {X Y : Scheme.{u}} (f : X ⟶ Y) (gX : X ⟶ X) (gY : Y ⟶ Y)
  (sq : IsPullback gX f f gY)
  (hx : ∀ K : SpTowerCalculus.C l E b q X,
    spConstructibleTorTowers l E X (q.abelian X)
      ((SpTowerCalculus.etalePullback l E b o q gX).obj K.obj))
  (hy : ∀ K : SpTowerCalculus.C l E b q Y,
    spConstructibleTorTowers l E Y (q.abelian Y)
      ((SpTowerCalculus.etalePullback l E b o q gY).obj K.obj))

/-- The actual restricted exact pullback on X, preserving all tower transitions.
Source: equivariance Step 1, Q (blueprint: def-pur-tower-geometric-purity-data). -/
def Q : SpTowerCalculus.C l E b q X ⥤ SpTowerCalculus.C l E b q X :=
  ObjectProperty.lift _ (SpTowerCalculus.inclusion l E b q X ⋙
    SpTowerCalculus.etalePullback l E b o q gX) hx

/-- The actual restricted exact pullback on Y.
Source: equivariance Step 1, P (blueprint: def-pur-tower-geometric-purity-data). -/
def P : SpTowerCalculus.C l E b q Y ⥤ SpTowerCalculus.C l E b q Y :=
  ObjectProperty.lift _ (SpTowerCalculus.inclusion l E b q Y ⋙
    SpTowerCalculus.etalePullback l E b o q gY) hy

/-- Composition, ordinary derived tensor pullback, the strict root tower and shift
comparisons define b_K. In particular this formula fixes b independently of Gamma.
Source: equivariance Step 1 (blueprint: def-pur-tower-geometric-purity-data). -/
def sourceComparison (w : SpChartAdmissibility.Twists l E X)
    (r : SpCoordinateAdjunction.RootLines l E X) (t : Roots l E b o gX w r)
    (d : ℕ) (K : SpTowerCalculus.C l E b q Y) :
    (SpTowerShriek.pull l E b (o.geometry gX)).obj
        ((SpTowerGamma.source l E b o q f w d).obj K) ≅
      (SpTowerGamma.source l E b o q f w d).obj ((P l E b o q gY hy).obj K) :=
  (o.geometry gX).tensorPullback.app _ ≪≫
    (SpTowerShriek.tensor l E b X).mapIso
      (Iso.prod ((SpTowerShriek.square l E b o gX f f gY sq.w).symm.app _ ≪≫
          (SpTowerShriek.pull l E b (o.geometry f)).mapIso
            (pullRealization l E b o q gY hy K).symm)
        (orderedRoots l E b o t d))

end Square

section Compactification
variable (k : Type u) [Field k] {X Y : Scheme.{u}}
  [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
  [IsSeparated (X ↘ Spec (.of k))]
  [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
  [IsSeparated (Y ↘ Spec (.of k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
  (f : X ⟶ Y) [f.IsOver (Spec (.of k))]
  [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
  (gX : X ⟶ X) (gY : Y ⟶ Y) (sq : IsPullback gX f f gY)
  (c : Compactification f)
  (z : SpTowerCalculus.FiniteCoordinates l E)
  (h : SpTowerCalculus.Preservation l E k b o q)
  (cal : SpTowerCalculus.Calculus l E k b o q z h)
  (x : SpTowerShriek.OpenExchange l E b o)
  (hx : ∀ K : SpTowerCalculus.C l E b q X,
    spConstructibleTorTowers l E X (q.abelian X)
      ((SpTowerCalculus.etalePullback l E b o q gX).obj K.obj))
  (hy : ∀ K : SpTowerCalculus.C l E b q Y,
    spConstructibleTorTowers l E Y (q.abelian Y)
      ((SpTowerCalculus.etalePullback l E b o q gY).obj K.obj))
  (hF : ∀ K : SpTowerCalculus.C l E b q X,
    spConstructibleTorTowers l E Y (q.abelian Y)
      ((SpTowerCalculus.F l E b o q c).obj K.obj))

/-- Proper/open exchange for the Cartesian square, followed by the canonical
refinement from the pulled-back compactification to c, restricted to the full ctf
subcategory. The retagged k-linear square has exactly these underlying site maps.
Source: equivariance Step 1, B (blueprint: def-pur-tower-geometric-purity-data). -/
def exchange : SpTowerGluing.support l E b o q c hF ⋙ P l E b o q gY hy ⟶
    Q l E b o q gX hx ⋙ SpTowerGluing.support l E b o q c hF where
  app K := ObjectProperty.homMk
    ((SpTowerMate.exchange l E b o q x sq c).app K.obj ≫
      (cal.composition.refinement f (c.ofIsPullback sq) c).hom.app
        ((Q l E b o q gX hx).obj K))
  naturality _K _L a := ObjectProperty.hom_ext _
    ((Functor.whiskerLeft (SpTowerCalculus.inclusion l E b q X)
        (SpTowerMate.exchange l E b o q x sq c) ≫
      Functor.whiskerLeft (Q l E b o q gX hx)
        (cal.composition.refinement f (c.ofIsPullback sq) c).hom).naturality a)

/-- The counit mate of the specified compact-support exchange, formed with the same
adjunction on both copies. Its component is the transpose of B inverse then P epsilon.
Source: equivariance Step 1, e (blueprint: def-pur-tower-geometric-purity-data). -/
def mate (G : SpTowerCalculus.C l E b q Y ⥤ SpTowerCalculus.C l E b q X)
    (adj : SpTowerGluing.support l E b o q c hF ⊣ G)
    (hb : IsIso (exchange l E b o q k f gX gY sq c z h cal x hx hy hF)) :
    G ⋙ Q l E b o q gX hx ⟶ P l E b o q gY hy ⋙ G :=
  (mateEquiv adj adj (TwoSquare.mk _ _ _ _
    (@inv _ _ _ _ (exchange l E b o q k f gX gY sq c z h cal x hx hy hF) hb))).natTrans

end Compactification
end AlgebraicGeometry.ProEtale.SpGeometricPurity

namespace AlgebraicGeometry.ProEtale.SpGeometricPurity
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (b : SpTowerShriek.Base l E) (o : SpTowerShriek.Operations l E b)
  (q : SpTowerCalculus.Coordinates l E b)

section Purity
variable {X Z Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
  (j : X ⟶ Z) [IsOpenImmersion j] (p : Z ⟶ Y) [IsProper p]
  [QuasiCompact (j ≫ p)] [HasCompactification (j ≫ p)]
  (d : ℕ) (w : SpChartAdmissibility.Twists l E X)
  (hF : ∀ K : SpTowerCalculus.C l E b q X,
    spConstructibleTorTowers l E Y (q.abelian Y)
      ((SpTowerCalculus.F l E b o q (SpTowerGamma.factorization j p)).obj K.obj))
  (G : SpTowerCalculus.C l E b q Y ⥤ SpTowerCalculus.C l E b q X)
  (adj : SpTowerGluing.support l E b o q (SpTowerGamma.factorization j p) hF ⊣ G)
  (lv : SpTowerGluing.Levels l E b o q (SpTowerGamma.factorization j p) hF G adj)
  (a : SpTowerGamma.Purity l E b o q j p d w hF G adj lv)

/-- The existing tower purity isomorphism, with its recorded orientation/tensor
factorization. This packages its proved invertibility without choosing a new map.
Source: tower gamma (2) (blueprint: def-pur-tower-geometric-purity-data). -/
def purityIso (K : SpTowerCalculus.C l E b q Y) :
    (SpTowerGamma.source l E b o q (j ≫ p) w d).obj K ≅
      (SpTowerGamma.exceptional l E b q G).obj K :=
  @asIso _ _ _ _
    (SpTowerGamma.gamma l E b o q (SpTowerGamma.factorization j p) w d
      a.tensorX a.tensorY hF G adj a.unit_mem a.orientation K
        (a.tensor_mem K) (a.projection_iso K)) (a.purity_iso K)

/-- Retagging the same compactification identifies the entire orientation and the
inverse-projection/counit transpose. Right-adjoint identification is the unique
counit-preserving comparison, with the same ordinary site and Tate-tower coordinates.
The quantified second presentation is the presentation for f retagged by gamma.
Source: equivariance Step 1, retagging of both factors
(blueprint: def-pur-tower-geometric-purity-data). -/
def Retagging : Prop :=
  ∀ (Gγ : SpTowerCalculus.C l E b q Y ⥤ SpTowerCalculus.C l E b q X)
    (adjγ : SpTowerGluing.support l E b o q (SpTowerGamma.factorization j p) hF ⊣ Gγ)
    (lvγ : SpTowerGluing.Levels l E b o q (SpTowerGamma.factorization j p) hF Gγ adjγ)
    (aγ : SpTowerGamma.Purity l E b o q j p d w hF Gγ adjγ lvγ),
    aγ.orientation.hom ≫ (SpTowerGamma.realization l E b q X).map
        ((adjγ.rightAdjointUniq adj).hom.app
          ⟨SpTowerGamma.originalUnit l E b q Y, aγ.unit_mem⟩) = a.orientation.hom ∧
    ∀ K : SpTowerCalculus.C l E b q Y,
      (SpTowerShriek.F l E b o (SpTowerGamma.factorization j p)).map
          ((SpTowerShriek.tensor l E b X).map (Prod.mkHom (𝟙 _)
            ((SpTowerGamma.realization l E b q X).map
              ((adjγ.rightAdjointUniq adj).hom.app
                ⟨SpTowerGamma.originalUnit l E b q Y, a.unit_mem⟩)))) ≫
        SpTowerGamma.projectionCounit l E b o q (SpTowerGamma.factorization j p)
          a.tensorX a.tensorY hF G adj a.unit_mem K (a.projection_iso K) =
        SpTowerGamma.projectionCounit l E b o q (SpTowerGamma.factorization j p)
          aγ.tensorX aγ.tensorY hF Gγ adjγ aγ.unit_mem K (aγ.projection_iso K) ∧
      (SpTowerShriek.tensor l E b X).map (Prod.mkHom (𝟙 _)
          ((SpTowerGamma.realization l E b q X).map
            ((adjγ.rightAdjointUniq adj).hom.app
              ⟨SpTowerGamma.originalUnit l E b q Y, a.unit_mem⟩))) ≫
        SpTowerGamma.tensorMate l E b o q (SpTowerGamma.factorization j p)
          a.tensorX a.tensorY hF G adj a.unit_mem K (a.tensor_mem K)
            (a.projection_iso K) =
        SpTowerGamma.tensorMate l E b o q (SpTowerGamma.factorization j p)
          aγ.tensorX aγ.tensorY hF Gγ adjγ aγ.unit_mem K (aγ.tensor_mem K)
            (aγ.projection_iso K) ≫
          (SpTowerGamma.realization l E b q X).map
            ((adjγ.rightAdjointUniq adj).hom.app K)

variable (k : Type u) [Field k]
  [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
  [IsSeparated (X ↘ Spec (.of k))]
  [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
  [IsSeparated (Y ↘ Spec (.of k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
  [(j ≫ p).IsOver (Spec (.of k))]
  (gX : X ⟶ X) (gY : Y ⟶ Y) (sq : IsPullback gX (j ≫ p) (j ≫ p) gY)
  (z : SpTowerCalculus.FiniteCoordinates l E)
  (h : SpTowerCalculus.Preservation l E k b o q)
  (cal : SpTowerCalculus.Calculus l E k b o q z h)
  (x : SpTowerShriek.OpenExchange l E b o)

/-- The full semilinear tower conclusion. Membership and root-comparison witnesses
are outputs; normalization is only a premise of the preservation clauses. The last
two fields are identities in the ordinary derived tower category, in its fixed
section-preserving realization. They do not test equality by finite evaluation.
Source: equivariance Steps 1 and 5
(blueprint: def-pur-tower-geometric-purity-data). -/
structure Result where
  pullX : ∀ K : SpTowerCalculus.C l E b q X,
    spConstructibleTorTowers l E X (q.abelian X)
      ((SpTowerCalculus.etalePullback l E b o q gX).obj K.obj)
  pullY : ∀ K : SpTowerCalculus.C l E b q Y,
    spConstructibleTorTowers l E Y (q.abelian Y)
      ((SpTowerCalculus.etalePullback l E b o q gY).obj K.obj)
  roots : Roots l E b o gX w a.roots
  retagging : Retagging l E b o q j p d w hF G adj lv a
  exchange_iso : IsIso (exchange l E b o q k (j ≫ p) gX gY sq
    (SpTowerGamma.factorization j p) z h cal x pullX pullY hF)
  mate_iso : IsIso (mate l E b o q k (j ≫ p) gX gY sq
    (SpTowerGamma.factorization j p) z h cal x pullX pullY hF G adj exchange_iso)
  support_normalized : ∀ M : SpTowerCalculus.C l E b q X,
    IsSpNormalizedTower l E X (q.abelian X) M.obj →
      IsSpNormalizedTower l E Y (q.abelian Y)
        ((P l E b o q gY pullY).obj
          ((SpTowerGluing.support l E b o q (SpTowerGamma.factorization j p) hF).obj M)).obj ∧
      IsSpNormalizedTower l E Y (q.abelian Y)
        ((SpTowerGluing.support l E b o q (SpTowerGamma.factorization j p) hF).obj
          ((Q l E b o q gX pullX).obj M)).obj
  exceptional_normalized : ∀ K : SpTowerCalculus.C l E b q Y,
    IsSpNormalizedTower l E Y (q.abelian Y) K.obj →
      IsSpNormalizedTower l E X (q.abelian X)
        ((Q l E b o q gX pullX).obj (G.obj K)).obj ∧
      IsSpNormalizedTower l E X (q.abelian X)
        (G.obj ((P l E b o q gY pullY).obj K)).obj
  transpose : ∀ K : SpTowerCalculus.C l E b q Y,
    (mate l E b o q k (j ≫ p) gX gY sq (SpTowerGamma.factorization j p)
        z h cal x pullX pullY hF G adj exchange_iso).app K =
      adj.homEquiv _ _
        ((@inv _ _ _ _ (exchange l E b o q k (j ≫ p) gX gY sq
            (SpTowerGamma.factorization j p) z h cal x pullX pullY hF) exchange_iso).app
            (G.obj K) ≫ (P l E b o q gY pullY).map (adj.counit.app K))
  source_naturality : ∀ (K L : SpTowerCalculus.C l E b q Y) (v : K ⟶ L),
    (SpTowerShriek.pull l E b (o.geometry gX)).map
        ((SpTowerGamma.source l E b o q (j ≫ p) w d).map v) ≫
      (sourceComparison l E b o q (j ≫ p) gX gY sq pullY w a.roots roots d L).hom =
    (sourceComparison l E b o q (j ≫ p) gX gY sq pullY w a.roots roots d K).hom ≫
      (SpTowerGamma.source l E b o q (j ≫ p) w d).map
        ((P l E b o q gY pullY).map v)
  purity_square : ∀ K : SpTowerCalculus.C l E b q Y,
    (SpTowerShriek.pull l E b (o.geometry gX)).map
        (purityIso l E b o q j p d w hF G adj lv a K).hom ≫
      (pullRealization l E b o q gX pullX (G.obj K)).inv ≫
      (SpTowerGamma.realization l E b q X).map
        ((mate l E b o q k (j ≫ p) gX gY sq (SpTowerGamma.factorization j p)
          z h cal x pullX pullY hF G adj exchange_iso).app K) =
    (sourceComparison l E b o q (j ≫ p) gX gY sq pullY w a.roots roots d K).hom ≫
      (purityIso l E b o q j p d w hF G adj lv a
        ((P l E b o q gY pullY).obj K)).hom
  conjugation : ∀ K : SpTowerCalculus.C l E b q Y,
    (pullRealization l E b o q gX pullX (G.obj K)).inv ≫
      (SpTowerGamma.realization l E b q X).map
        ((mate l E b o q k (j ≫ p) gX gY sq (SpTowerGamma.factorization j p)
          z h cal x pullX pullY hF G adj exchange_iso).app K) =
    ((SpTowerShriek.pull l E b (o.geometry gX)).mapIso
      (purityIso l E b o q j p d w hF G adj lv a K)).inv ≫
      (sourceComparison l E b o q (j ≫ p) gX gY sq pullY w a.roots roots d K).hom ≫
      (purityIso l E b o q j p d w hF G adj lv a
        ((P l E b o q gY pullY).obj K)).hom
end Purity

end AlgebraicGeometry.ProEtale.SpGeometricPurity
