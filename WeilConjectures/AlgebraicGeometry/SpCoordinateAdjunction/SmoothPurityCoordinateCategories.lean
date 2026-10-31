/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpChartAdmissibility.SmoothPurityTowerChartAdmissibility
public import WeilConjectures.AlgebraicGeometry.SpTowerP1.SmoothPurityTowerP1Adjunction
public import WeilConjectures.AlgebraicGeometry.SpTowerCalculus.CoefficientTowerShriekCalculus
public import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicCoefficientTwistsUnrestricted
public import WeilConjectures.AlgebraicGeometry.Affine.Trace.AffineTraceTower
import WeilConjectures.SmoothPurity.PurityFiniteSetting.Kummer.PurityFiniteKummerLevel
import WeilConjectures.Algebra.Homology.CanonicalTensorPullbackOfUniverses.RingedTopoiCanonicalTensorPullbackOfUniverses
import WeilConjectures.AlgebraicGeometry.SmoothPurity.AmbTateRootProjectionReduction
import WeilConjectures.AlgebraicGeometry.Finite.FiniteRootSiteComparison
import WeilConjectures.AlgebraicGeometry.FiniteEtaleTwistLine
import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateTwist
import WeilConjectures.AlgebraicGeometry.Sites.Kummer
import Mathlib.Algebra.Module.ZMod
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import Mathlib.CategoryTheory.Sites.Monoidal
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import WeilConjectures.AlgebraicGeometry.EtaleConstantRingModuleEquivalence
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import WeilConjectures.ConstructibleSheaf.Defs
import WeilConjectures.EtaleCohomology.TateTwist.Sheaf
import WeilConjectures.ConstructibleSheaf.Pullback
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.AlgebraicGeometry.SmoothPurity.RootTowerFiniteTensor

/-! # Ordered coordinate adjunctions on ordinary derived towers

Source: blueprint latest, sec-smooth-purity/sk-prop-sp-tower-geometric,
`sk-prop-sp-tower-geometric-gluing.proof.md`, Local pairs and Levels
(blueprint: def-sp-coordinate-adjunction-categories).

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

/-- Restriction of two actual functors to specified full subcategories, together with
an adjunction there. The adjunction is Mathlib's, so includes natural Hom bijections
and both triangle identities. Source: Local pairs
(blueprint: def-sp-coordinate-adjunction-categories). -/
structure RestrictedPair {A : Type v} {B : Type w} [Category.{v'} A] [Category.{w'} B]
    (P : ObjectProperty A) (Q : ObjectProperty B) (F : A ⥤ B) (G : B ⥤ A) where
  left_closed : ∀ M : P.FullSubcategory, Q (F.obj M.obj)
  right_closed : ∀ K : Q.FullSubcategory, P (G.obj K.obj)
  adjunction : ObjectProperty.lift Q (P.ι ⋙ F) left_closed ⊣
    ObjectProperty.lift P (Q.ι ⋙ G) right_closed

/-- The actual ambient counit, using the full inclusion. Source: Local pairs
(blueprint: def-sp-coordinate-adjunction-categories). -/
def RestrictedPair.counit {A : Type v} {B : Type w} [Category.{v'} A] [Category.{w'} B]
    {P : ObjectProperty A} {Q : ObjectProperty B} {F : A ⥤ B} {G : B ⥤ A}
    (a : RestrictedPair P Q F G) (K : Q.FullSubcategory) : F.obj (G.obj K.obj) ⟶ K.obj :=
  Q.ι.map (a.adjunction.counit.app K)

/-- The actual ambient unit. Source: Local pairs
(blueprint: def-sp-coordinate-adjunction-categories). -/
def RestrictedPair.unit {A : Type v} {B : Type w} [Category.{v'} A] [Category.{w'} B]
    {P : ObjectProperty A} {Q : ObjectProperty B} {F : A ⥤ B} {G : B ⥤ A}
    (a : RestrictedPair P Q F G) (M : P.FullSubcategory) : M.obj ⟶ G.obj (F.obj M.obj) :=
  P.ι.map (a.adjunction.unit.app M)

/-- The ambient Hom bijection, expressed through the fully faithful inclusions.
Source: displayed Hom bijection (blueprint: def-sp-coordinate-adjunction-categories). -/
def RestrictedPair.homEquiv {A : Type v} {B : Type w} [Category.{v'} A] [Category.{w'} B]
    {P : ObjectProperty A} {Q : ObjectProperty B} {F : A ⥤ B} {G : B ⥤ A}
    (a : RestrictedPair P Q F G) (M : P.FullSubcategory) (K : Q.FullSubcategory) :
    (F.obj M.obj ⟶ K.obj) ≃ (M.obj ⟶ G.obj K.obj) :=
  Q.fullyFaithfulι.homEquiv.symm.trans
    ((a.adjunction.homEquiv M K).trans P.fullyFaithfulι.homEquiv)

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- The recorded unnormalized uniform domain in the section-preserving system coordinates.
Source: standing convention (blueprint: def-sp-coordinate-adjunction-categories). -/
abbrev uniform (b : SpTowerShriek.Base l E) (q : SpTowerCalculus.Coordinates l E b)
    (T : Scheme.{u}) := SpTowerP1.uniform l E b T (q.abelian T)

/-- Tensor by the specified strict Tate tower, followed by the specified even shift.
Source: Local pairs (blueprint: def-sp-coordinate-adjunction-categories). -/
def twistShift (b : SpTowerShriek.Base l E) {T : Scheme.{u}}
    (w : SpChartAdmissibility.Twists l E T) (d : ℕ) :
    SpTowerShriek.D l E T ⥤ SpTowerShriek.D l E T :=
  Prod.sectL (SpTowerShriek.D l E T)
      ((DerivedCategory.singleFunctor (SpTowerShriek.S l E T) 0).obj (w.tower d)) ⋙
    SpTowerShriek.tensor l E b T ⋙ shiftFunctor _ (2 * (d : ℤ))

/-- p_d^*(-)(d)[2d], as an actual functor on ordinary derived towers.
Source: ordered projection factor (blueprint: def-sp-coordinate-adjunction-categories). -/
def projectionRight (b : SpTowerShriek.Base l E) (o : SpTowerShriek.Operations l E b)
    {T Y : Scheme.{u}} (p : T ⟶ Y) (w : SpChartAdmissibility.Twists l E T) (d : ℕ) :=
  SpTowerShriek.pull l E b (o.geometry p) ⋙ twistShift l E b w d

/-- The displayed chart functor, with the two pullbacks kept in their stated order.
Source: H_U (blueprint: def-sp-coordinate-adjunction-categories). -/
def chartRight (b : SpTowerShriek.Base l E) (o : SpTowerShriek.Operations l E b)
    {U T Y : Scheme.{u}} (e : U ⟶ T) (p : T ⟶ Y)
    (w : SpChartAdmissibility.Twists l E U) (d : ℕ) :=
  SpTowerShriek.pull l E b (o.geometry p) ⋙
    SpTowerShriek.pull l E b (o.geometry e) ⋙ twistShift l E b w d

/-- Finite tensor by the actual evaluated degree-zero line. Its identification with
A_(n+1)(d) is the specified sheaf-level comparison w.level, not a chosen derived lift.
Source: finite chart operations (blueprint: def-sp-coordinate-adjunction-categories). -/
def finiteTwistShift (b : SpTowerShriek.Base l E) {T : Scheme.{u}}
    (w : SpChartAdmissibility.Twists l E T) (d n : ℕ) :=
  Prod.sectL (proEtaleDerivedCategory T (SpTowerShriek.R l E n))
      ((SpTowerShriek.Ev l E T n).obj
        ((DerivedCategory.singleFunctor (SpTowerShriek.S l E T) 0).obj (w.tower d))) ⋙
    ((b.calculus T).levelClosed n).tensor

/-- Finite projection right functor, using the same shift as the tower functor.
Source: Levels (blueprint: def-sp-coordinate-adjunction-categories). -/
def finiteProjectionRight (b : SpTowerShriek.Base l E) {T Y : Scheme.{u}}
    (p : T ⟶ Y) (w : SpChartAdmissibility.Twists l E T) (d n : ℕ) :=
  proEtaleConstantRingDerivedPullback (SpTowerShriek.R l E n) p ⋙
    finiteTwistShift l E b w d n ⋙ shiftFunctor _ (2 * (d : ℤ))

/-- Finite chart right functor. Source: Levels
(blueprint: def-sp-coordinate-adjunction-categories). -/
def finiteChartRight (b : SpTowerShriek.Base l E) {U T Y : Scheme.{u}}
    (e : U ⟶ T) (p : T ⟶ Y) (w : SpChartAdmissibility.Twists l E U) (d n : ℕ) :=
  proEtaleConstantRingDerivedPullback (SpTowerShriek.R l E n) p ⋙
    proEtaleConstantRingDerivedPullback (SpTowerShriek.R l E n) e ⋙
      finiteTwistShift l E b w d n ⋙ shiftFunctor _ (2 * (d : ℤ))


/-- Reuse the section-normalized realization to express the displayed right functor
in the original strict tower category. Source: Local pairs
(blueprint: def-sp-coordinate-adjunction-categories). -/
def originalProjectionRight (b : SpTowerShriek.Base l E)
    (o : SpTowerShriek.Operations l E b) (q : SpTowerCalculus.Coordinates l E b)
    {T Y : Scheme.{u}} (p : T ⟶ Y) (w : SpChartAdmissibility.Twists l E T) (d : ℕ) :=
  (SpTowerCalculus.realization l E b Y (q.abelian Y)).functor ⋙
    projectionRight l E b o p w d ⋙
      (SpTowerCalculus.realization l E b T (q.abelian T)).inverse

/-- The same transport for the full chart. Source: Local pairs
(blueprint: def-sp-coordinate-adjunction-categories). -/
def originalChartRight (b : SpTowerShriek.Base l E)
    (o : SpTowerShriek.Operations l E b) (q : SpTowerCalculus.Coordinates l E b)
    {U T Y : Scheme.{u}} (e : U ⟶ T) (p : T ⟶ Y)
    (w : SpChartAdmissibility.Twists l E U) (d : ℕ) :=
  (SpTowerCalculus.realization l E b Y (q.abelian Y)).functor ⋙
    chartRight l E b o e p w d ⋙
      (SpTowerCalculus.realization l E b U (q.abelian U)).inverse

/-- The actual finite evaluation, restricted to the full constructible category.
The level property is literally a conjunct of the recorded uniform predicate.
Source: Levels (blueprint: def-sp-coordinate-adjunction-categories). -/
def evaluation (b : SpTowerShriek.Base l E) (q : SpTowerCalculus.Coordinates l E b)
    (T : Scheme.{u}) (n : ℕ) : SpTowerCalculus.C l E b q T ⥤
      spFiniteConstructibleTorCategory T (SpTowerShriek.R l E n) :=
  ObjectProperty.lift _
    (SpTowerCalculus.inclusion l E b q T ⋙
      spDerivedCoefficientEvaluation l E T (q.abelian T) n) (fun M ↦ M.property.1 n)

/-- Exact tower unit/counit compatibility, including both transpose operations.
The finite adjunction is on *all* finite constructible finite-Tor objects, rather
than just the image of evaluation. Source: Levels
(blueprint: def-sp-coordinate-adjunction-categories). -/
structure LevelCompatibility (b : SpTowerShriek.Base l E)
    (q : SpTowerCalculus.Coordinates l E b) {U Y : Scheme.{u}}
    {F : spDerivedCoefficientTowers l E U (q.abelian U) ⥤
      spDerivedCoefficientTowers l E Y (q.abelian Y)}
    {G : spDerivedCoefficientTowers l E Y (q.abelian Y) ⥤
      spDerivedCoefficientTowers l E U (q.abelian U)}
    (a : RestrictedPair (spConstructibleTorTowers l E U (q.abelian U))
      (spConstructibleTorTowers l E Y (q.abelian Y)) F G)
    (n : ℕ) (Fn : proEtaleDerivedCategory U (SpTowerShriek.R l E n) ⥤
      proEtaleDerivedCategory Y (SpTowerShriek.R l E n))
    (Gn : proEtaleDerivedCategory Y (SpTowerShriek.R l E n) ⥤
      proEtaleDerivedCategory U (SpTowerShriek.R l E n)) where
  finite : RestrictedPair (spFiniteConstructibleTor U (SpTowerShriek.R l E n))
    (spFiniteConstructibleTor Y (SpTowerShriek.R l E n)) Fn Gn
  left : F ⋙ spDerivedCoefficientEvaluation l E Y (q.abelian Y) n ≅
    spDerivedCoefficientEvaluation l E U (q.abelian U) n ⋙ Fn
  right : G ⋙ spDerivedCoefficientEvaluation l E U (q.abelian U) n ≅
    spDerivedCoefficientEvaluation l E Y (q.abelian Y) n ⋙ Gn
  unit : ∀ M : SpTowerCalculus.C l E b q U,
    (spDerivedCoefficientEvaluation l E U (q.abelian U) n).map (a.unit M) ≫
      right.hom.app (F.obj M.obj) ≫ Gn.map (left.hom.app M.obj) =
    finite.unit ((evaluation l E b q U n).obj M)
  counit : ∀ K : SpTowerCalculus.C l E b q Y,
    Fn.map (right.hom.app K.obj) ≫ finite.counit ((evaluation l E b q Y n).obj K) =
      left.inv.app (G.obj K.obj) ≫
        (spDerivedCoefficientEvaluation l E Y (q.abelian Y) n).map (a.counit K)
  transpose : ∀ (M : SpTowerCalculus.C l E b q U) (K : SpTowerCalculus.C l E b q Y)
    (f : F.obj M.obj ⟶ K.obj),
    (spDerivedCoefficientEvaluation l E U (q.abelian U) n).map
        (a.homEquiv M K f) ≫ right.hom.app K.obj =
      finite.homEquiv ((evaluation l E b q U n).obj M)
        ((evaluation l E b q Y n).obj K)
        (left.inv.app M.obj ≫
          (spDerivedCoefficientEvaluation l E Y (q.abelian Y) n).map f)
  inverse_transpose : ∀ (M : SpTowerCalculus.C l E b q U)
    (K : SpTowerCalculus.C l E b q Y) (f : M.obj ⟶ G.obj K.obj),
    left.inv.app M.obj ≫ (spDerivedCoefficientEvaluation l E Y (q.abelian Y) n).map
        ((a.homEquiv M K).symm f) =
      (finite.homEquiv ((evaluation l E b q U n).obj M)
        ((evaluation l E b q Y n).obj K)).symm
        ((spDerivedCoefficientEvaluation l E U (q.abelian U) n).map f ≫ right.hom.app K.obj)

/-- The original uniformly bounded full domain, as a reusable predicate only.
Source: standing convention (blueprint: def-sp-coordinate-adjunction-categories). -/
abbrev P (b : SpTowerShriek.Base l E) (q : SpTowerCalculus.Coordinates l E b)
    (T : Scheme.{u}) := spConstructibleTorTowers l E T (q.abelian T)

/-- A chart's actual tower adjunction, on the full subcategories in the statement.
Source: first display (blueprint: def-sp-coordinate-adjunction-categories). -/
abbrev ChartPair (b : SpTowerShriek.Base l E) (o : SpTowerShriek.Operations l E b)
    (q : SpTowerCalculus.Coordinates l E b) {U T Y : Scheme.{u}}
    (e : U ⟶ T) (p : T ⟶ Y) (c : Compactification (e ≫ p))
    (w : SpChartAdmissibility.Twists l E U) (d : ℕ) :=
  RestrictedPair (P l E b q U) (P l E b q Y) (SpTowerCalculus.F l E b o q c)
    (originalChartRight l E b o q e p w d)

/-- The projection specialization. The compactification is independent of coefficients.
Source: ordered integration (blueprint: def-sp-coordinate-adjunction-categories). -/
abbrev ProjectionPair (b : SpTowerShriek.Base l E) (o : SpTowerShriek.Operations l E b)
    (q : SpTowerCalculus.Coordinates l E b) {T Y : Scheme.{u}}
    (p : T ⟶ Y) (c : Compactification p) (w : SpChartAdmissibility.Twists l E T) (d : ℕ) :=
  RestrictedPair (P l E b q T) (P l E b q Y) (SpTowerCalculus.F l E b o q c)
    (originalProjectionRight l E b o q p w d)

/-- The ordered coordinate model's projection. Source: Local pairs, iteration;
the canonical affineTraceAffineSpaceIso identifies it with p_d.
(blueprint: def-sp-coordinate-adjunction-categories). -/
abbrev space (Y : Scheme.{u}) (d : ℕ) := affineTraceTower Y d

/-- Projection from the existing ordered coordinate model. At d=0 it is literally id.
Source: Local pairs (blueprint: def-sp-coordinate-adjunction-categories). -/
abbrev proj (Y : Scheme.{u}) (d : ℕ) := affineTraceProjection Y d


/-- Cancel the actual realization counit after a compactification composite.
This is the fixed comparison used before applying the projective-line Hom bijection.
Source: affine-line Hom display (blueprint: def-sp-coordinate-adjunction-categories). -/
def supportRealization (b : SpTowerShriek.Base l E) (o : SpTowerShriek.Operations l E b)
    (q : SpTowerCalculus.Coordinates l E b) {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f) :
    SpTowerCalculus.F l E b o q c ⋙
        (SpTowerCalculus.realization l E b Y (q.abelian Y)).functor ≅
      (SpTowerCalculus.realization l E b X (q.abelian X)).functor ⋙
        SpTowerShriek.F l E b o c :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _
      (Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft _
          (SpTowerCalculus.realization l E b Y (q.abelian Y)).counitIso ≪≫
            Functor.rightUnitor _)

/-- The forward realization of a right-functor value, using its counit only.
Source: actual coordinate transports (blueprint: def-sp-coordinate-adjunction-categories). -/
def rightRealization (b : SpTowerShriek.Base l E) (q : SpTowerCalculus.Coordinates l E b)
    {X Y : Scheme.{u}} (G : SpTowerShriek.D l E Y ⥤ SpTowerShriek.D l E X)
    (K : spDerivedCoefficientTowers l E Y (q.abelian Y)) :
    (SpTowerCalculus.realization l E b X (q.abelian X)).functor.obj
        ((SpTowerCalculus.realization l E b X (q.abelian X)).inverse.obj
          (G.obj ((SpTowerCalculus.realization l E b Y (q.abelian Y)).functor.obj K))) ≅
      G.obj ((SpTowerCalculus.realization l E b Y (q.abelian Y)).functor.obj K) :=
  (SpTowerCalculus.realization l E b X (q.abelian X)).counitIso.app _

/-- The exact Hom-coordinate change for the displayed affine-line composite. No
choice of a Hom lift is made: the section-preserving realization is fully faithful.
Source: affine-line display (blueprint: def-sp-coordinate-adjunction-categories). -/
def realizedTranspose (b : SpTowerShriek.Base l E)
    (q : SpTowerCalculus.Coordinates l E b) {X Y : Scheme.{u}}
    (G : SpTowerShriek.D l E Y ⥤ SpTowerShriek.D l E X)
    (M : spDerivedCoefficientTowers l E X (q.abelian X))
    (K : spDerivedCoefficientTowers l E Y (q.abelian Y))
    (f : M ⟶ (SpTowerCalculus.realization l E b X (q.abelian X)).inverse.obj
      (G.obj ((SpTowerCalculus.realization l E b Y (q.abelian Y)).functor.obj K))) :=
  (SpTowerCalculus.realization l E b X (q.abelian X)).functor.map f ≫
    (rightRealization l E b q G K).hom

/-- Natural bijections on the full domains with the specified composite counit.
This equation fixes the composite by actual arrows before evaluation.
Source: chart counit display (blueprint: def-sp-coordinate-adjunction-categories). -/
def CompositeEquation {A : Type v} {B : Type w} {C : Type z}
    [Category.{v'} A] [Category.{w'} B] [Category.{z'} C]
    (PA : ObjectProperty A) (PB : ObjectProperty B) (PC : ObjectProperty C)
    (F : A ⥤ B) (G : B ⥤ A) (H : B ⥤ C) (I : C ⥤ B)
    (J : A ⥤ C) (R : C ⥤ A)
    (a : RestrictedPair PA PB F G) (b : RestrictedPair PB PC H I)
    (c : RestrictedPair PA PC J R)
    (alpha : PA.ι ⋙ F ⋙ H ≅ PA.ι ⋙ J) (beta : I ⋙ G ≅ R) : Prop :=
  ∀ K : PC.FullSubcategory,
    c.counit K =
      J.map (beta.inv.app K.obj) ≫
        alpha.inv.app ⟨G.obj (I.obj K.obj),
          a.right_closed ⟨I.obj K.obj, b.right_closed K⟩⟩ ≫
        H.map (a.counit ⟨I.obj K.obj, b.right_closed K⟩) ≫ b.counit K


/-- Separated finite-type schemes over the stated field, retaining their structure map.
Source: standing convention (blueprint: def-sp-coordinate-adjunction-categories). -/
abbrev Bases (k : Type u) [Field k] :=
  {T : Over (Spec (.of k)) //
    IsSeparated T.hom ∧ LocallyOfFiniteType T.hom ∧ QuasiCompact T.hom}

/-- The structure map retained by a bundled base. Source: standing convention
(blueprint: def-sp-coordinate-adjunction-categories). -/
instance baseOver {k : Type u} [Field k] (T : Bases k) :
    T.val.left.Over (Spec (.of k)) := ⟨T.val.hom⟩

/-- The separatedness already present in Bases. Source: standing convention
(blueprint: def-sp-coordinate-adjunction-categories). -/
instance baseSeparated {k : Type u} [Field k] (T : Bases k) :
    IsSeparated (T.val.left ↘ Spec (.of k)) :=
  T.property.1

/-- The local finite-type property already present in Bases. Source: standing convention
(blueprint: def-sp-coordinate-adjunction-categories). -/
instance baseFiniteType {k : Type u} [Field k] (T : Bases k) :
    LocallyOfFiniteType (T.val.left ↘ Spec (.of k)) := T.property.2.1

/-- The quasi-compactness already present in Bases. Source: standing convention
(blueprint: def-sp-coordinate-adjunction-categories). -/
instance baseCompact {k : Type u} [Field k] (T : Bases k) :
    QuasiCompact (T.val.left ↘ Spec (.of k)) :=
  T.property.2.2

/-- The ordinary Tate tower on schemes over the fixed ground field. The global
existence theorem is restricted to schemes where l is invertible; restriction to
k-schemes is supplied by restrictTwistFamily below.
Source: twists in Local pairs (blueprint: def-sp-coordinate-adjunction-categories). -/
abbrev TwistFamily (k : Type u) [Field k] :=
  ∀ (T : Scheme.{u}) [T.Over (Spec (.of k))], SpChartAdmissibility.Twists l E T

/-- Restrict an ell-invertible Tate family to schemes over a field in which ell is
a unit. Ring maps preserve units, including on empty schemes.
Source: Local pairs (blueprint: def-sp-coordinate-adjunction-categories). -/
def restrictTwistFamily {k : Type u} [Field k] (hl : IsUnit (l : k))
    (w : ∀ T : Scheme.{u}, IsUnit (l : Γ(T, ⊤)) → SpChartAdmissibility.Twists l E T) :
    TwistFamily l E k := fun T _ ↦ w T (by
  let g : k →+* Γ(T, ⊤) :=
    (T ↘ Spec (.of k)).appTop.hom.comp (Scheme.ΓSpecIso (.of k)).inv.hom
  simpa only [map_natCast] using hl.map g)

/-- The ordered coordinate space inherits the ground-field structure of its base.
Source: Local pairs (blueprint: def-sp-coordinate-adjunction-categories). -/
instance twistSpaceOver {k : Type u} [Field k] (Y : Scheme.{u})
    [Y.Over (Spec (.of k))] (d : ℕ) :
    (space Y d).Over (Spec (.of k)) := ⟨proj Y d ≫ (Y ↘ Spec (.of k))⟩

/-- A normalized projective-line presentation in the same geometric calculus.
The field equalities retain the actual trace and diagonal unit of the dependency.
Source: affine-line restriction (blueprint: def-sp-coordinate-adjunction-categories). -/
structure ProjectivePresentation (b : SpTowerShriek.Base l E)
    (o : SpTowerShriek.Operations l E b) (S : Scheme.{u}) where
  invertible : IsUnit (l : Γ(S, ⊤))
  presentation : SpTowerP1.Presentation l E S invertible
  base_eq : presentation.classes.base = b
  operations_eq : HEq presentation.operations o
  maps : SpTowerP1.Maps l E presentation
  adjunction : SpTowerP1.AdjunctionData l E maps

/-- Transport of the projective-line right functor through the specified base equality.
Source: affine-line Hom display (blueprint: def-sp-coordinate-adjunction-categories). -/
def projectiveRight {b : SpTowerShriek.Base l E} {o : SpTowerShriek.Operations l E b}
    {S : Scheme.{u}} (t : ProjectivePresentation l E b o S) :=
  t.presentation.G l E

/-- The normalized projective-line Hom bijection on ambient morphisms, restricted to
the dependency's bounded-below etale-origin domains.
Source: affine-line factor (blueprint: def-sp-coordinate-adjunction-categories). -/
def projectiveHom {b : SpTowerShriek.Base l E} {o : SpTowerShriek.Operations l E b}
    {S : Scheme.{u}} (t : ProjectivePresentation l E b o S)
    (M : SpTowerP1.C l E t.presentation.classes.base (ProjectiveLine S))
    (K : SpTowerP1.C l E t.presentation.classes.base S) :
    ((t.presentation.F l E).obj M.obj ⟶ K.obj) ≃
      (M.obj ⟶ (t.presentation.G l E).obj K.obj) :=
  (SpTowerP1.domain l E t.presentation.classes.base S).fullyFaithfulι.homEquiv.symm.trans
    ((t.adjunction.adjunction.homEquiv M K).trans
      (SpTowerP1.domain l E t.presentation.classes.base (ProjectiveLine S)).fullyFaithfulι.homEquiv)

/-- Exact open-adjunction Hom bijection in the ordinary derived tower category.
Source: affine-line second factor (blueprint: def-sp-coordinate-adjunction-categories). -/
def openHom (b : SpTowerShriek.Base l E) (o : SpTowerShriek.Operations l E b)
    (S : Scheme.{u}) (M : SpTowerShriek.D l E (AffineSpace PUnit.{u + 1} S))
    (K : SpTowerShriek.D l E (ProjectiveLine S)) :=
  (o.openOp (ProjectiveLine.affineChart S)).derivedAdjunction.homEquiv M K

/-- The ordered affine-line right composites, with literal identity at dimension zero.
Source: Local pairs, iteration (blueprint: def-sp-coordinate-adjunction-categories). -/
def orderedRight (b : SpTowerShriek.Base l E) (o : SpTowerShriek.Operations l E b)
    {k : Type u} [Field k] (w : TwistFamily l E k) (Y : Scheme.{u})
    [Y.Over (Spec (.of k))] :
    (d : ℕ) → SpTowerShriek.D l E Y ⥤ SpTowerShriek.D l E (space Y d)
  | 0 => 𝟭 _
  | d + 1 => orderedRight b o w Y d ⋙
      projectionRight l E b o
        (AffineSpace PUnit.{u + 1} (space Y d) ↘ space Y d)
        (w (space Y (d + 1))) 1

/-- The original-coordinate version of the ordered right composite.
Source: Local pairs (blueprint: def-sp-coordinate-adjunction-categories). -/
def originalOrderedRight (b : SpTowerShriek.Base l E)
    (o : SpTowerShriek.Operations l E b) (q : SpTowerCalculus.Coordinates l E b)
    {k : Type u} [Field k] (w : TwistFamily l E k) (Y : Scheme.{u})
    [Y.Over (Spec (.of k))] (d : ℕ) :=
  (SpTowerCalculus.realization l E b Y (q.abelian Y)).functor ⋙
    orderedRight l E b o w Y d ⋙
      (SpTowerCalculus.realization l E b (space Y d) (q.abelian (space Y d))).inverse

/-- The original structure map on the concrete ordered coordinate tower.
Source: ordered iteration (blueprint: def-sp-coordinate-adjunction-categories). -/
instance coordinateSpaceOver {k : Type u} [Field k] (Y : Bases k) (d : ℕ) :
    (space Y.val.left d).Over (Spec (.of k)) := ⟨proj Y.val.left d ≫ Y.val.hom⟩

/-- Ordered projections respect the retained ground-field structure.
Source: ordered iteration (blueprint: def-sp-coordinate-adjunction-categories). -/
instance coordinateProjectionOver {k : Type u} [Field k] (Y : Bases k) (d : ℕ) :
    (proj Y.val.left d).IsOver (Spec (.of k)) := ⟨rfl⟩

/-- The ordered space is separated over the ground field.
Source: standing convention (blueprint: def-sp-coordinate-adjunction-categories). -/
instance coordinateSeparated {k : Type u} [Field k] (Y : Bases k) (d : ℕ) :
    IsSeparated (space Y.val.left d ↘ Spec (.of k)) :=
  inferInstanceAs (IsSeparated (proj Y.val.left d ≫ (Y.val.left ↘ Spec (.of k))))

/-- The ordered space is locally of finite type over the ground field.
Source: standing convention (blueprint: def-sp-coordinate-adjunction-categories). -/
instance coordinateFiniteType {k : Type u} [Field k] (Y : Bases k) (d : ℕ) :
    LocallyOfFiniteType (space Y.val.left d ↘ Spec (.of k)) :=
  inferInstanceAs (LocallyOfFiniteType (proj Y.val.left d ≫ (Y.val.left ↘ Spec (.of k))))

/-- The ordered space is quasi-compact over the ground field.
Source: standing convention (blueprint: def-sp-coordinate-adjunction-categories). -/
instance coordinateCompact {k : Type u} [Field k] (Y : Bases k) (d : ℕ) :
    QuasiCompact (space Y.val.left d ↘ Spec (.of k)) :=
  inferInstanceAs (QuasiCompact (proj Y.val.left d ≫ (Y.val.left ↘ Spec (.of k))))

/-- A single ordered coordinate projection is a ground-field morphism.
Source: ordered iteration (blueprint: def-sp-coordinate-adjunction-categories). -/
instance coordinateStepOver {k : Type u} [Field k] (Y : Bases k) (d : ℕ) :
    (AffineSpace PUnit.{u + 1} (space Y.val.left d) ↘ space Y.val.left d).IsOver
      (Spec (.of k)) := ⟨rfl⟩

/-- Separatedness of a coordinate successor in its recursive affine presentation.
Source: ordered iteration (blueprint: def-sp-coordinate-adjunction-categories). -/
instance coordinateStepSeparated {k : Type u} [Field k] (Y : Bases k) (d : ℕ) :
    IsSeparated (AffineSpace PUnit.{u + 1} (space Y.val.left d) ↘ Spec (.of k)) :=
  inferInstanceAs (IsSeparated (space Y.val.left (d + 1) ↘ Spec (.of k)))

/-- Finite type of a coordinate successor in its recursive affine presentation.
Source: ordered iteration (blueprint: def-sp-coordinate-adjunction-categories). -/
instance coordinateStepFiniteType {k : Type u} [Field k] (Y : Bases k) (d : ℕ) :
    LocallyOfFiniteType (AffineSpace PUnit.{u + 1} (space Y.val.left d) ↘ Spec (.of k)) :=
  inferInstanceAs (LocallyOfFiniteType (space Y.val.left (d + 1) ↘ Spec (.of k)))

/-- Quasi-compactness of a coordinate successor in its recursive affine presentation.
Source: ordered iteration (blueprint: def-sp-coordinate-adjunction-categories). -/
instance coordinateStepCompact {k : Type u} [Field k] (Y : Bases k) (d : ℕ) :
    QuasiCompact (AffineSpace PUnit.{u + 1} (space Y.val.left d) ↘ Spec (.of k)) :=
  inferInstanceAs (QuasiCompact (space Y.val.left (d + 1) ↘ Spec (.of k)))

/-- The standard affine-coordinate base, retaining the original k-structure.
Source: ordered iteration (blueprint: def-sp-coordinate-adjunction-categories). -/
def coordinateBase {k : Type u} [Field k] (Y : Bases k) (d : ℕ) : Bases k :=
  ⟨Over.mk (proj Y.val.left d ≫ Y.val.hom),
    inferInstanceAs (IsSeparated (proj Y.val.left d ≫
      (Y.val.left ↘ Spec (.of k)))),
    inferInstanceAs (LocallyOfFiniteType (proj Y.val.left d ≫
      (Y.val.left ↘ Spec (.of k)))),
    inferInstanceAs (QuasiCompact (proj Y.val.left d ≫
      (Y.val.left ↘ Spec (.of k))))⟩

/-- The projective direct image is precisely the operation of the common calculus.
This is an equality transport, not an independently chosen comparison.
Source: affine-line factor (blueprint: def-sp-coordinate-adjunction-categories). -/
def projectivePush {b : SpTowerShriek.Base l E} {o : SpTowerShriek.Operations l E b}
    {S : Scheme.{u}} (t : ProjectivePresentation l E b o S) :
    t.presentation.F l E ≅
      SpTowerShriek.push l E b (o.geometry (ProjectiveLine S ↘ S)) := by
  rcases t with ⟨hinv, p, hb, ho, m, a⟩
  cases hb
  cases ho
  exact Iso.refl _

/-- The projection full category at the indicated ordered stage.
Source: iteration (blueprint: def-sp-coordinate-adjunction-categories). -/
abbrev stageCategory (b : SpTowerShriek.Base l E)
    (q : SpTowerCalculus.Coordinates l E b) (Y : Scheme.{u}) (d : ℕ) :=
  (P l E b q (space Y d)).FullSubcategory

/-- The right functor comparison after a canonical coordinate realization cancellation.
Source: composition of actual tower arrows
(blueprint: def-sp-coordinate-adjunction-categories). -/
def transportedIso (b : SpTowerShriek.Base l E)
    (q : SpTowerCalculus.Coordinates l E b) {X Y : Scheme.{u}}
    {F G : SpTowerShriek.D l E Y ⥤ SpTowerShriek.D l E X} (a : F ≅ G) :=
  Functor.isoWhiskerLeft (SpTowerCalculus.realization l E b Y (q.abelian Y)).functor
    (Functor.isoWhiskerRight a
      (SpTowerCalculus.realization l E b X (q.abelian X)).inverse)

/-- Canonical finite evaluation of compact support in the actual constant-ring coordinates.
Every factor is the previously normalized comparison.
Source: Levels (blueprint: def-sp-coordinate-adjunction-categories). -/
def supportEvaluation (b : SpTowerShriek.Base l E)
    (o : SpTowerShriek.Operations l E b) (q : SpTowerCalculus.Coordinates l E b)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) (n : ℕ) :
    SpTowerCalculus.F l E b o q c ⋙
        spDerivedCoefficientEvaluation l E Y (q.abelian Y) n ≅
      spDerivedCoefficientEvaluation l E X (q.abelian X) n ⋙
        SpTowerShriek.finiteF l E b c n :=
  Functor.isoWhiskerLeft _ (SpTowerCalculus.levelComparison l E b q Y n).symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (supportRealization l E b o q c) _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (SpTowerShriek.Fcomparison l E b o c n) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (SpTowerCalculus.levelComparison l E b q X n) _

/-- The actual étale sum-extension pair, including the restricted ambient counit.
Source: Local pairs, fibre summation
(blueprint: def-sp-coordinate-adjunction-categories). -/
def etalePair (k : Type u) [Field k] (b : SpTowerShriek.Base l E)
    (o : SpTowerShriek.Operations l E b) (q : SpTowerCalculus.Coordinates l E b)
    (z : SpTowerCalculus.FiniteCoordinates l E)
    (h : SpTowerCalculus.Preservation l E k b o q)
    (cal : SpTowerCalculus.Calculus l E k b o q z h)
    (U T : Bases k) (e : U.val.left ⟶ T.val.left)
    [e.IsOver (Spec (.of k))] [Etale e] [IsSeparated e]
    [LocallyOfFiniteType e] [QuasiCompact e] :
    RestrictedPair (P l E b q U.val.left) (P l E b q T.val.left)
      (SpTowerCalculus.etaleExtension l E b o q z (cal.etale.etale e))
      (SpTowerCalculus.etalePullback l E b o q e) where
  left_closed := (cal.etale.etale_preserves e).1
  right_closed := (cal.etale.etale_preserves e).2
  adjunction := SpTowerCalculus.restrictedEtaleAdjunction l E b o q z
    (cal.etale.etale e) (cal.etale.etale_preserves e).1 (cal.etale.etale_preserves e).2


end AlgebraicGeometry.ProEtale.SpCoordinateAdjunction
