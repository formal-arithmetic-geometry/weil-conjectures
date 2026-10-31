/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SmoothPurityTowerGammaData
public import WeilConjectures.AlgebraicGeometry.SmoothPurityTowerGluing
public import WeilConjectures.AlgebraicGeometry.SmoothPurityTowerShriekLevels
public import WeilConjectures.AlgebraicGeometry.SmoothPurityCoefficientTowers
public import WeilConjectures.AlgebraicGeometry.SmoothPurityNormalizedTowers
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Tensor
public import WeilConjectures.AlgebraicGeometry.PurityDiagonalDualizingObject
public import WeilConjectures.AlgebraicGeometry.FiniteTorAmplitudeSites
public import WeilConjectures.AlgebraicGeometry.DerivedPullbackTensorHom
public import WeilConjectures.AlgebraicGeometry.IntrinsicCoefficientTwistsUnrestricted
public import WeilConjectures.AlgebraicGeometry.FiniteFieldFiberSupplement
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Noetherian

/-! # Data for twisted pullback bounds and the tower projection domain

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/sk-prop-sp-tower-geometric/
sk-prop-sp-tower-geometric-gamma.proof.md, paragraph (2)
(blueprint: def-sp-twisted-pullback-tower-domain-data).

Natural indices n denote the positive exponents n+1. The published section-preserving
realization is an equivalence of ordinary derived categories of strict varying-ring
towers. P uses the published ordered tensor presentation of the Tate twist and shift.
Only definitions from the gamma module are used; its purity theorem is not an input.
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

namespace AlgebraicGeometry.ProEtale.SpTwistedTowerDomain

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (b : SpTowerShriek.Base l E) (o : SpTowerShriek.Operations l E b)
  (q : SpTowerCalculus.Coordinates l E b)

/-- The pullback B=f* K in the specified ordinary tower coordinates.
Source: gamma proof (2) (blueprint: def-sp-twisted-pullback-tower-domain-data). -/
abbrev B {X Y : Scheme.{u}} (f : X ⟶ Y) (K : SpTowerCalculus.C l E b q Y) :=
  (SpTowerShriek.pull l E b (o.geometry f)).obj
    ((SpTowerGamma.realization l E b q Y).obj K)

/-- The coefficient unit in the original strict-tower full subcategory.
The proof argument only types the already specified coefficient object.
Source: gamma proof (2) (blueprint: def-sp-twisted-pullback-tower-domain-data). -/
abbrev U (T : Scheme.{u})
    (hU : spConstructibleTorTowers l E T (q.abelian T)
      (SpTowerGamma.originalUnit l E b q T)) : SpTowerCalculus.C l E b q T :=
  ⟨SpTowerGamma.originalUnit l E b q T, hU⟩

/-- Omega is the GIVEN right adjoint applied to the coefficient unit.
Source: gamma proof (2) (blueprint: def-sp-twisted-pullback-tower-domain-data). -/
abbrev omega {X Y : Scheme.{u}}
    (G : SpTowerCalculus.C l E b q Y ⥤ SpTowerCalculus.C l E b q X)
    (hU : spConstructibleTorTowers l E Y (q.abelian Y)
      (SpTowerGamma.originalUnit l E b q Y)) :=
  (SpTowerGamma.exceptional l E b q G).obj (U l E b q Y hU)

/-- The P of the node, in its existing ordered shifted-Tate tensor presentation.
Source: gamma proof (2) (blueprint: def-sp-twisted-pullback-tower-domain-data). -/
abbrev P {X Y : Scheme.{u}} (f : X ⟶ Y)
    (w : SpChartAdmissibility.Twists l E X) (d : ℕ)
    (K : SpTowerCalculus.C l E b q Y) :=
  (SpTowerGamma.source l E b o q f w d).obj K

/-- The Q of the node, with the ordinary uncompleted derived tensor.
Source: gamma proof (2) (blueprint: def-sp-twisted-pullback-tower-domain-data). -/
abbrev Q {X Y : Scheme.{u}} (f : X ⟶ Y)
    (G : SpTowerCalculus.C l E b q Y ⥤ SpTowerCalculus.C l E b q X)
    (hU : spConstructibleTorTowers l E Y (q.abelian Y)
      (SpTowerGamma.originalUnit l E b q Y)) (K : SpTowerCalculus.C l E b q Y) :=
  (SpTowerGamma.tensorSource l E b o q f (omega l E b q G hU)).obj K

/-- The specified map 1 tensor a; twist reassociation is built into P's ordered model.
Source: gamma proof (2) (blueprint: def-sp-twisted-pullback-tower-domain-data). -/
def orientationMap {X Y : Scheme.{u}} (f : X ⟶ Y)
    (w : SpChartAdmissibility.Twists l E X) (d : ℕ)
    (G : SpTowerCalculus.C l E b q Y ⥤ SpTowerCalculus.C l E b q X)
    (hU : spConstructibleTorTowers l E Y (q.abelian Y)
      (SpTowerGamma.originalUnit l E b q Y))
    (a : SpTowerGamma.orderedLine l E b X w d ≅ omega l E b q G hU)
    (K : SpTowerCalculus.C l E b q Y) : P l E b o q f w d K ⟶ Q l E b o q f G hU K :=
  (SpTowerShriek.tensor l E b X).map (Prod.mkHom (𝟙 (B l E b o q f K)) a.hom)

/-- A bounded constructible finite-Tor etale origin at ONE level, with its specified
Tor interval. There is no equation relating origins at distinct indices.
Source: gamma proof (2) (blueprint: def-sp-twisted-pullback-tower-domain-data). -/
def OriginIn (T : Scheme.{u}) (n : ℕ) (C : SpTowerShriek.D l E T) (a c : ℤ) : Prop :=
  ∃ z : SpTowerShriek.Origin l E b T n C,
    Etale.DerivedCategory.isBoundedConstructible (ULift.{u + 1} (SpTowerShriek.R l E n))
      T z.witness.complex.obj ∧
    Etale.DerivedCategory.hasTorAmplitudeIn (ULift.{u + 1} (SpTowerShriek.R l E n))
      T a c z.witness.complex.obj

variable (D : FiniteFieldDatum.{u}) (X Y : Over (Spec (CommRingCat.of D.k)))
  [IsSeparated X.hom] [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
  [IsSeparated Y.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
  (f : X ⟶ Y) (c : Compactification f.left) (d : ℕ)
  (w : SpChartAdmissibility.Twists l E X.left)
  (hF : ∀ M : SpTowerCalculus.C l E b q X.left,
    spConstructibleTorTowers l E Y.left (q.abelian Y.left)
      ((SpTowerCalculus.F l E b o q c).obj M.obj))
  (G : SpTowerCalculus.C l E b q Y.left ⥤ SpTowerCalculus.C l E b q X.left)
  (adj : SpTowerGluing.support l E b o q c hF ⊣ G)
  (lv : SpTowerGluing.Levels l E b o q c hF G adj)
  (hU : spConstructibleTorTowers l E Y.left (q.abelian Y.left)
    (SpTowerGamma.originalUnit l E b q Y.left))

/-- The finite-level hypothesis on the given orientation. Its normalized comparison
words are the published ones, and alpha satisfies the diagonal/DNC/Kummer equation.
No tower purity or projection-invertibility assertion is included in this hypothesis.
Source: gamma proof (1)--(2) (blueprint: def-sp-twisted-pullback-tower-domain-data). -/
def DiagonalLevels
    (roots : SpCoordinateAdjunction.RootLines l E X.left)
    (unitsX : ∀ n : ℕ, IsUnit ((l ^ (n + 1) : ℕ) : Γ(X.left, ⊤)))
    (cc : ∀ n : ℕ, SpTowerP1.CoefficientCoordinates l E n X.left (unitsX n))
    (tc : ∀ n : ℕ, SpTowerP1.TensorCoordinates l E n b X.left)
    (unitsY : ∀ n : ℕ, IsUnit ((l ^ (n + 1) : ℕ) : Γ(Y.left, ⊤)))
    (cy : ∀ n : ℕ, SpTowerP1.CoefficientCoordinates l E n Y.left (unitsY n))
    (a : SpTowerGamma.orderedLine l E b X.left w d ≅ omega l E b q G hU) : Prop :=
  letI := isNoetherian_of_locallyOfFiniteType X.hom
  letI : HasCompactification (c.i ≫ c.g) :=
    ⟨⟨c.Z, c.g, c.i, rfl, inferInstance, inferInstance⟩⟩
  ∀ n : ℕ,
    ∃ dg : Etale.FiniteRingSectionDeformation.Geometry d
      (pullback.fst (c.i ≫ c.g) (c.i ≫ c.g)) (pullback.diagonal (c.i ≫ c.g)),
    ∃ alpha : Etale.dualizingComplex (SpTowerP1.levelRing l E n)
        (c.i ≫ c.g) ≅
      Etale.FiniteSmoothPurity.line (SpTowerP1.levelRing l E n) (l ^ (n + 1))
        (SpTowerP1.levelAnnihilates l E n) X.left d,
    Etale.FiniteSmoothPurity.OrientationNormalized (SpTowerP1.levelRing l E n)
      (l ^ (n + 1)) (pow_pos (Fact.out : l.Prime).pos _) (SpTowerP1.levelAnnihilates l E n)
      (c.i ≫ c.g) d dg (unitsX n) alpha ∧
    ∃ ui : (lv.realization n).origin.obj
        ((SpTowerGluing.level l E b q Y.left n).obj (U l E b q Y.left hU)) ≅
      Etale.ordinaryFiniteUnit (SpTowerP1.levelRing l E n) Y.left,
    (SpTowerP1.nu l E n Y.left).map ui.hom ≫
        (SpTowerP1.unitWord l E n Y.left (cy n)).comparison =
      (SpTowerGamma.inputWord l E b o q c hF G adj lv n
        (U l E b q Y.left hU)).comparison ≫
        (SpTowerShriek.Ev l E Y.left n).map
          ((SpTowerCalculus.realization l E b Y.left (q.abelian Y.left)).counitIso.hom.app
            (SpTowerGamma.unit l E Y.left)) ∧
    SpTowerP1.WordComparison l E n
      (SpTowerGamma.coefficientWord l E b X.left w roots n (unitsX n) (cc n) (tc n) d)
      (SpTowerGamma.targetWord l E b o q c hF G adj lv n (U l E b q Y.left hU)) a.hom
      (alpha.inv ≫ (SpTowerGamma.finiteRightComparison (SpTowerShriek.R l E n) c.i c.g
        (lv.finite_closed n) (lv.right n) (lv.adjunction n) (lv.realization n)).inv.app _ ≫
        (lv.realization n).right.map ui.inv)

/-- The clauses of the tower-domain lemma, using precisely the ordinary tensor,
projection and full-subcategory predicates of the recorded dependencies.
Source: gamma proof (2) (blueprint: def-sp-twisted-pullback-tower-domain-data). -/
structure Conclusion (K : SpTowerCalculus.C l E b q Y.left) (a z : ℤ)
    (orientation : SpTowerGamma.orderedLine l E b X.left w d ≅ omega l E b q G hU) : Prop where
  noetherianX : IsNoetherian X.left
  noetherianY : IsNoetherian Y.left
  compactX : CompactSpace X.left
  compactY : CompactSpace Y.left
  quasiSeparatedX : QuasiSeparatedSpace X.left
  quasiSeparatedY : QuasiSeparatedSpace Y.left
  coefficients : ∀ n : ℕ, Finite (SpTowerShriek.R l E n) ∧
    IsNoetherianRing (SpTowerShriek.R l E n)
  pullback_bounds : SpChartAdmissibility.bounds l E X.left (B l E b o q f.left K) a z a z
  lines : ∀ n : ℕ,
    IsConstructibleProEtaleModuleSheaf X.left (SpTowerShriek.R l E n)
      (spEllTwistLine l E X.left n (d : ℤ)) ∧
    (spEllTwistLine l E X.left n (d : ℤ)).IsFiniteLocallyFreeOfRank 1 ∧
    (d = 0 → Nonempty (spEllTwistLine l E X.left n (d : ℤ) ≅
      SheafOfModules.unit ((sheafCompose (ProEt.topology X.left)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (SpTowerShriek.B l E X.left n))))
  P_mem : spConstructibleTorTowers l E X.left (q.abelian X.left)
    ((SpTowerCalculus.realization l E b X.left (q.abelian X.left)).inverse.obj
      (P l E b o q f.left w d K))
  Q_mem : spConstructibleTorTowers l E X.left (q.abelian X.left)
    ((SpTowerCalculus.realization l E b X.left (q.abelian X.left)).inverse.obj
      (Q l E b o q f.left G hU K))
  P_bounds : SpChartAdmissibility.bounds l E X.left (P l E b o q f.left w d K)
    (a - 2 * d) (z - 2 * d) (a - 2 * d) (z - 2 * d)
  Q_bounds : SpChartAdmissibility.bounds l E X.left (Q l E b o q f.left G hU K)
    (a - 2 * d) (z - 2 * d) (a - 2 * d) (z - 2 * d)
  orientation_iso : IsIso (orientationMap l E b o q f.left w d G hU orientation K)
  input_origins : ∀ n : ℕ, OriginIn l E b Y.left n
    ((SpTowerGamma.realization l E b q Y.left).obj K) a z
  dualizing_origins : ∀ n : ℕ, OriginIn l E b X.left n (omega l E b q G hU)
    (-2 * d) (-2 * d)
  input_lower : ((SpTowerGamma.realization l E b q Y.left).obj K).IsGE a
  dualizing_lower : (omega l E b q G hU).IsGE (-2 * d)
  projection_iso : IsIso (SpTowerShriek.projection l E b o c (omega l E b q G hU)
    ((SpTowerGamma.realization l E b q Y.left).obj K))
  projection_source_mem : spConstructibleTorTowers l E Y.left (q.abelian Y.left)
    ((SpTowerCalculus.realization l E b Y.left (q.abelian Y.left)).inverse.obj
      ((SpTowerShriek.tensor l E b Y.left).obj
        ((SpTowerShriek.F l E b o c).obj (omega l E b q G hU),
          (SpTowerGamma.realization l E b q Y.left).obj K)))
  projection_target_mem : spConstructibleTorTowers l E Y.left (q.abelian Y.left)
    ((SpTowerCalculus.realization l E b Y.left (q.abelian Y.left)).inverse.obj
      ((SpTowerShriek.F l E b o c).obj ((SpTowerShriek.tensor l E b X.left).obj
        (omega l E b q G hU, B l E b o q f.left K))))


end AlgebraicGeometry.ProEtale.SpTwistedTowerDomain

attribute [instance high] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
