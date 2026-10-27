module

public import Sheaf.Paper.FiniteFieldFiber
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Sheaf.Paper.PurityDiagonalDualizingObject
public import Sheaf.Paper.SmoothPurityCoefficientTowers
public import Sheaf.Paper.SmoothPurityCoefficientTowersAbelian
public import Sheaf.Paper.SmoothPurityNormalizedTowers
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Tensor
public import Sheaf.Paper.CohomologicalSmoothnessFiniteComparison
public import Sheaf.Paper.SmoothPurityTowerGluing
public import Sheaf.Paper.SmoothPurityTowerGamma
public import Sheaf.Paper.SmoothPurityMap
public import Sheaf.Paper.IntrinsicCoefficientTwistsUnrestricted
public import Sheaf.AlgebraicGeometry.UnboundedEtaleCompactSupportComparisons
public import Sheaf.SecSmoothPurity.FiniteGeneralRingData
public import Sheaf.Paper.TowerAdjointCompositorRealization
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Proper

/-! # Composition of smooth orientations and tensor maps

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/
sk-prop-sp-composition/sk-prop-sp-composition-factors.md
(blueprint: det-sp-composition-factors).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry.Scheme
namespace AlgebraicGeometry.ProEtale

namespace SpCompositionFactors
open MonoidalCategory WeilConjectures.PurityFiniteSetting

section Finite
variable (A : Type (u + 1)) [CommRing A] [Finite A]
  {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
  [HasCompactification f] [HasCompactification g] [HasCompactification (f ≫ g)]
  [QuasiCompact f] [QuasiCompact (f ≫ g)]

/-- The unique right-adjoint comparison of the canonical proper/open left compositor.
Source: composition-factors, c (blueprint: det-sp-composition-factors). -/
def finiteCompositor :
    Etale.rightDerivedUpperShriek (ModuleCat.{u + 1} A) (f ≫ g) ≅
      Etale.rightDerivedUpperShriek (ModuleCat.{u + 1} A) g ⋙
        Etale.rightDerivedUpperShriek (ModuleCat.{u + 1} A) f :=
  (Etale.rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} A) (f ≫ g)).rightAdjointUniq
    (((Etale.rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} A) f).comp
      (Etale.rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} A) g)).ofNatIsoLeft
        (Etale.unboundedEtaleLowerShriekCompIso A f g))

/-- The actual finite tensor mate, with outside coefficient first.
Source: composition-factors, t (blueprint: det-sp-composition-factors). -/
abbrev finiteTensor {U V : Scheme.{u}} (v : U ⟶ V) [HasCompactification v]
    (K : Etale.DerivedCategoryModule A V) :=
  Etale.smoothTensorDualityMap (ModuleCat.{u + 1} A) v
    (Etale.isIso_projectionMap_of_finite A v) K

/-- The coefficient rho before taking its inverse.
Source: composition-factors, rho (blueprint: det-sp-composition-factors). -/
abbrev finiteRho :=
  finiteTensor A f (Etale.dualizingComplex (ModuleCat.{u + 1} A) g)

/-- The specified coefficient identification c_1 followed by rho inverse.
Source: composition-factors, mu (blueprint: det-sp-composition-factors). -/
def finiteMu (hR : IsIso (finiteRho A f g)) :=
  letI := hR
  (finiteCompositor A f g).app (𝟙_ _) ≪≫ (asIso (finiteRho A f g)).symm

/-- Canonical shifted Tate splitting, in the order f*L_g tensor L_f.
The even shifts are already part of the ordered finite line construction.
Source: composition-factors, clause (1) (blueprint: det-sp-composition-factors). -/
def finiteLineSplit (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    (hY : IsUnit (N : Γ(Y, ⊤))) (e : ℕ) : ∀ d : ℕ,
    Etale.FiniteSmoothPurity.line A N hA X (d + e) ≅
      ((Etale.derivedTensor (ModuleCat.{u + 1} A) X).obj
        ((Etale.ordinaryFinitePullback A f).obj
          (Etale.FiniteSmoothPurity.line A N hA Y e))).obj
            (Etale.FiniteSmoothPurity.line A N hA X d)
  | 0 => eqToIso (congrArg (Etale.FiniteSmoothPurity.line A N hA X) (Nat.zero_add e)) ≪≫
      (Etale.vectorIntegrationBaseCoefficientPullback A N hA
        (Etale.projectiveLineTraceTransport N hN A hA) f hY e).symm ≪≫
      (Etale.derivedTensorRightUnitor (ModuleCat.{u + 1} A) X _).symm ≪≫
      ((Etale.derivedTensor (ModuleCat.{u + 1} A) X).obj _).mapIso
        (smoothPurityUnitIso A X).symm
  | d + 1 =>
      eqToIso (congrArg (Etale.FiniteSmoothPurity.line A N hA X) (Nat.succ_add d e)) ≪≫
      ((Etale.derivedTensor (ModuleCat.{u + 1} A) X).mapIso
        (finiteLineSplit N hN hA hY e d)).app
          ((Etale.ordinaryFiniteLine A N hA X)⟦(2 : ℤ)⟧) ≪≫
      Etale.derivedTensorAssociator (ModuleCat.{u + 1} A) X _ _ _

/-- Pullback composition, inverse tensor associator and inverse pullback tensorator.
This identifies h*K tensor (f*M tensor N) with f*(g*K tensor M) tensor N.
Source: composition-factors, clause (2) (blueprint: det-sp-composition-factors). -/
def finiteReassociate (K : Etale.DerivedCategoryModule A Z)
    (M : Etale.DerivedCategoryModule A Y) (N : Etale.DerivedCategoryModule A X) :=
  ((Etale.derivedTensor (ModuleCat.{u + 1} A) X).mapIso
      ((Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} A) f g).app K)).app
        (((Etale.derivedTensor (ModuleCat.{u + 1} A) X).obj
          ((Etale.ordinaryFinitePullback A f).obj M)).obj N) ≪≫
    (Etale.derivedTensorAssociator (ModuleCat.{u + 1} A) X _ _ _).symm ≪≫
    ((Etale.derivedTensor (ModuleCat.{u + 1} A) X).mapIso
      (Etale.leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} A) f
        ((Etale.ordinaryFinitePullback A g).obj K) M).symm).app N

/-- The three equations on the finite pro-etale category, written in its canonical
ordinary-etale origin coordinates and then mapped by nu*. Every input is still an
arbitrary intrinsic constructible finite-Tor pro-etale complex. The source comparison
is sourceToOrigin/sourceAtOriginIso of the recorded finite purity interface.
Source: composition-factors, clauses (1), (2), consequence
(blueprint: det-sp-composition-factors). -/
def FiniteEquations (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    (hY : IsUnit (N : Γ(Y, ⊤))) (d e : ℕ)
    (af : Etale.dualizingComplex (ModuleCat.{u + 1} A) f ≅
      Etale.FiniteSmoothPurity.line A N hA X d)
    (ag : Etale.dualizingComplex (ModuleCat.{u + 1} A) g ≅
      Etale.FiniteSmoothPurity.line A N hA Y e)
    (ah : Etale.dualizingComplex (ModuleCat.{u + 1} A) (f ≫ g) ≅
      Etale.FiniteSmoothPurity.line A N hA X (d + e)) : Prop :=
  ∃ hR : IsIso (finiteRho A f g),
    (Etale.FiniteSmoothPurity.comparison A X).map
        (ah.inv ≫ (finiteMu A f g hR).hom) =
      (Etale.FiniteSmoothPurity.comparison A X).map
        ((finiteLineSplit A f N hN hA hY e d).hom ≫
          ((Etale.derivedTensor (ModuleCat.{u + 1} A) X).map
            ((Etale.ordinaryFinitePullback A f).map ag.inv)).app _ ≫
          ((Etale.derivedTensor (ModuleCat.{u + 1} A) X).obj _).map af.inv) ∧
    ∀ (K : Etale.FiniteSmoothPurity.proCategory A Z),
      Etale.FiniteSmoothPurity.IsCtf A Z K →
      (Etale.FiniteSmoothPurity.comparison A X).map
          (((Etale.derivedTensor (ModuleCat.{u + 1} A) X).obj
              ((Etale.ordinaryFinitePullback A (f ≫ g)).obj
                ((Etale.FiniteSmoothPurity.origin A Z).obj K))).map
                ((finiteMu A f g hR).inv) ≫
            finiteTensor A (f ≫ g) ((Etale.FiniteSmoothPurity.origin A Z).obj K) ≫
            (finiteCompositor A f g).hom.app ((Etale.FiniteSmoothPurity.origin A Z).obj K)) =
        (Etale.FiniteSmoothPurity.comparison A X).map
          ((finiteReassociate A f g ((Etale.FiniteSmoothPurity.origin A Z).obj K)
            (Etale.dualizingComplex (ModuleCat.{u + 1} A) g)
            (Etale.dualizingComplex (ModuleCat.{u + 1} A) f)).hom ≫
            ((Etale.derivedTensor (ModuleCat.{u + 1} A) X).map
              ((Etale.ordinaryFinitePullback A f).map
                (finiteTensor A g ((Etale.FiniteSmoothPurity.origin A Z).obj K)))).app _ ≫
            finiteTensor A f
              ((Etale.rightDerivedUpperShriek (ModuleCat.{u + 1} A) g).obj
                ((Etale.FiniteSmoothPurity.origin A Z).obj K))) ∧
      (Etale.FiniteSmoothPurity.comparison A X).map
          (Etale.FiniteSmoothPurity.gamma A (f ≫ g) _ ah
              ((Etale.FiniteSmoothPurity.origin A Z).obj K) ≫
            (finiteCompositor A f g).hom.app ((Etale.FiniteSmoothPurity.origin A Z).obj K)) =
        (Etale.FiniteSmoothPurity.comparison A X).map
          (((Etale.derivedTensor (ModuleCat.{u + 1} A) X).obj
              ((Etale.ordinaryFinitePullback A (f ≫ g)).obj
                ((Etale.FiniteSmoothPurity.origin A Z).obj K))).map
              (finiteLineSplit A f N hN hA hY e d).hom ≫
            (finiteReassociate A f g ((Etale.FiniteSmoothPurity.origin A Z).obj K)
              (Etale.FiniteSmoothPurity.line A N hA Y e)
              (Etale.FiniteSmoothPurity.line A N hA X d)).hom ≫
            ((Etale.derivedTensor (ModuleCat.{u + 1} A) X).map
              ((Etale.ordinaryFinitePullback A f).map
                (Etale.FiniteSmoothPurity.gamma A g _ ag
                  ((Etale.FiniteSmoothPurity.origin A Z).obj K)))).app _ ≫
            Etale.FiniteSmoothPurity.gamma A f _ af
              ((Etale.rightDerivedUpperShriek (ModuleCat.{u + 1} A) g).obj
                ((Etale.FiniteSmoothPurity.origin A Z).obj K)))


/-- Composition of the specified diagonal orientations and tensor transposes, at every
finite ell-primary ring. Equalities are in the actual pro-etale derived category via
its canonical ordinary-etale coordinates, retaining every intrinsic Dctf input.
Source: composition-factors, clauses (1), (2), consequence
(blueprint: det-sp-composition-factors).

Proof:
1. lem-sp-composite-projection-coefficients supplies the domains and coherent invertible
projections. Finite general-ring purity at omega_g makes rho invertible.
2. lem-sp-composite-tensor-transpose and the counit-preserving compositor give clause (2).
3. At Z/ell^r use lem-sp-nested-affine-charts and lem-sp-nested-affine-orientation.
Remove the common even shift by lem-weil-pbc-derived-single-fully-faithful, and glue
with lem-pur-sheaf-hom-cover-gluing. This gives clause (1), including zero blocks.
4. lem-sp-orientation-scalar-propagation transfers that equality to A without flatness.
5. Substitute the orientation equality into clause (2), and use naturality of the
specified tensor mates. Twist and shift reassociation gives the final gamma equation.
The interchange of the two even shifts has sign +1. -/
theorem finite (D : WeilConjectures.FiniteFieldDatum.{u})
    (ell : ℕ) [Fact ell.Prime] (hne : ell ≠ D.p) (r : ℕ) (hr : 1 ≤ r)
    [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))] [Z.Over (Spec (.of D.k))]
    [IsSeparated (X ↘ Spec (.of D.k))] [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
    [QuasiCompact (X ↘ Spec (.of D.k))]
    [IsSeparated (Y ↘ Spec (.of D.k))] [LocallyOfFiniteType (Y ↘ Spec (.of D.k))]
    [QuasiCompact (Y ↘ Spec (.of D.k))]
    [IsSeparated (Z ↘ Spec (.of D.k))] [LocallyOfFiniteType (Z ↘ Spec (.of D.k))]
    [QuasiCompact (Z ↘ Spec (.of D.k))]
    [f.IsOver (Spec (.of D.k))] [g.IsOver (Spec (.of D.k))]
    [IsNoetherian X] [IsNoetherian Y] [IsSeparated f] [IsSeparated g]
    [QuasiCompact g] (d e : ℕ)
    [SmoothOfRelativeDimension d f] [SmoothOfRelativeDimension e g]
    (hA : ((ell ^ r : ℕ) : A) = 0)
    (df : Etale.FiniteRingSectionDeformation.Geometry d
      (pullback.fst f f) (pullback.diagonal f))
    (dg : Etale.FiniteRingSectionDeformation.Geometry e
      (pullback.fst g g) (pullback.diagonal g))
    (dh : Etale.FiniteRingSectionDeformation.Geometry (d + e)
      (pullback.fst (f ≫ g) (f ≫ g)) (pullback.diagonal (f ≫ g)))
    (af : Etale.dualizingComplex (ModuleCat.{u + 1} A) f ≅
      Etale.FiniteSmoothPurity.line A (ell ^ r) hA X d)
    (ag : Etale.dualizingComplex (ModuleCat.{u + 1} A) g ≅
      Etale.FiniteSmoothPurity.line A (ell ^ r) hA Y e)
    (ah : Etale.dualizingComplex (ModuleCat.{u + 1} A) (f ≫ g) ≅
      Etale.FiniteSmoothPurity.line A (ell ^ r) hA X (d + e))
    (_hf : Etale.FiniteSmoothPurity.OrientationNormalized A (ell ^ r)
      (pow_pos (Fact.out : ell.Prime).pos r) hA f d df
      ((finiteGeneralRingPrimeSetting D ell hne r hr).diagonalExponent_isUnit
        (X ↘ Spec (.of D.k))) af)
    (_hg : Etale.FiniteSmoothPurity.OrientationNormalized A (ell ^ r)
      (pow_pos (Fact.out : ell.Prime).pos r) hA g e dg
      ((finiteGeneralRingPrimeSetting D ell hne r hr).diagonalExponent_isUnit
        (Y ↘ Spec (.of D.k))) ag)
    (_hh : Etale.FiniteSmoothPurity.OrientationNormalized A (ell ^ r)
      (pow_pos (Fact.out : ell.Prime).pos r) hA (f ≫ g) (d + e) dh
      ((finiteGeneralRingPrimeSetting D ell hne r hr).diagonalExponent_isUnit
        (X ↘ Spec (.of D.k))) ah) :
    FiniteEquations A f g (ell ^ r) (pow_pos (Fact.out : ell.Prime).pos r) hA
      ((finiteGeneralRingPrimeSetting D ell hne r hr).diagonalExponent_isUnit
        (Y ↘ Spec (.of D.k))) d e af ag ah := by
  sorry

end Finite

section Towers
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (b : SpTowerShriek.Base l E) (o : SpTowerShriek.Operations l E b)
  (q : SpTowerCalculus.Coordinates l E b)
  {X Y Z V W U : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y] [IsNoetherian Z]
  (jf : X ⟶ V) [IsOpenImmersion jf] (pf : V ⟶ Y) [IsProper pf]
  (jg : Y ⟶ W) [IsOpenImmersion jg] (pg : W ⟶ Z) [IsProper pg]
  (jh : X ⟶ U) [IsOpenImmersion jh] (ph : U ⟶ Z) [IsProper ph]
  [QuasiCompact (jf ≫ pf)] [QuasiCompact (jg ≫ pg)] [QuasiCompact (jh ≫ ph)]
  [HasCompactification (jf ≫ pf)] [HasCompactification (jg ≫ pg)]
  [HasCompactification (jh ≫ ph)]
  (d e : ℕ)
  (wf : SpChartAdmissibility.Twists l E X)
  (wg : SpChartAdmissibility.Twists l E Y)
  (wh : SpChartAdmissibility.Twists l E X)
  (Pf : TowerAdjointCompositor.Pair l E b o q (SpTowerGamma.factorization jf pf))
  (Pg : TowerAdjointCompositor.Pair l E b o q (SpTowerGamma.factorization jg pg))
  (Ph : TowerAdjointCompositor.Pair l E b o q (SpTowerGamma.factorization jh ph))
  (af : SpTowerGamma.Purity l E b o q jf pf d wf Pf.closed Pf.right Pf.adj Pf.levels)
  (ag : SpTowerGamma.Purity l E b o q jg pg e wg Pg.closed Pg.right Pg.adj Pg.levels)
  (ah : SpTowerGamma.Purity l E b o q jh ph (d + e) wh
    Ph.closed Ph.right Ph.adj Ph.levels)
  (c : Ph.right ≅ Pg.right ⋙ Pf.right)

/-- The actual tower tensor mate supplied by gamma, before any level evaluation.
Source: composition-factors, t_f (blueprint: det-sp-composition-factors). -/
def towerTensorF (K : SpTowerCalculus.C l E b q Y) :=
  SpTowerGamma.tensorMate l E b o q (SpTowerGamma.factorization jf pf)
    af.tensorX af.tensorY Pf.closed Pf.right Pf.adj af.unit_mem K
      (af.tensor_mem K) (af.projection_iso K)

/-- The actual tower tensor mate for g.
Source: composition-factors, t_g (blueprint: det-sp-composition-factors). -/
def towerTensorG (K : SpTowerCalculus.C l E b q Z) :=
  SpTowerGamma.tensorMate l E b o q (SpTowerGamma.factorization jg pg)
    ag.tensorX ag.tensorY Pg.closed Pg.right Pg.adj ag.unit_mem K
      (ag.tensor_mem K) (ag.projection_iso K)

/-- The actual tower tensor mate for h.
Source: composition-factors, t_h (blueprint: det-sp-composition-factors). -/
def towerTensorH (K : SpTowerCalculus.C l E b q Z) :=
  SpTowerGamma.tensorMate l E b o q (SpTowerGamma.factorization jh ph)
    ah.tensorX ah.tensorY Ph.closed Ph.right Ph.adj ah.unit_mem K
      (ah.tensor_mem K) (ah.projection_iso K)

/-- The coefficient object omega_g as an object of the full uniform tower category.
Source: composition-factors, omega_g (blueprint: det-sp-composition-factors). -/
def towerOmegaG := Pg.right.obj ⟨SpTowerGamma.originalUnit l E b q Z, ag.unit_mem⟩

/-- Rho is the existing tower tensor mate at omega_g, not a chosen isomorphism.
Source: composition-factors, rho (blueprint: det-sp-composition-factors). -/
def towerRho := towerTensorF l E b o q jf pf d wf Pf af
  (towerOmegaG l E b o q jg pg e wg Pg ag)

/-- Mu is c at the unit followed by the inverse of that particular rho.
Source: composition-factors, mu (blueprint: det-sp-composition-factors). -/
def towerMu (hR : IsIso (towerRho l E b o q jf pf jg pg d e wf wg Pf Pg af ag)) :=
  letI := hR
  (SpTowerGamma.realization l E b q X).mapIso
      (c.app ⟨SpTowerGamma.originalUnit l E b q Z, ag.unit_mem⟩) ≪≫
    (asIso (towerRho l E b o q jf pf jg pg d e wf wg Pf Pg af ag)).symm

/-- The canonical tower pullback compositor and K-flat tensor reassociation.
Source: composition-factors, clause (2) (blueprint: det-sp-composition-factors). -/
def towerReassociate (hcomp : (jf ≫ pf) ≫ (jg ≫ pg) = jh ≫ ph)
    (K : SpTowerShriek.D l E Z) (M : SpTowerShriek.D l E Y)
    (N : SpTowerShriek.D l E X) :=
  (SpTowerShriek.tensor l E b X).mapIso
      (Iso.prod
        (((eqToIso (congrArg (fun v ↦ SpTowerShriek.pull l E b (o.geometry v))
            hcomp.symm)).app K) ≪≫ (o.comp (jf ≫ pf) (jg ≫ pg)).symm.app K)
        (Iso.refl ((SpTowerShriek.tensor l E b X).obj
          ((SpTowerShriek.pull l E b (o.geometry (jf ≫ pf))).obj M, N)))) ≪≫
    ((b.calculus X).closed.monoidal.associator _ _ _).symm ≪≫
    (SpTowerShriek.tensor l E b X).mapIso
      (Iso.prod
        (((o.geometry (jf ≫ pf)).tensorPullback).symm.app
          ((SpTowerShriek.pull l E b (o.geometry (jg ≫ pg))).obj K, M)) (Iso.refl N))

/-- Canonical finite evaluation of the shifted-Tate splitting in the tower category.
This pins the splitting by the specified root, unit, pullback and K-flat tensor words,
including rank zero; no arbitrary endpoint isomorphism is admitted.
Source: composition-factors, clause (1) (blueprint: det-sp-composition-factors). -/
def TowerSplitNormalized
    (s : SpTowerGamma.orderedLine l E b X wh (d + e) ≅
      (SpTowerShriek.tensor l E b X).obj
        ((SpTowerShriek.pull l E b (o.geometry (jf ≫ pf))).obj
          (SpTowerGamma.orderedLine l E b Y wg e),
          SpTowerGamma.orderedLine l E b X wf d)) : Prop :=
  ∀ n : ℕ,
    SpTowerP1.WordComparison l E n
      (SpTowerGamma.coefficientWord l E b X wh ah.roots n
        (ah.unitsX n) (ah.coefficientsX n) (ah.tensors n) (d + e))
      (SpTowerP1.tensorWord l E n b (af.tensors n)
        (SpTowerP1.pullWord l E n b (o.geometry (jf ≫ pf)) (af.geometry n)
          (SpTowerGamma.coefficientWord l E b Y wg ag.roots n
            (ag.unitsX n) (ag.coefficientsX n) (ag.tensors n) e))
        (SpTowerGamma.coefficientWord l E b X wf af.roots n
          (af.unitsX n) (af.coefficientsX n) (af.tensors n) d)) s.hom
      (finiteLineSplit (SpTowerP1.levelRing l E n) (jf ≫ pf) (l ^ (n + 1))
        (pow_pos (Fact.out : l.Prime).pos _) (SpTowerP1.levelAnnihilates l E n)
        (ag.unitsX n) e d).hom

/-- Both tower equations and their gamma consequence, in the actual ordinary derived
category of varying-ring systems. The input category has uniform constructibility and
Tor bounds; it imposes no derived reduction isomorphism on the input tower.
Source: composition-factors, clauses (1), (2), consequence
(blueprint: det-sp-composition-factors). -/
def TowerEquations (hcomp : (jf ≫ pf) ≫ (jg ≫ pg) = jh ≫ ph) : Prop :=
  ∃ s : SpTowerGamma.orderedLine l E b X wh (d + e) ≅
      (SpTowerShriek.tensor l E b X).obj
        ((SpTowerShriek.pull l E b (o.geometry (jf ≫ pf))).obj
          (SpTowerGamma.orderedLine l E b Y wg e),
          SpTowerGamma.orderedLine l E b X wf d),
    TowerSplitNormalized l E b o q jf pf jg pg jh ph d e wf wg wh Pf Pg Ph af ag ah s ∧
    ∃ hR : IsIso (towerRho l E b o q jf pf jg pg d e wf wg Pf Pg af ag),
      ah.orientation.hom ≫
          (towerMu l E b o q jf pf jg pg jh ph d e wf wg Pf Pg Ph af ag c hR).hom =
        s.hom ≫ (SpTowerShriek.tensor l E b X).map
          (Prod.mkHom
            ((SpTowerShriek.pull l E b (o.geometry (jf ≫ pf))).map ag.orientation.hom)
            af.orientation.hom) ∧
      ∀ K : SpTowerCalculus.C l E b q Z,
        (SpTowerShriek.tensor l E b X).map
            (Prod.mkHom (𝟙 ((SpTowerShriek.pull l E b (o.geometry (jh ≫ ph))).obj
                ((SpTowerGamma.realization l E b q Z).obj K)))
              (towerMu l E b o q jf pf jg pg jh ph d e wf wg
                Pf Pg Ph af ag c hR).inv) ≫
            towerTensorH l E b o q jh ph d e wh Ph ah K ≫
      (SpTowerGamma.realization l E b q X).map (c.hom.app K) =
          (towerReassociate l E b o jf pf jg pg jh ph hcomp
            ((SpTowerGamma.realization l E b q Z).obj K)
            ((SpTowerGamma.realization l E b q Y).obj
              (towerOmegaG l E b o q jg pg e wg Pg ag))
            ((SpTowerGamma.exceptional l E b q Pf.right).obj
              ⟨SpTowerGamma.originalUnit l E b q Y, af.unit_mem⟩)).hom ≫
          (SpTowerShriek.tensor l E b X).map
            (Prod.mkHom
              ((SpTowerShriek.pull l E b (o.geometry (jf ≫ pf))).map
                (towerTensorG l E b o q jg pg e wg Pg ag K)) (𝟙 _)) ≫
          towerTensorF l E b o q jf pf d wf Pf af (Pg.right.obj K) ∧
        SpTowerGamma.gamma l E b o q (SpTowerGamma.factorization jh ph) wh (d + e)
            ah.tensorX ah.tensorY Ph.closed Ph.right Ph.adj ah.unit_mem ah.orientation
            K (ah.tensor_mem K) (ah.projection_iso K) ≫
            (SpTowerGamma.realization l E b q X).map (c.hom.app K) =
          (SpTowerShriek.tensor l E b X).map (Prod.mkHom (𝟙 _) s.hom) ≫
          (towerReassociate l E b o jf pf jg pg jh ph hcomp
            ((SpTowerGamma.realization l E b q Z).obj K)
            (SpTowerGamma.orderedLine l E b Y wg e)
            (SpTowerGamma.orderedLine l E b X wf d)).hom ≫
          (SpTowerShriek.tensor l E b X).map
            (Prod.mkHom
              ((SpTowerShriek.pull l E b (o.geometry (jf ≫ pf))).map
                (SpTowerGamma.gamma l E b o q (SpTowerGamma.factorization jg pg) wg e
                  ag.tensorX ag.tensorY Pg.closed Pg.right Pg.adj ag.unit_mem ag.orientation
                  K (ag.tensor_mem K) (ag.projection_iso K))) (𝟙 _)) ≫
          SpTowerGamma.gamma l E b o q (SpTowerGamma.factorization jf pf) wf d
            af.tensorX af.tensorY Pf.closed Pf.right Pf.adj af.unit_mem af.orientation
            (Pg.right.obj K) (af.tensor_mem (Pg.right.obj K))
            (af.projection_iso (Pg.right.obj K))

/-- Composition of the diagonal orientations and actual tensor mates for ordinary
coefficient towers. All arrows are ordinary derived-tower arrows; neither the input nor
its morphisms are replaced by a family of levelwise arrows.
Source: composition-factors, clauses (1), (2), consequence
(blueprint: det-sp-composition-factors).

Proof:
1. The tower orientation-evaluation and projection-domain lemmas make rho invertible.
2. Apply lem-sp-composite-tensor-transpose to the actual tower adjunctions. The counit
normalization of c gives the common transpose, proving clause (2).
3. At every positive exponent apply the finite-ring orientation identity, first for
Z/ell^r by nested admissible charts and then for the quotient ring by scalar propagation.
The finite normalized gamma evaluations identify these with the evaluations of the
specified tower orientations and the canonical shifted-Tate splitting.
4. All coefficient objects are concentrated after their common even shifts. Use
lem-sp-tower-orientation-evaluation to remove those shifts and the ordinary single
fully-faithful theorem. Equality of the tower sheaf maps is componentwise equality,
so the orientation identity holds as an ordinary derived-tower morphism.
5. Substitute this equality in clause (2) and use tensor-mate naturality. This yields
the gamma consequence on every uniform constructible finite-Tor tower, without any
normalization condition. The symmetry of the two even shifts contributes +1. -/
theorem towers (D : WeilConjectures.FiniteFieldDatum.{u}) (_hl : l ≠ D.p)
    [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))] [Z.Over (Spec (.of D.k))]
    [IsSeparated (X ↘ Spec (.of D.k))] [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
    [QuasiCompact (X ↘ Spec (.of D.k))]
    [IsSeparated (Y ↘ Spec (.of D.k))] [LocallyOfFiniteType (Y ↘ Spec (.of D.k))]
    [QuasiCompact (Y ↘ Spec (.of D.k))]
    [IsSeparated (Z ↘ Spec (.of D.k))] [LocallyOfFiniteType (Z ↘ Spec (.of D.k))]
    [QuasiCompact (Z ↘ Spec (.of D.k))]
    [(jf ≫ pf).IsOver (Spec (.of D.k))] [(jg ≫ pg).IsOver (Spec (.of D.k))]
    [IsSeparated (jf ≫ pf)] [IsSeparated (jg ≫ pg)]
    [SmoothOfRelativeDimension d (jf ≫ pf)] [SmoothOfRelativeDimension e (jg ≫ pg)]
    (hcomp : (jf ≫ pf) ≫ (jg ≫ pg) = jh ≫ ph)
    (z : SpTowerCalculus.FiniteCoordinates l E)
    (pres : SpTowerCalculus.Preservation l E D.k b o q)
    (cal : SpTowerCalculus.Calculus l E D.k b o q z pres)
    (alpha : TowerAdjointCompositor.left l E b o q Pf ⋙
      TowerAdjointCompositor.left l E b o q Pg ≅ TowerAdjointCompositor.left l E b o q Ph)
    (_ha : ∀ M, (alpha.hom.app M).hom =
      (cal.composition.composition (jf ≫ pf) (jg ≫ pg) (jh ≫ ph) hcomp
        (SpTowerGamma.factorization jf pf) (SpTowerGamma.factorization jg pg)
        (SpTowerGamma.factorization jh ph)).hom.app M)
    (_hc : ∀ K,
      (TowerAdjointCompositor.left l E b o q Pf ⋙
        TowerAdjointCompositor.left l E b o q Pg).map (c.hom.app K) ≫
          (Pf.adj.comp Pg.adj).counit.app K =
        alpha.hom.app (Ph.right.obj K) ≫ Ph.adj.counit.app K) :
    TowerEquations l E b o q jf pf jg pg jh ph d e wf wg wh Pf Pg Ph af ag ah c hcomp := by
  sorry

end Towers
end SpCompositionFactors
end AlgebraicGeometry.ProEtale

