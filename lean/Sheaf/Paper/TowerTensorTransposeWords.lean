/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q11
-/
module

public import Sheaf.Paper.SmoothPurityTowerGammaData
public import Sheaf.Paper.SmoothPurityMap
public import Sheaf.Paper.FiniteSmoothPurityMaps
public import Sheaf.Paper.ExchangeProjectionSuppliedDomains
public import Sheaf.Paper.DerivedPullbackTensorHom
public import Sheaf.Paper.TowerP1CoefficientCoordinates
public import Sheaf.Paper.TowerP1GeometricCoordinates
public import Sheaf.Paper.CohomologicalSmoothnessFiniteComparison
public import Sheaf.Paper.IntrinsicCoefficientTwistsUnrestricted

/-! # Finite evaluation of the tower tensor transpose

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/
sk-prop-sp-tower-geometric/sk-prop-sp-tower-geometric-gamma.proof.md, (2).
(blueprint: def-sp-tensor-transpose-evaluation-words).

The maps are the published actual ordinary-tower composites in SpTowerGamma.
These definitions are imported and reused from SmoothPurityTowerGamma.
A natural index n always denotes the positive coefficient exponent n+1. Level words
retain the normalized site, scalar, tensor and adjunction comparisons.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option genInjectivity false
set_option genSizeOfSpec false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry.Scheme WeilConjectures

namespace AlgebraicGeometry.ProEtale.SpTensorTranspose

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (b : SpTowerShriek.Base l E) (o : SpTowerShriek.Operations l E b)
  (q : SpTowerCalculus.Coordinates l E b)
  {X Z Y : Scheme.{u}}
  (j : X ⟶ Z) [IsOpenImmersion j] (p : Z ⟶ Y) [IsProper p]
  [QuasiCompact (j ≫ p)] [HasCompactification (j ≫ p)]
  (hF : ∀ M : SpTowerCalculus.C l E b q X,
    spConstructibleTorTowers l E Y (q.abelian Y)
      ((SpTowerCalculus.F l E b o q (SpTowerGamma.factorization j p)).obj M.obj))
  (G : SpTowerCalculus.C l E b q Y ⥤ SpTowerCalculus.C l E b q X)
  (adj : SpTowerGluing.support l E b o q (SpTowerGamma.factorization j p) hF ⊣ G)
  (lv : SpTowerGluing.Levels l E b o q (SpTowerGamma.factorization j p) hF G adj)
  (hU : spConstructibleTorTowers l E Y (q.abelian Y)
    (SpTowerGamma.originalUnit l E b q Y))
  (tx : SpTowerP1.TensorData l E b X) (ty : SpTowerP1.TensorData l E b Y)
/-- The tensor source as an object of the original full tower category.
Source: tower-geometric gamma proof (2)
(blueprint: def-sp-tensor-transpose-evaluation-words). -/
def originalSource (K : SpTowerCalculus.C l E b q Y)
    (hQ : spConstructibleTorTowers l E X (q.abelian X)
      ((SpTowerCalculus.realization l E b X (q.abelian X)).inverse.obj
        ((SpTowerGamma.tensorSource l E b o q (j ≫ p) ((SpTowerGamma.exceptional l E b q G).obj
          ⟨SpTowerGamma.originalUnit l E b q Y, hU⟩)).obj K))) : SpTowerCalculus.C l E b q X :=
  ⟨_, hQ⟩

/-- The actual projection/counit map in the full tower category, before evaluation.
Source: tower-geometric gamma proof (2)
(blueprint: def-sp-tensor-transpose-evaluation-words). -/
def originalComposite (K : SpTowerCalculus.C l E b q Y)
    (hQ : spConstructibleTorTowers l E X (q.abelian X)
      ((SpTowerCalculus.realization l E b X (q.abelian X)).inverse.obj
        ((SpTowerGamma.tensorSource l E b o q (j ≫ p) ((SpTowerGamma.exceptional l E b q G).obj
          ⟨SpTowerGamma.originalUnit l E b q Y, hU⟩)).obj K)))
    (hpf : IsIso (SpTowerShriek.projection l E b o (SpTowerGamma.factorization j p)
      ((SpTowerGamma.exceptional l E b q G).obj ⟨SpTowerGamma.originalUnit l E b q Y, hU⟩)
        ((SpTowerGamma.realization l E b q Y).obj K))) :
    (SpTowerGluing.support l E b o q (SpTowerGamma.factorization j p) hF).obj
      (originalSource l E b o q j p G hU K hQ) ⟶ K :=
  ObjectProperty.homMk
    ((SpTowerCalculus.realization l E b Y (q.abelian Y)).functor.preimage
      ((SpCoordinateAdjunction.supportRealization l E b o q (SpTowerGamma.factorization j
        p)).hom.app _ ≫
        (SpTowerShriek.F l E b o (SpTowerGamma.factorization j p)).map
          ((SpTowerCalculus.realization l E b X (q.abelian X)).counitIso.hom.app _) ≫
        SpTowerGamma.projectionCounit l E b o q (SpTowerGamma.factorization j p) tx ty hF G adj hU K
          hpf))

variable (n : ℕ) [Finite (SpTowerShriek.R l E n)]
  (ui : (SpTowerGamma.inputWord l E b o q (SpTowerGamma.factorization j p) hF G adj lv n
    ⟨SpTowerGamma.originalUnit l E b q Y, hU⟩).etale ≅
    Etale.ordinaryFiniteUnit (SpTowerP1.levelRing l E n) Y)
/-- The finite dualizing object with its counit-normalized evaluation comparison.
Source: tower-geometric gamma proof (2)
(blueprint: def-sp-tensor-transpose-evaluation-words). -/
def dualizingWord : SpTowerP1.LevelWord l E n X where
  tower := (SpTowerGamma.exceptional l E b q G).obj ⟨SpTowerGamma.originalUnit l E b q Y, hU⟩
  etale := Etale.dualizingComplex (ModuleCat.{u + 1} (SpTowerP1.levelRing l E n)) (j ≫ p)
  comparison := (SpTowerP1.nu l E n X).map
      ((Etale.rightDerivedUpperShriek
        (ModuleCat.{u + 1} (SpTowerP1.levelRing l E n)) (j ≫ p)).map
          (PurityFiniteSetting.smoothPurityUnitIso (SpTowerP1.levelRing l E n) Y).inv ≫
        (SpTowerGamma.finiteRightComparison (SpTowerShriek.R l E n) j p
    (lv.finite_closed n) (lv.right n) (lv.adjunction n) (lv.realization n)).inv.app _ ≫
        (lv.realization n).right.map ui.inv) ≫
    (SpTowerGamma.targetWord l E b o q (SpTowerGamma.factorization j p) hF G adj lv n
      ⟨SpTowerGamma.originalUnit l E b q Y, hU⟩).comparison

variable (tc : SpTowerP1.TensorCoordinates l E n b X)
  (gc : SpTowerP1.GeometricCoordinates l E n (j ≫ p))
/-- The finite tensor source, with the specified K-flat and pullback comparisons.
Source: tower-geometric gamma proof (2)
(blueprint: def-sp-tensor-transpose-evaluation-words). -/
def tensorWord (K : SpTowerCalculus.C l E b q Y) : SpTowerP1.LevelWord l E n X :=
  SpTowerP1.tensorWord l E n b tc
    (SpTowerP1.pullWord l E n b (o.geometry (j ≫ p)) gc
      (SpTowerGamma.inputWord l E b o q (SpTowerGamma.factorization j p) hF G adj lv n K))
    (dualizingWord l E b o q j p hF G adj lv hU n ui)

/-- The specified finite tensor map, transported by the unique right-adjoint comparison.
It is the finite canonical gamma of def-pur-finite-smooth-canonical-maps at the identity
orientation of the dualizing complex: the adjoint transpose of symmetry, inverse
projection, symmetry, identity tensor the counit and the right unitor, which is the
tensor map of def-pur-co-smoothness (2) up to symmetry naturality.
Source: tower-geometric gamma proof (2)
(blueprint: def-sp-tensor-transpose-evaluation-words). -/
def finiteTheta (K : SpTowerCalculus.C l E b q Y) :=
  Etale.FiniteSmoothPurity.gamma (SpTowerP1.levelRing l E n) (j ≫ p)
    (Etale.dualizingComplex (ModuleCat.{u + 1} (SpTowerP1.levelRing l E n)) (j ≫ p))
    (Iso.refl _)
      (SpTowerGamma.inputWord l E b o q (SpTowerGamma.factorization j p) hF G adj lv n K).etale ≫
    (SpTowerGamma.finiteRightComparison (SpTowerShriek.R l E n) j p
    (lv.finite_closed n) (lv.right n) (lv.adjunction n) (lv.realization n)).inv.app _

/-- The same specified finite theta in the intrinsic full finite coefficient category.
Source: tower-geometric gamma proof (2)
(blueprint: def-sp-tensor-transpose-evaluation-words). -/
def intrinsicTheta (K : SpTowerCalculus.C l E b q Y)
    (hQ : spConstructibleTorTowers l E X (q.abelian X)
      ((SpTowerCalculus.realization l E b X (q.abelian X)).inverse.obj
        ((SpTowerGamma.tensorSource l E b o q (j ≫ p) ((SpTowerGamma.exceptional l E b q G).obj
          ⟨SpTowerGamma.originalUnit l E b q Y, hU⟩)).obj K)))
    (hi : IsIso (tensorWord l E b o q j p hF G adj lv hU n ui tc gc K).comparison) :
    (SpTowerGluing.level l E b q X n).obj
        (originalSource l E b o q j p G hU K hQ) ⟶
      (lv.right n).obj ((SpTowerGluing.level l E b q Y n).obj K) :=
  ObjectProperty.homMk
    ((SpTowerCalculus.levelComparison l E b q X n).inv.app _ ≫
      (SpTowerShriek.Ev l E X n).map
        ((SpTowerCalculus.realization l E b X (q.abelian X)).counitIso.hom.app _) ≫
      @inv _ _ _ _
        (tensorWord l E b o q j p hF G adj lv hU n ui tc gc K).comparison hi ≫
      (SpTowerP1.nu l E n X).map (finiteTheta l E b o q j p hF G adj lv n K) ≫
      (SpTowerGamma.targetWord l E b o q (SpTowerGamma.factorization j p) hF G adj lv n
        K).comparison ≫
      (SpTowerCalculus.levelComparison l E b q X n).hom.app (G.obj K).obj ≫
      ((lv.comparison n).hom.app K).hom)


end AlgebraicGeometry.ProEtale.SpTensorTranspose

attribute [instance high] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
