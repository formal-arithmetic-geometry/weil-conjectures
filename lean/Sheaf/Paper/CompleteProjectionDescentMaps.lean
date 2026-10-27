/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q115
-/
module

public import Sheaf.Paper.ProjectionReductionPresentation

/-! # Descent of the actual compact-support projection mate

Source: current Weil blueprint, sec-smooth-purity,
`sk-prop-sp-integral-adjunction-direct-image.proof.md`, paragraphs (2)--(3)
(blueprint: def-sp-complete-projection-descent-maps).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genCtorIdx false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open WeilConjectures WeilConjectures.SemilinearSections
open WeilConjectures.IntegralSystemRealization

namespace AlgebraicGeometry.ProEtale.CompleteProjectionDescent

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

attribute [local irreducible] HasDerivedCategory.standard constantSheaf
  Functor.mapDerivedCategory SheafOfModules.changeOfRings SheafOfModules.monoidalCategory
  reductionEpsilon reductionGenerator ordinaryReduction
  derivedTowerEquivalence towerEquivalence reduction totalLimit

/-- Ordinary geometric pullback over the specified completed coefficient sheaves.
Source: blueprint paragraph (3) (blueprint: def-sp-complete-projection-descent-maps). -/
abbrev ordinaryPull {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  Scheme.proEtaleRingModulePullback f ((PurCompactSupport.completed l E).ring Y)
    ((PurCompactSupport.completed l E).ring X) ((PurCompactSupport.completed l E).pull f)

/-- Exact geometric pullback is additive in the recorded ordinary presentation.
Source: Stacks 03D7 (blueprint: def-sp-complete-projection-descent-maps). -/
instance ordinaryPullAdditive {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (ordinaryPull l E f).Additive :=
  inferInstanceAs (Scheme.proEtaleRingModulePullback f
    ((PurCompactSupport.completed l E).ring Y)
    ((PurCompactSupport.completed l E).ring X) ((PurCompactSupport.completed l E).pull f)).Additive

/-- The normalized whole-system pullback/scalar comparison, on every complex.
Its ordinary formula identifies the two actual quotient-augmentation unit sections.
Source: blueprint paragraph (3), pullback commutes with scalar extension
(blueprint: def-sp-complete-projection-descent-maps). -/
def PullReductionModel {X Y : Scheme.{u}} (f : X ⟶ Y)
    (DX : SpCoefficientTowersAbelian l E X) (DY : SpCoefficientTowersAbelian l E Y)
    (RX : SpReductionTower l E X DX) (RY : SpReductionTower l E Y DY)
    (nu : ringedPull l E f ⋙ reduction l E X DX RX ≅
      reduction l E Y DY RY ⋙ VaryingRing.G (rings l E) (transitions l E) f) : Prop :=
  ∃ ordinary : ordinaryPull l E f ⋙ ordinaryReduction l E X DX RX ≅
    ordinaryReduction l E Y DY RY ⋙ VaryingRing.pull (rings l E) (transitions l E) f,
    (∀ (M : scalarReductionSource l E Y) (U : Y.ProEt)
    (x : M.val.obj (op U)) (n : ℕ),
    ((ordinary.hom.app M).val.app
      (op (n, (Scheme.proEtaleBaseChange f).obj U)))
      (reductionGenerator l E X DX RX ((ordinaryPull l E f).obj M) n
        (op ((Scheme.proEtaleBaseChange f).obj U))
        (((Scheme.proEtaleRingModuleAdjunction f
          ((PurCompactSupport.completed l E).ring Y)
          ((PurCompactSupport.completed l E).ring X)
          ((PurCompactSupport.completed l E).pull f)).unit.app M).val.app (op U) x)) =
      (((VaryingRing.moduleAdj (rings l E) (transitions l E) f).unit.app
        ((ordinaryReduction l E Y DY RY).obj M)).val.app (op (n, U)))
        (reductionGenerator l E Y DY RY M n (op U) x)) ∧
    ∀ P : CochainComplex (scalarReductionSource l E Y) ℤ,
    (reduction l E X DX RX).map
      ((ordinaryPull l E f).mapDerivedCategoryFactors.hom.app P) ≫
      reductionEpsilon l E X DX RX
        (((ordinaryPull l E f).mapHomologicalComplex (.up ℤ)).obj P) ≫
      DerivedCategory.Q.map ((letI : (ordinaryPull l E f).Additive := ordinaryPullAdditive l E f
        letI : (ordinaryReduction l E X DX RX).Additive :=
          ordinaryReductionAdditive l E X DX RX
        letI : (ordinaryReduction l E Y DY RY).Additive :=
          ordinaryReductionAdditive l E Y DY RY
        NatIso.mapHomologicalComplex ordinary (.up ℤ)).hom.app P) =
    nu.hom.app (DerivedCategory.Q.obj P) ≫
      (VaryingRing.G (rings l E) (transitions l E) f).map
        (reductionEpsilon l E Y DY RY P) ≫
      (VaryingRing.pull (rings l E) (transitions l E) f).mapDerivedCategoryFactors.hom.app
        (((ordinaryReduction l E Y DY RY).mapHomologicalComplex (.up ℤ)).obj P)

/-- Canonical tensor pullback on the ringed sequence site, fixed by its ordinary
unit sections and its total-complex representative square.
Source: Stacks 03EL, 07A4; blueprint paragraph (3)
(blueprint: def-sp-complete-projection-descent-maps). -/
structure SystemTensorPull {X Y : Scheme.{u}} (f : X ⟶ Y)
    (SX : Calculus l E X) (SY : Calculus l E Y) where
  iso : SY.closed.tensor ⋙ VaryingRing.G (rings l E) (transitions l E) f ≅
    ((VaryingRing.G (rings l E) (transitions l E) f).prod
      (VaryingRing.G (rings l E) (transitions l E) f)) ⋙ SX.closed.tensor
  model : TensorComparisonModel.{u + 1, u, u + 1} _ _ _ _
    (VaryingRing.pull (rings l E) (transitions l E) f)
    SY.closed SX.closed SY.tensorModels SX.tensorModels iso
  pure : ∀ (M N : VaryingRing.Modules (rings l E) (transitions l E) Y)
    (U : (ℕ × Y.ProEt)) (x : M.val.obj (op U)) (y : N.val.obj (op U)),
    ((model.ordinary M N).hom.val.app
      (op ((VaryingRing.baseChange f).obj U)))
      (((VaryingRing.moduleAdj (rings l E) (transitions l E) f).unit.app
        (ordinaryTensor.{u + 1, u, u + 1} _ _ M N)).val.app (op U)
          (tensorSection.{u + 1, u, u + 1} _ _ M N (op U) x y)) =
      tensorSection.{u + 1, u, u + 1} _ _ _ _ (op ((VaryingRing.baseChange f).obj U))
        (((VaryingRing.moduleAdj (rings l E) (transitions l E) f).unit.app M).val.app (op U) x)
        (((VaryingRing.moduleAdj (rings l E) (transitions l E) f).unit.app N).val.app (op U) y)

/-- A simultaneous presentation of the already specified canonical comparisons.
All maps are fixed on whole quotient complexes, rather than by levelwise choices.
Source: blueprint paragraphs (2)--(3)
(blueprint: def-sp-complete-projection-descent-maps). -/
structure DescentModels where
  abelian : ∀ T : Scheme.{u}, SpCoefficientTowersAbelian l E T
  red : ∀ T : Scheme.{u}, SpReductionTower l E T (abelian T)
  integral : RingedModels l E
  openIntegral : RingedOpenComparisons l E integral
  systems : ∀ T : Scheme.{u}, Calculus l E T
  tensor : ∀ T : Scheme.{u},
    (integral.tensor T).ordinary.tensor ⋙ reduction l E T (abelian T) (red T) ≅
      ((reduction l E T (abelian T) (red T)).prod
        (reduction l E T (abelian T) (red T))) ⋙ (systems T).closed.tensor
  tensor_model : ∀ T : Scheme.{u},
    TensorReductionModel l E T (abelian T) (red T) integral (systems T) (tensor T)
  pull : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y),
    ringedPull l E f ⋙ reduction l E X (abelian X) (red X) ≅
      reduction l E Y (abelian Y) (red Y) ⋙ VaryingRing.G (rings l E) (transitions l E) f
  pull_model : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y),
    PullReductionModel l E f (abelian X) (abelian Y) (red X) (red Y) (pull f)
  systemPull : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y),
    SystemTensorPull l E f (systems X) (systems Y)

  openScalar : ∀ {X Z : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j],
    ringedOpen l E j ⋙ reduction l E Z (abelian Z) (red Z) ≅
      reduction l E X (abelian X) (red X) ⋙ VaryingRing.J (rings l E) (transitions l E) j
  openScalar_normalized : ∀ {X Z : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j],
    (openScalar j).inv =
      ((mateEquiv (ringedOpenAdj l E j)
        (VaryingRing.jAdj (rings l E) (transitions l E) j)).symm
        (TwoSquare.mk _ _ _ _ (pull j).hom)).natTrans

variable (m : DescentModels l E)

/-- The stipulated reduction of ordinary unbounded integral modules.
Source: blueprint paragraph (3) (blueprint: def-sp-complete-projection-descent-maps). -/
abbrev red (T : Scheme.{u}) := reduction l E T (m.abelian T) (m.red T)

/-- The stipulated total derived inverse limit, retaining every quotient transition.
Source: blueprint paragraph (3) (blueprint: def-sp-complete-projection-descent-maps). -/
abbrev lim (T : Scheme.{u})
    (A : SpNormalizedEquivalence l E T (m.abelian T) (m.red T)) :=
  totalLimit l E T (m.abelian T) (m.red T) A

/-- The actual normalized reduction/limit adjunction.
Source: blueprint paragraphs (2)--(3)
(blueprint: def-sp-complete-projection-descent-maps). -/
abbrev adj (T : Scheme.{u})
    (A : SpNormalizedEquivalence l E T (m.abelian T) (m.red T)) :=
  reductionAdjunction l E T (m.abelian T) (m.red T) A

/-- Proper scalar exchange is the mate of the canonical pullback/scalar square.
Source: blueprint paragraph (3) (blueprint: def-sp-complete-projection-descent-maps). -/
def properScalar {Z Y : Scheme.{u}} (p : Z ⟶ Y) :
    ringedPush l E p ⋙ red l E m Y ⟶
      red l E m Z ⋙ VaryingRing.P (rings l E) (transitions l E) p :=
  (mateEquiv (ringedAdj l E p) (VaryingRing.adj (rings l E) (transitions l E) p)
    (TwoSquare.mk _ _ _ _ (m.pull p).inv)).natTrans

/-- The open/limit comparison, defined by its actual adjunction transpose.
Source: blueprint paragraph (2) (blueprint: def-sp-complete-projection-descent-maps). -/
def openLimit {X Z : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j]
    (AX : SpNormalizedEquivalence l E X (m.abelian X) (m.red X))
    (AZ : SpNormalizedEquivalence l E Z (m.abelian Z) (m.red Z))
    (B : System l E X) :
    (ringedOpen l E j).obj ((lim l E m X AX).obj B) ⟶
      (lim l E m Z AZ).obj ((VaryingRing.J (rings l E) (transitions l E) j).obj B) :=
  (adj l E m Z AZ).homEquiv _ _
    ((m.openScalar j).hom.app ((lim l E m X AX).obj B) ≫
      (VaryingRing.J (rings l E) (transitions l E) j).map ((adj l E m X AX).counit.app B))

/-- The proper/limit comparison, with the same proper counit mate.
Source: blueprint paragraph (2) (blueprint: def-sp-complete-projection-descent-maps). -/
def properLimit {Z Y : Scheme.{u}} (p : Z ⟶ Y)
    (AZ : SpNormalizedEquivalence l E Z (m.abelian Z) (m.red Z))
    (AY : SpNormalizedEquivalence l E Y (m.abelian Y) (m.red Y)) (B : System l E Z) :
    (ringedPush l E p).obj ((lim l E m Z AZ).obj B) ⟶
      (lim l E m Y AY).obj ((VaryingRing.P (rings l E) (transitions l E) p).obj B) :=
  (adj l E m Y AY).homEquiv _ _
    ((properScalar l E m p).app ((lim l E m Z AZ).obj B) ≫
      (VaryingRing.P (rings l E) (transitions l E) p).map ((adj l E m Z AZ).counit.app B))

/-- Integral compact support in the given compactification, without completion.
Source: blueprint paragraph (2) (blueprint: def-sp-complete-projection-descent-maps). -/
abbrev integralImage {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) :=
  ringedOpen l E c.i ⋙ ringedPush l E c.g

/-- The simultaneous compact-support operation on the ell-power sequence site.
Source: blueprint paragraph (3) (blueprint: def-sp-complete-projection-descent-maps). -/
abbrev systemImage {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) :=
  VaryingRing.J (rings l E) (transitions l E) c.i ⋙
    VaryingRing.P (rings l E) (transitions l E) c.g

/-- The canonical compactification/limit map: compact support of the actual
unit, then the open/limit map, then the proper/limit map.
Source: blueprint paragraph (2) (blueprint: def-sp-complete-projection-descent-maps). -/
def compactificationLimit {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (AX : SpNormalizedEquivalence l E X (m.abelian X) (m.red X))
    (AZ : SpNormalizedEquivalence l E c.Z (m.abelian c.Z) (m.red c.Z))
    (AY : SpNormalizedEquivalence l E Y (m.abelian Y) (m.red Y))
    (N : Integral l E X) :
    (integralImage l E c).obj N ⟶
      (lim l E m Y AY).obj ((systemImage l E c).obj ((red l E m X).obj N)) :=
  (integralImage l E c).map ((adj l E m X AX).unit.app N) ≫
    (ringedPush l E c.g).map (openLimit l E m c.i AX AZ ((red l E m X).obj N)) ≫
    properLimit l E m c.g AZ AY
      ((VaryingRing.J (rings l E) (transitions l E) c.i).obj ((red l E m X).obj N))

/-- The specified reconstruction counit; it is the transpose of the normalized
compactification/limit comparison, rather than a separately chosen isomorphism.
Source: blueprint paragraphs (2)--(3)
(blueprint: def-sp-complete-projection-descent-maps). -/
def reconstruction {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (AX : SpNormalizedEquivalence l E X (m.abelian X) (m.red X))
    (AZ : SpNormalizedEquivalence l E c.Z (m.abelian c.Z) (m.red c.Z))
    (AY : SpNormalizedEquivalence l E Y (m.abelian Y) (m.red Y))
    (N : Integral l E X) :
    (red l E m Y).obj ((integralImage l E c).obj N) ⟶
      (systemImage l E c).obj ((red l E m X).obj N) :=
  (red l E m Y).map (compactificationLimit l E m c AX AZ AY N) ≫
    (adj l E m Y AY).counit.app ((systemImage l E c).obj ((red l E m X).obj N))

/-- The ordinary derived input tensor, using the actual geometric pullback.
Source: blueprint paragraph (3) (blueprint: def-sp-complete-projection-descent-maps). -/
abbrev inputTensor {X Y : Scheme.{u}} (f : X ⟶ Y) (M : Integral l E X)
    (K : Integral l E Y) :=
  (m.integral.tensor X).ordinary.tensor.obj (M, (ringedPull l E f).obj K)

/-- The actual proper counit projection mate on whole derived coefficient systems.
Source: blueprint paragraph (3) (blueprint: def-sp-complete-projection-descent-maps). -/
def systemProperProjection {Z Y : Scheme.{u}} (p : Z ⟶ Y) :
    VaryingRing.P (rings l E) (transitions l E) p ⋙
        Functor.curryObj (m.systems Y).closed.tensor ⟶
      (Functor.postcompose₂.obj (VaryingRing.P (rings l E) (transitions l E) p)).obj
        ((((Functor.whiskeringLeft₂ _).obj (𝟭 _)).obj
          (VaryingRing.G (rings l E) (transitions l E) p)).obj
            (Functor.curryObj (m.systems Z).closed.tensor)) :=
  (VaryingRing.adj (rings l E) (transitions l E) p).rightAdjointProjectionMap
    (Functor.curry.mapIso (m.systemPull p).iso ≪≫
      Functor.curryObjProdComp
        (VaryingRing.G (rings l E) (transitions l E) p)
        (VaryingRing.G (rings l E) (transitions l E) p) (m.systems Z).closed.tensor).hom

/-- The inverse open projection: precisely the adjunct of unit tensor identity.
Source: blueprint paragraph (3) (blueprint: def-sp-complete-projection-descent-maps). -/
def systemOpenInverse {X Z : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j]
    (B : System l E X) (C : System l E Z) :
    (VaryingRing.J (rings l E) (transitions l E) j).obj
        ((m.systems X).closed.tensor.obj
          (B, (VaryingRing.G (rings l E) (transitions l E) j).obj C)) ⟶
      (m.systems Z).closed.tensor.obj
        ((VaryingRing.J (rings l E) (transitions l E) j).obj B, C) :=
  ((VaryingRing.jAdj (rings l E) (transitions l E) j).homEquiv _ _).symm
    ((m.systems X).closed.tensor.map
      (Prod.mkHom ((VaryingRing.jAdj (rings l E) (transitions l E) j).unit.app B) (𝟙 _)) ≫
        (m.systemPull j).iso.inv.app
          ((VaryingRing.J (rings l E) (transitions l E) j).obj B, C))

/-- The system compact-support projection in the specified proper/open order.
Source: blueprint paragraph (3) (blueprint: def-sp-complete-projection-descent-maps). -/
def systemProjection {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (B : System l E X) (C : System l E Y)
    (hOpen : IsIso (systemOpenInverse l E m c.i B
      ((VaryingRing.G (rings l E) (transitions l E) c.g).obj C))) :
    (m.systems Y).closed.tensor.obj ((systemImage l E c).obj B, C) ⟶
      (systemImage l E c).obj ((m.systems X).closed.tensor.obj
        (B, (VaryingRing.G (rings l E) (transitions l E) f).obj C)) :=
  (((systemProperProjection l E m c.g).app
    ((VaryingRing.J (rings l E) (transitions l E) c.i).obj B)).app C) ≫
    (VaryingRing.P (rings l E) (transitions l E) c.g).map
      ((@asIso _ _ _ _ (systemOpenInverse l E m c.i B
        ((VaryingRing.G (rings l E) (transitions l E) c.g).obj C)) hOpen).inv ≫
        (VaryingRing.J (rings l E) (transitions l E) c.i).map
          ((m.systems X).closed.tensor.map (Prod.mkHom (𝟙 B)
            ((VaryingRing.gComp (rings l E) (transitions l E) c.i c.g).inv.app C ≫
              eqToHom (congrArg (fun g : X ⟶ Y ↦
                (VaryingRing.G (rings l E) (transitions l E) g).obj C) c.comm.symm)))))

/-- The source identification uses the actual reconstruction counit and tensor/scalar map.
Source: blueprint paragraph (3) (blueprint: def-sp-complete-projection-descent-maps). -/
def sourceComparison {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (AX : SpNormalizedEquivalence l E X (m.abelian X) (m.red X))
    (AZ : SpNormalizedEquivalence l E c.Z (m.abelian c.Z) (m.red c.Z))
    (AY : SpNormalizedEquivalence l E Y (m.abelian Y) (m.red Y))
    (M : Integral l E X) (K : Integral l E Y)
    (hb : IsIso (reconstruction l E m c AX AZ AY M)) :
    (red l E m Y).obj ((m.integral.tensor Y).ordinary.tensor.obj
      ((integralImage l E c).obj M, K)) ≅
    (m.systems Y).closed.tensor.obj
      ((systemImage l E c).obj ((red l E m X).obj M), (red l E m Y).obj K) :=
  (m.tensor Y).app ((integralImage l E c).obj M, K) ≪≫
    (m.systems Y).closed.tensor.mapIso
      (Iso.prod (@asIso _ _ _ _ (reconstruction l E m c AX AZ AY M) hb) (Iso.refl _))

/-- The target identification uses reconstruction, tensor/scalar and pullback/scalar,
in that order, on whole derived systems.
Source: blueprint paragraph (3) (blueprint: def-sp-complete-projection-descent-maps). -/
def targetComparison {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (AX : SpNormalizedEquivalence l E X (m.abelian X) (m.red X))
    (AZ : SpNormalizedEquivalence l E c.Z (m.abelian c.Z) (m.red c.Z))
    (AY : SpNormalizedEquivalence l E Y (m.abelian Y) (m.red Y))
    (M : Integral l E X) (K : Integral l E Y)
    (hb : IsIso (reconstruction l E m c AX AZ AY (inputTensor l E m f M K))) :
    (red l E m Y).obj ((integralImage l E c).obj (inputTensor l E m f M K)) ≅
      (systemImage l E c).obj ((m.systems X).closed.tensor.obj
        ((red l E m X).obj M,
          (VaryingRing.G (rings l E) (transitions l E) f).obj ((red l E m Y).obj K))) :=
  (@asIso _ _ _ _ (reconstruction l E m c AX AZ AY (inputTensor l E m f M K)) hb) ≪≫
    (systemImage l E c).mapIso ((m.tensor X).app (M, (ringedPull l E f).obj K) ≪≫
      (m.systems X).closed.tensor.mapIso (Iso.prod (Iso.refl _) ((m.pull f).app K)))

/-- The transported system projection, with the stipulated reconstruction coordinates.
Source: blueprint paragraph (3) (blueprint: def-sp-complete-projection-descent-maps). -/
def transportedProjection {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (AX : SpNormalizedEquivalence l E X (m.abelian X) (m.red X))
    (AZ : SpNormalizedEquivalence l E c.Z (m.abelian c.Z) (m.red c.Z))
    (AY : SpNormalizedEquivalence l E Y (m.abelian Y) (m.red Y))
    (M : Integral l E X) (K : Integral l E Y)
    (hbM : IsIso (reconstruction l E m c AX AZ AY M))
    (hbH : IsIso (reconstruction l E m c AX AZ AY (inputTensor l E m f M K)))
    (hOpen : IsIso (systemOpenInverse l E m c.i ((red l E m X).obj M)
      ((VaryingRing.G (rings l E) (transitions l E) c.g).obj ((red l E m Y).obj K)))) :=
  (sourceComparison l E m c AX AZ AY M K hbM).hom ≫
    systemProjection l E m c ((red l E m X).obj M) ((red l E m Y).obj K) hOpen ≫
      (targetComparison l E m c AX AZ AY M K hbH).inv


end AlgebraicGeometry.ProEtale.CompleteProjectionDescent
