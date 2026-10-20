/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NG
-/
module

public import Sheaf.Paper.SmoothPurityTowerClasses
public import Sheaf.Paper.SmoothPurityNormalizedTowers
public import Sheaf.Paper.SmoothPurityTowerBound
import Sheaf.CategoryTheory.RingedSitePerfectDuality
public import Sheaf.AlgebraicGeometry.ProEtalePullbackStalkCoherence

import Sheaf.Paper.SmoothPurityTowerLevels
import Sheaf.AlgebraicGeometry.FixedComparisonDirectImageMate
import Sheaf.AlgebraicGeometry.SupportComparisonPullbackCoherence
import Sheaf.AlgebraicGeometry.EtaleFiniteTwistPullback
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.ClosedImmersion
import Sheaf.Paper.SmoothPurityCoefficientTowersAbelian
import Sheaf.Paper.SemilinearDerivedSections
import Sheaf.AlgebraicGeometry.ProperTorsionProjectionFormula
import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
import Sheaf.AlgebraicGeometry.ArbitraryBaseP1Integrals
import Sheaf.AlgebraicGeometry.ProperUnboundedBaseChange
import Sheaf.Paper.SmoothPurityTowerShriekLevels
import Sheaf.Paper.RingedExchangeTensorCoherence
import Sheaf.Paper.SmoothPurityCoefficientTowers
import Sheaf.AlgebraicGeometry.BoundedBelowProEtaleComparison
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
import Sheaf.AlgebraicGeometry.ConstructibleProEtaleComparison
import Sheaf.AlgebraicGeometry.ClassicalDerivedEquivalence
import Sheaf.AlgebraicGeometry.ComparisonTorInterval
import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.FlatModel
import Sheaf.Paper.KFlatRingedToposPullback
import Sheaf.AlgebraicGeometry.FiniteEtaleTwistLine

/-! # The projective-line adjunction on ordinary coefficient towers

Source: blueprint main-20261015, sec-smooth-purity,
`sk-prop-sp-tower-geometric-p1.md` (blueprint: det-sp-tower-p1-adjunction).
The domain is bounded below with etale-origin levels. No normalization is imposed.
All natural-number indices denote the positive exponent n+1.
-/

@[expose] public noncomputable section
set_option Elab.async false
set_option autoImplicit false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme WeilConjectures

namespace AlgebraicGeometry.ProEtale.SpTowerP1

open SpTowerClasses
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- The full bounded-below etale-origin domain in the ordinary system localization.
Source: the opening paragraph (blueprint: det-sp-tower-p1-adjunction). -/
def domain (b : SpTowerShriek.Base l E) (T : Scheme.{u}) :
    ObjectProperty (SpTowerShriek.D l E T) :=
  fun K ↦ (∃ a : ℤ, DerivedCategory.IsGE K a) ∧
    ∀ n : ℕ, Nonempty (SpTowerShriek.Origin l E b T n K)

/-- The actual full subcategory, retaining all ambient derived morphisms.
Source: the opening paragraph (blueprint: det-sp-tower-p1-adjunction). -/
abbrev C (b : SpTowerShriek.Base l E) (T : Scheme.{u}) := (domain l E b T).FullSubcategory

/-- Unit and signed symmetry of the existing tensor, with its representative normalization.
The model's closed structure is required to be the already recorded system tensor.
Source: the projection identifications (blueprint: det-sp-tower-p1-adjunction). -/
structure TensorData (b : SpTowerShriek.Base l E) (T : Scheme.{u}) where
  model : RingedSiteDualityModel.{u + 1, u, u + 1, u + 2}
    (coefficientSequenceTopology (ProEt.topology T)) (systemRing l E T)
  closed_eq : model.closed = (b.calculus T).closed
  unitIso : (b.calculus T).closed.monoidal.tensorUnit ≅ unit T (Arings l E T)
  unit_normalization : HEq unitIso model.unitIso

/-- Transport only the structure equality; the signed symmetry remains the recorded one.
Source: projection reordering (blueprint: det-sp-tower-p1-adjunction). -/
@[instance_reducible]
def TensorData.symmetry {b : SpTowerShriek.Base l E} {T : Scheme.{u}}
    (t : TensorData l E b T) :
    @SymmetricCategory (SpTowerShriek.D l E T) _ (b.calculus T).closed.monoidal :=
  Eq.mp (congrArg (fun z ↦ @SymmetricCategory (SpTowerShriek.D l E T) _ z.monoidal)
    t.closed_eq) t.model.symmetric

/-- Tensor with the coefficient object contracts by actual scalar multiplication.
Source: projection identifications (blueprint: det-sp-tower-p1-adjunction). -/
def TensorData.rightUnit {b : SpTowerShriek.Base l E} {T : Scheme.{u}}
    (t : TensorData l E b T) (K : SpTowerShriek.D l E T) :
    (SpTowerShriek.tensor l E b T).obj (K, unit T (Arings l E T)) ≅ K :=
  (SpTowerShriek.tensor l E b T).mapIso (Iso.prod (Iso.refl K) t.unitIso.symm) ≪≫
    (b.calculus T).closed.monoidal.rightUnitor K

/-- The other coefficient constraint uses the same unit normalization.
Source: the diagonal projection (blueprint: det-sp-tower-p1-adjunction). -/
def TensorData.leftUnit {b : SpTowerShriek.Base l E} {T : Scheme.{u}}
    (t : TensorData l E b T) (K : SpTowerShriek.D l E T) :
    (SpTowerShriek.tensor l E b T).obj (unit T (Arings l E T), K) ≅ K :=
  (SpTowerShriek.tensor l E b T).mapIso (Iso.prod t.unitIso.symm (Iso.refl K)) ≪≫
    (b.calculus T).closed.monoidal.leftUnitor K

/-- The projection arrow is the counit transpose, before any invertibility assertion.
Source: the displayed projection formula (blueprint: det-sp-tower-p1-adjunction). -/
def projection {b : SpTowerShriek.Base l E} {X Y : Scheme.{u}} {f : X ⟶ Y}
    (g : SpTowerShriek.Geometry l E b f)
    (N : SpTowerShriek.D l E X) (K : SpTowerShriek.D l E Y) :
    (SpTowerShriek.tensor l E b Y).obj ((SpTowerShriek.push l E b g).obj N, K) ⟶
      (SpTowerShriek.push l E b g).obj
        ((SpTowerShriek.tensor l E b X).obj (N, (SpTowerShriek.pull l E b g).obj K)) :=
  (SpTowerShriek.adjunction l E b g).homEquiv _ _
    (g.tensorPullback.hom.app ((SpTowerShriek.push l E b g).obj N, K) ≫
      (SpTowerShriek.tensor l E b X).map
        (Prod.mkHom ((SpTowerShriek.adjunction l E b g).counit.app N) (𝟙 _)))

/-- The canonical geometric comparisons used in the displayed formulas. Composition
comes from the recorded ordinary system operations. The identity comparison is fixed
at the ordinary sheaf level, where evaluation is faithful; no equality of general
ordinary-derived morphisms is inferred from their levels.
Source: construction paragraphs (blueprint: det-sp-tower-p1-adjunction). -/
structure Presentation (S : Scheme.{u}) (hS : IsUnit (l : Γ(S, ⊤))) where
  classes : TowerClasses l E S hS
  operations : SpTowerShriek.Operations l E classes.base
  q_geometry : operations.geometry (ProjectiveLine S ↘ S) = classes.projective.geometry
  diagonal_geometry : operations.geometry (diagonalImmersion S) = classes.diagonal.geometry
  tensorS : TensorData l E classes.base S
  tensorP : TensorData l E classes.base (ProjectiveLine S)
  tensorW : TensorData l E classes.base (diagonalSurface S)
  identity : (operations.geometry (𝟙 (ProjectiveLine S))).pull ≅
    𝟭 (SpTowerShriek.S l E (ProjectiveLine S))
  identity_normalization : ∀ (n : ℕ) (M : SpTowerShriek.S l E (ProjectiveLine S)),
    (SpTowerShriek.ev l E (ProjectiveLine S) n).map (identity.hom.app M) =
      ((operations.geometry (𝟙 (ProjectiveLine S))).ordinaryPullEvaluation n).hom.app M ≫
        (proEtaleStalkIdentityPullback (SpTowerShriek.R l E n)
          (ProjectiveLine S)).hom.app ((SpTowerShriek.ev l E (ProjectiveLine S) n).obj M)
  line2 : LinePullback l E
    (pullback.snd (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S))
    (operations.geometry (pullback.snd (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S)))
    classes.chernP classes.chernW

variable {S : Scheme.{u}} {hS : IsUnit (l : Γ(S, ⊤))}

/-- Rq_* in the same recorded system coordinates as the classes.
Source: displayed adjunction (blueprint: det-sp-tower-p1-adjunction). -/
abbrev Presentation.F (p : Presentation l E S hS) :=
  SpTowerShriek.push l E p.classes.base (p.operations.geometry (ProjectiveLine S ↘ S))

/-- q^*(-)(1)[2], as the existing derived tensor with the shifted line.
Source: displayed adjunction (blueprint: det-sp-tower-p1-adjunction). -/
def Presentation.G (p : Presentation l E S hS) :=
  SpTowerShriek.pull l E p.classes.base (p.operations.geometry (ProjectiveLine S ↘ S)) ⋙
    Prod.sectL (SpTowerShriek.D l E (ProjectiveLine S))
      ((line l E p.classes.chernP)⟦(2 : ℤ)⟧) ⋙
        SpTowerShriek.tensor l E p.classes.base (ProjectiveLine S)

/-- Transport of the actual splitting trace along the equality of geometric presentations.
Source: displayed counit (blueprint: det-sp-tower-p1-adjunction). -/
def Presentation.trace (p : Presentation l E S hS) :
    (p.F l E).obj ((line l E p.classes.chernP)⟦(2 : ℤ)⟧) ⟶
      unit S (Arings l E S) :=
  letI := p.classes.splitting
  (eqToIso (congrArg (SpTowerShriek.push l E p.classes.base) p.q_geometry)).hom.app _ ≫
    p.classes.projective.trace l E

/-- Transport of the actual supported diagonal class, with its Kummer sign.
Source: displayed unit (blueprint: det-sp-tower-p1-adjunction). -/
def Presentation.delta (p : Presentation l E S hS) :
    (SpTowerShriek.push l E p.classes.base
      (p.operations.geometry (diagonalImmersion S))).obj
        (unit (ProjectiveLine S) (Arings l E (ProjectiveLine S))) ⟶
      (line l E p.classes.chernW)⟦(2 : ℤ)⟧ :=
  (eqToIso (congrArg (SpTowerShriek.push l E p.classes.base)
    p.diagonal_geometry)).hom.app _ ≫
      diagonalArrow l E p.classes.chernW p.classes.diagonal.sourceIso

/-- The canonical pullback of the shifted Tate line along p2.
Source: displayed unit, final identification (blueprint: det-sp-tower-p1-adjunction). -/
def Presentation.line2Iso (p : Presentation l E S hS) :
    (SpTowerShriek.pull l E p.classes.base (p.operations.geometry
      (pullback.snd (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S)))).obj
        ((line l E p.classes.chernP)⟦(2 : ℤ)⟧) ≅
          (line l E p.classes.chernW)⟦(2 : ℤ)⟧ :=
  ((SpTowerShriek.pull l E p.classes.base (p.operations.geometry
      (pullback.snd (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S)))).commShiftIso
        (2 : ℤ)).app _ ≪≫
    (shiftFunctor _ (2 : ℤ)).mapIso (p.line2.derivedIso l E)

/-- The restriction of p1 or p2 to the diagonal, localized from ordinary composition.
Source: source identification in the unit (blueprint: det-sp-tower-p1-adjunction). -/
def Presentation.diagonalPull (p : Presentation l E S hS)
    (r : diagonalSurface S ⟶ ProjectiveLine S)
    (hr : diagonalImmersion S ≫ r = 𝟙 (ProjectiveLine S)) :
    SpTowerShriek.pull l E p.classes.base (p.operations.geometry r) ⋙
      SpTowerShriek.pull l E p.classes.base (p.operations.geometry (diagonalImmersion S)) ≅
        𝟭 (SpTowerShriek.D l E (ProjectiveLine S)) :=
  p.operations.comp (diagonalImmersion S) r ≪≫
    eqToIso (congrArg (fun f ↦ SpTowerShriek.pull l E p.classes.base
      (p.operations.geometry f)) hr) ≪≫
    Functor.mapDerivedCategoryNatIso p.identity ≪≫
      Functor.mapDerivedCategoryIdIso _

/-- The canonical composition unit M -> Rp2_* RDelta_* M.
Source: first identification in the displayed unit (blueprint: det-sp-tower-p1-adjunction). -/
def Presentation.sourceUnit (p : Presentation l E S hS)
    (M : SpTowerShriek.D l E (ProjectiveLine S)) :
    M ⟶ (SpTowerShriek.push l E p.classes.base (p.operations.geometry
      (pullback.snd (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S)))).obj
        ((SpTowerShriek.push l E p.classes.base
          (p.operations.geometry (diagonalImmersion S))).obj M) :=
  (SpTowerShriek.adjunction l E p.classes.base (p.operations.geometry
    (pullback.snd (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S)))).unit.app M ≫
      (SpTowerShriek.push l E p.classes.base (p.operations.geometry
        (pullback.snd (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S)))).map
          ((SpTowerShriek.adjunction l E p.classes.base
            (p.operations.geometry (diagonalImmersion S))).unit.app _ ≫
              (SpTowerShriek.push l E p.classes.base
                (p.operations.geometry (diagonalImmersion S))).map
                  ((p.diagonalPull l E _ (pullback.diagonal_snd _)).hom.app M))

/-- The proper exchange arrow for the projective-line square: the unit of p2,
the specified pullback square, and the counit of q, in that order.
Source: last identification in the displayed unit (blueprint: det-sp-tower-p1-adjunction). -/
def Presentation.exchange (p : Presentation l E S hS)
    (M : SpTowerShriek.D l E (ProjectiveLine S)) :
    (SpTowerShriek.pull l E p.classes.base
      (p.operations.geometry (ProjectiveLine S ↘ S))).obj ((p.F l E).obj M) ⟶
        (SpTowerShriek.push l E p.classes.base (p.operations.geometry
          (pullback.snd (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S)))).obj
            ((SpTowerShriek.pull l E p.classes.base (p.operations.geometry
              (pullback.fst (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S)))).obj M) :=
  (SpTowerShriek.adjunction l E p.classes.base (p.operations.geometry
    (pullback.snd (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S)))).unit.app _ ≫
      (SpTowerShriek.push l E p.classes.base (p.operations.geometry
        (pullback.snd (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S)))).map
          ((SpTowerShriek.square l E p.classes.base p.operations
            (pullback.fst _ _) (pullback.snd _ _) (ProjectiveLine S ↘ S)
              (ProjectiveLine S ↘ S) pullback.condition).hom.app ((p.F l E).obj M) ≫
            (SpTowerShriek.pull l E p.classes.base
              (p.operations.geometry (pullback.fst _ _))).map
                ((SpTowerShriek.adjunction l E p.classes.base
                  (p.operations.geometry (ProjectiveLine S ↘ S))).counit.app M))

/-- Projection across Delta followed by Delta^*p1^*=1 and scalar multiplication.
Its inverse is the source identification before delta tensor identity.
Source: displayed unit, middle arrow (blueprint: det-sp-tower-p1-adjunction). -/
def Presentation.diagonalProjection (p : Presentation l E S hS)
    (M : SpTowerShriek.D l E (ProjectiveLine S)) :
    (SpTowerShriek.tensor l E p.classes.base (diagonalSurface S)).obj
      ((SpTowerShriek.push l E p.classes.base
        (p.operations.geometry (diagonalImmersion S))).obj
          (unit (ProjectiveLine S) (Arings l E (ProjectiveLine S))),
        (SpTowerShriek.pull l E p.classes.base
          (p.operations.geometry (pullback.fst (ProjectiveLine S ↘ S)
            (ProjectiveLine S ↘ S)))).obj M) ⟶
      (SpTowerShriek.push l E p.classes.base
        (p.operations.geometry (diagonalImmersion S))).obj M :=
  projection l E (p.operations.geometry (diagonalImmersion S)) _ _ ≫
    (SpTowerShriek.push l E p.classes.base
      (p.operations.geometry (diagonalImmersion S))).map
        ((SpTowerShriek.tensor l E p.classes.base (ProjectiveLine S)).map
          (Prod.mkHom (𝟙 _) ((p.diagonalPull l E _
            (pullback.diagonal_fst _)).hom.app M)) ≫
              (p.tensorP.leftUnit l E M).hom)

/-- The domain-preservation and invertible *specified* projection and exchange maps.
All isomorphisms are constrained by equality with the already defined mate arrows.
Source: construction on C^+ (blueprint: det-sp-tower-p1-adjunction). -/
structure Maps (p : Presentation l E S hS) where
  push_closed : ∀ M : C l E p.classes.base (ProjectiveLine S),
    domain l E p.classes.base S ((p.F l E).obj M.obj)
  pull_closed : ∀ K : C l E p.classes.base S,
    domain l E p.classes.base (ProjectiveLine S) ((p.G l E).obj K.obj)
  projectionQ : ∀ K : C l E p.classes.base S,
    (SpTowerShriek.tensor l E p.classes.base S).obj
      ((p.F l E).obj ((line l E p.classes.chernP)⟦(2 : ℤ)⟧), K.obj) ≅
        (p.F l E).obj ((SpTowerShriek.tensor l E p.classes.base (ProjectiveLine S)).obj
          ((line l E p.classes.chernP)⟦(2 : ℤ)⟧,
            (SpTowerShriek.pull l E p.classes.base
              (p.operations.geometry (ProjectiveLine S ↘ S))).obj K.obj))
  projectionQ_eq : ∀ K : C l E p.classes.base S,
    (projectionQ K).hom = projection l E (p.operations.geometry (ProjectiveLine S ↘ S))
      ((line l E p.classes.chernP)⟦(2 : ℤ)⟧) K.obj
  diagonalProjection : ∀ M : C l E p.classes.base (ProjectiveLine S),
    IsIso (p.diagonalProjection l E M.obj)
  exchange : ∀ M : C l E p.classes.base (ProjectiveLine S), IsIso (p.exchange l E M.obj)
  projection2 : ∀ M : C l E p.classes.base (ProjectiveLine S),
    IsIso (projection l E (p.operations.geometry (pullback.snd
      (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S)))
      ((SpTowerShriek.pull l E p.classes.base
        (p.operations.geometry (pullback.fst (ProjectiveLine S ↘ S)
          (ProjectiveLine S ↘ S)))).obj M.obj)
      ((line l E p.classes.chernP)⟦(2 : ℤ)⟧))


/-- Restrict Rq_* to the full domain; its morphisms are unchanged.
Source: displayed adjunction (blueprint: det-sp-tower-p1-adjunction). -/
def left {p : Presentation l E S hS} (d : Maps l E p) :
    C l E p.classes.base (ProjectiveLine S) ⥤ C l E p.classes.base S :=
  ObjectProperty.lift _ ((domain l E p.classes.base (ProjectiveLine S)).ι ⋙ p.F l E)
    d.push_closed

/-- Restrict q^*(-)(1)[2] to the full domain.
Source: displayed adjunction (blueprint: det-sp-tower-p1-adjunction). -/
def rightRestricted {p : Presentation l E S hS} (d : Maps l E p) :
    C l E p.classes.base S ⥤ C l E p.classes.base (ProjectiveLine S) :=
  ObjectProperty.lift _ ((domain l E p.classes.base S).ι ⋙ p.G l E) d.pull_closed

/-- The exact displayed counit: inverse projection, symmetry, identity tensor trace,
and the scalar-multiplication unitor. No arbitrary counit is selected.
Source: displayed epsilon (blueprint: det-sp-tower-p1-adjunction). -/
def epsilon {p : Presentation l E S hS} (d : Maps l E p)
    (K : C l E p.classes.base S) : (p.F l E).obj ((p.G l E).obj K.obj) ⟶ K.obj :=
  (p.F l E).map
    (((p.tensorP.symmetry l E).braiding _ _).hom) ≫
      (d.projectionQ K).inv ≫ ((p.tensorS.symmetry l E).braiding _ _).hom ≫
        (SpTowerShriek.tensor l E p.classes.base S).map
          (Prod.mkHom (𝟙 K.obj) (p.trace l E)) ≫ (p.tensorS.rightUnit l E K.obj).hom

/-- The exact displayed unit: composition unit, inverse diagonal projection,
delta tensor identity, the twist-line projection, and inverse proper exchange.
Source: displayed eta (blueprint: det-sp-tower-p1-adjunction). -/
def eta {p : Presentation l E S hS} (d : Maps l E p)
    (M : C l E p.classes.base (ProjectiveLine S)) : M.obj ⟶
      (p.G l E).obj ((p.F l E).obj M.obj) :=
  letI := d.diagonalProjection M
  letI := d.exchange M
  letI := d.projection2 M
  p.sourceUnit l E M.obj ≫
    (SpTowerShriek.push l E p.classes.base (p.operations.geometry
      (pullback.snd (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S)))).map
        (inv (p.diagonalProjection l E M.obj) ≫
          (SpTowerShriek.tensor l E p.classes.base (diagonalSurface S)).map
            (Prod.mkHom (p.delta l E) (𝟙 _)) ≫
              ((p.tensorW.symmetry l E).braiding _ _).hom ≫
                (SpTowerShriek.tensor l E p.classes.base (diagonalSurface S)).map
                  (Prod.mkHom (𝟙 _) (p.line2Iso l E).inv)) ≫
      inv (projection l E (p.operations.geometry (pullback.snd
        (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S))) _ _) ≫
        (SpTowerShriek.tensor l E p.classes.base (ProjectiveLine S)).map
          (Prod.mkHom (inv (p.exchange l E M.obj)) (𝟙 _))

/-- The bounded-below finite etale-origin domain, using the retained witness interface.
Source: finite evaluations of C^+ (blueprint: det-sp-tower-p1-adjunction). -/
def finiteDomain (T : Scheme.{u}) (n : ℕ) :
    ObjectProperty (proEtaleDerivedCategory T (SpTowerShriek.R l E n)) :=
  fun K ↦ ∃ V : DerivedCategory.Plus (Sheaf (ProEt.topology T)
    (ModuleCat.{u + 1} (ULift.{u + 1} (SpTowerShriek.R l E n)))),
      Nonempty (FixedEtaleOriginWitness T (ULift.{u + 1} (SpTowerShriek.R l E n)) V) ∧
        Nonempty
          (((sfIntrinsicModuleEquivalence T (SpTowerShriek.R l E n)).functor.mapDerivedCategory).obj
            V.obj ≅ K)

/-- Finite direct image is the recorded total derived direct image.
Source: evaluation clause (blueprint: det-sp-tower-p1-adjunction). -/
abbrev finiteF (S : Scheme.{u}) (n : ℕ) :=
  (proEtaleConstantRingPushforward (SpTowerShriek.R l E n)
    (ProjectiveLine S ↘ S)).rightDerivedFunctor

/-- The finite inverse image tensored with the evaluated shifted Tate line.
The line evaluation of TowerClasses identifies this with the usual finite twist.
Source: evaluation clause (blueprint: det-sp-tower-p1-adjunction). -/
def finiteG (p : Presentation l E S hS) (n : ℕ) :=
  proEtaleConstantRingDerivedPullback (SpTowerShriek.R l E n) (ProjectiveLine S ↘ S) ⋙
    Prod.sectL (proEtaleDerivedCategory (ProjectiveLine S) (SpTowerShriek.R l E n))
      ((SpTowerShriek.Ev l E (ProjectiveLine S) n).obj
        ((line l E p.classes.chernP)⟦(2 : ℤ)⟧)) ⋙
      ((p.classes.base.calculus (ProjectiveLine S)).levelClosed n).tensor

/-- Exact evaluation into the finite full domain, retaining its actual level object.
Source: level evaluations (blueprint: det-sp-tower-p1-adjunction). -/
def evaluation (b : SpTowerShriek.Base l E) (T : Scheme.{u}) (n : ℕ) :
    C l E b T ⥤ (finiteDomain l E T n).FullSubcategory :=
  ObjectProperty.lift _ ((domain l E b T).ι ⋙ SpTowerShriek.Ev l E T n)
    (fun K ↦ ⟨(Classical.choice (K.property.2 n)).level,
      ⟨(Classical.choice (K.property.2 n)).witness⟩,
      ⟨(Classical.choice (K.property.2 n)).realization⟩⟩)

/-- Preservation of the finite domains, with the tensor/pullback evaluation specified
componentwise by the recorded canonical comparisons. No free comparison map is used.
Source: finite-level assertion (blueprint: det-sp-tower-p1-adjunction). -/
structure FiniteMaps (p : Presentation l E S hS) (n : ℕ) where
  push_closed : ∀ M : (finiteDomain l E (ProjectiveLine S) n).FullSubcategory,
    finiteDomain l E S n ((finiteF l E S n).obj M.obj)
  pull_closed : ∀ K : (finiteDomain l E S n).FullSubcategory,
    finiteDomain l E (ProjectiveLine S) n ((finiteG l E p n).obj K.obj)
  comparison : p.G l E ⋙ SpTowerShriek.Ev l E (ProjectiveLine S) n ≅
    SpTowerShriek.Ev l E S n ⋙ finiteG l E p n
  comparison_eq : ∀ K : SpTowerShriek.D l E S,
    comparison.hom.app K =
      ((p.classes.base.calculus (ProjectiveLine S)).tensorEvaluation n).hom.app
        ((SpTowerShriek.pull l E p.classes.base
          (p.operations.geometry (ProjectiveLine S ↘ S))).obj K,
            (line l E p.classes.chernP)⟦(2 : ℤ)⟧) ≫
        ((p.classes.base.calculus (ProjectiveLine S)).levelClosed n).tensor.map
          (Prod.mkHom
            (((p.operations.geometry (ProjectiveLine S ↘ S)).pullEvaluation n).hom.app K) (𝟙 _))

/-- The finite left functor restricted without changing morphisms.
Source: finite adjunction (blueprint: det-sp-tower-p1-adjunction). -/
def finiteLeft {p : Presentation l E S hS} {n : ℕ} (d : FiniteMaps l E p n) :=
  ObjectProperty.lift _ ((finiteDomain l E (ProjectiveLine S) n).ι ⋙ finiteF l E S n)
    d.push_closed

/-- The finite right functor restricted without changing morphisms.
Source: finite adjunction (blueprint: det-sp-tower-p1-adjunction). -/
def finiteRight {p : Presentation l E S hS} {n : ℕ} (d : FiniteMaps l E p n) :=
  ObjectProperty.lift _ ((finiteDomain l E S n).ι ⋙ finiteG l E p n) d.pull_closed

/-- Uniformly bounded constructible finite-Tor towers in the system coordinates.
This is only transport of the recorded predicate, not a second definition of Dctf.
Source: final restriction clause (blueprint: det-sp-tower-p1-adjunction). -/
def uniform (b : SpTowerShriek.Base l E) (T : Scheme.{u})
    (a : SpCoefficientTowersAbelian l E T) : ObjectProperty (SpTowerShriek.D l E T) :=
  fun K ↦ spConstructibleTorTowers l E T a
    ((spTowerShriekRealization l E b T a).inverse.obj K)

/-- Adjunction with exactly the displayed maps, finite adjunctions with exactly their
evaluations, and preservation of the full uniformly bounded constructible finite-Tor
subcategories in the standing scheme setting. The last preservation statements, together
with fullness, are precisely the restriction of this same adjunction.
Source: all clauses of the statement (blueprint: det-sp-tower-p1-adjunction). -/
structure AdjunctionData {p : Presentation l E S hS} (d : Maps l E p) where
  adjunction : left l E d ⊣ rightRestricted l E d
  unit_eq : ∀ M : C l E p.classes.base (ProjectiveLine S),
    (domain l E p.classes.base (ProjectiveLine S)).ι.map (adjunction.unit.app M) = eta l E d M
  counit_eq : ∀ K : C l E p.classes.base S,
    (domain l E p.classes.base S).ι.map (adjunction.counit.app K) = epsilon l E d K
  finiteMaps : ∀ n : ℕ, FiniteMaps l E p n
  finiteAdjunction : ∀ n : ℕ, finiteLeft l E (finiteMaps n) ⊣ finiteRight l E (finiteMaps n)
  finite_unit : ∀ (n : ℕ) (M : C l E p.classes.base (ProjectiveLine S)),
    (SpTowerShriek.Ev l E (ProjectiveLine S) n).map (eta l E d M) ≫
      (finiteMaps n).comparison.hom.app ((p.F l E).obj M.obj) ≫
        (finiteG l E p n).map
          (((p.operations.geometry (ProjectiveLine S ↘ S)).pushEvaluation n).hom.app M.obj) =
      (finiteDomain l E (ProjectiveLine S) n).ι.map
        ((finiteAdjunction n).unit.app
          ((evaluation l E p.classes.base (ProjectiveLine S) n).obj M))
  finite_counit : ∀ (n : ℕ) (K : C l E p.classes.base S),
    (finiteF l E S n).map ((finiteMaps n).comparison.inv.app K.obj) ≫
      ((p.operations.geometry (ProjectiveLine S ↘ S)).pushEvaluation n).inv.app
        ((p.G l E).obj K.obj) ≫ (SpTowerShriek.Ev l E S n).map (epsilon l E d K) =
      (finiteDomain l E S n).ι.map
        ((finiteAdjunction n).counit.app ((evaluation l E p.classes.base S n).obj K))
  constructible_restriction : ∀ (pchar : ℕ) [Fact pchar.Prime]
    (k : Type u) [Field k] [CharP k pchar], l ≠ pchar →
    ∀ [S.Over (Spec (.of k))] [IsSeparated (S ↘ Spec (.of k))]
      [LocallyOfFiniteType (S ↘ Spec (.of k))] [QuasiCompact (S ↘ Spec (.of k))]
      (aS : SpCoefficientTowersAbelian l E S)
      (aP : SpCoefficientTowersAbelian l E (ProjectiveLine S)),
      (∀ M : SpTowerShriek.D l E (ProjectiveLine S),
        uniform l E p.classes.base (ProjectiveLine S) aP M →
          domain l E p.classes.base (ProjectiveLine S) M ∧
            uniform l E p.classes.base S aS ((p.F l E).obj M)) ∧
      (∀ K : SpTowerShriek.D l E S, uniform l E p.classes.base S aS K →
        domain l E p.classes.base S K ∧ uniform l E p.classes.base (ProjectiveLine S) aP
          ((p.G l E).obj K))

/-- The projective-line tower adjunction with its specified diagonal unit and splitting trace
counit, all positive finite levels, and its constructible finite-Tor restriction.
Source: blueprint main-20261015, sk-prop-sp-tower-geometric-p1.md and its proof
(blueprint: det-sp-tower-p1-adjunction).

Proof plan, in the order of the DAG:

1. Put $P=\mathbf P^1_S$, $W=P\times_SP$, $A_T=\mathcal O_{E,T}/\ell^\bullet$, $F=Rq_{*,\bullet}$
and $G=q_\bullet^*(-)(1)[2]$. By [sk-lem-sp-tower-levels], these direct images are bounded below
and evaluate to the finite direct images. The canonical comparison
[lem-weil-pbc-comparison-direct-image-canonical-mate] applies to $q,p_1,p_2,\Delta$, which are
quasi-compact and quasi-separated, and therefore their direct images preserve etale-origin levels.
Pullback preserves such levels by [lem-weil-pbc-comparison-pullback]. The finite twist is a
locally free rank-one sheaf, compatible with pullback, by [lem-asd-etale-finite-twist-pullback]
with $N=\ell^n$ and $A=\mathcal O_E/\ell^n$. Thus $F,G$ preserve the stated bounded-below
etale-origin domains.

2. Each of $q,p_1,p_2$ is a projective-line projection, hence proper by
[lemma-nagata-projective-space-base-change-proper]. The diagonal is a closed Cartier divisor by
[det-sp-tower-classes], hence proper by [lem-weil-pbc-closed-immersion-proper](a). Its
complementary open is quasi-compact: over each affine open of $W$, finitely many principal opens
trivialize the invertible ideal, and the complement on each is one more principal open. Thus
[lem-exc-proetale-closed-exact] makes $\Delta_*$ exact at every finite level. Exactness on towers
is levelwise by [det-sp-coefficient-towers-abelian], so $R\Delta_{*,\bullet}=\Delta_*$, justifying
the notation in the unit formula.

3. Form the canonical tensor, projection, composition and exchange maps on the simultaneous
section models [lem-coef-semilinear-derived-sections]. These exist in the ambient unbounded
derived category and evaluate to their finite maps. At level $n$, put $B=\mathcal O_E/\ell^n$. On
the ordinary etale site, [lem-kun-0f0g] makes the projection maps for $q,p_1,p_2,\Delta$
invertible for these coefficients and arbitrary derived inputs. For the present etale-origin
inputs, [lem-weil-pbc-ringed-topoi-derived-tensor-pullback] applied to $\nu^*$ transports tensor,
and [lem-weil-pbc-comparison-direct-image-canonical-mate] transports the direct images of the
bounded-below arguments. The canonical comparisons transport the projection map itself: both maps
are the transpose of the same counit tensored with identity, so the normalization in the
direct-image comparison identifies their transposes. The finite etale projection identities also
show that the tensors occurring here are bounded below: their targets are respectively
$Rq_*q^{-1}K(1)[2]$, $R\Delta_*M$, or $Rp_{i*}p_i^{-1}M(1)[2]$. For the last two projection
reorderings, $Rp_{i*}B_W(1)[2]$ is a sum of two shifted flat lines by
[lem-sp-tower-p1-arbitrary-base-integrals], so its tensor with $M$ is bounded below. Proper
exchange is invertible by [lem-kun-proper-base-change-torsion-ring], and the same counit-mate
normalization transports its actual map. Hence every evaluated projection and exchange map used
here is invertible. Tower evaluation detects isomorphisms by [det-sp-tower-shriek-levels](3), so
the actual tower maps are invertible. This avoids applying that node's restricted finite-Tor
projection clause outside its hypotheses.

4. The projection isomorphism for $\Delta$, with $\Delta^*p_1^*M=M$, identifies $\Delta_*M$ with
$\Delta_*A_P\otimes^Lp_1^*M$. Exchange identifies $Rp_{2*,\bullet}p_1^*M$ with $q_\bullet^*FM$,
and the projection formula for $q$ identifies $FGK$ with $K\otimes^LRq_{*,\bullet}A_P(1)[2]$, as
in step 3. Composing with the actual diagonal class and trace of [det-sp-tower-classes] gives
precisely the displayed natural $\eta$ and $\varepsilon$. Their naturality and evaluations follow
from [lem-coef-semilinear-derived-sections]. Write $t_i=\operatorname{Tr}_{p_i,\bullet}$. Under
exchange $t_i$ is the base change of the trace for $q$: the splitting components are the unit and
$c_1(\mathcal O(1))$; pullback preserves the unit, pulls back $\mathcal O(1)$, and commutes with
the Kummer boundary. It therefore carries the splitting, its inverse, and its second projection to
those on the base change. This is an identity of the actual tower constructions, not an inference
of equality from evaluation.

5. *The two scalar endomorphisms and detection.* Let
$\alpha_i:A_P\xrightarrow{\sim}Rp_{i*,\bullet}\Delta_*A_P$ be the composition identification for
$p_i\Delta=1_P$, and put $c_i=t_i\circ Rp_{i*,\bullet}(\delta_\bullet)\circ\alpha_i$. These are
endomorphisms of $A_P[0]$. Apply [lem-weil-pbc-derived-single-fully-faithful] to the abelian tower
category of [det-sp-coefficient-towers-abelian]: each $c_i$ is a unique compatible family of
module-sheaf maps. If all evaluated $c_i$ are identities, their underlying families equal the
identity family, so $c_i=1$. This uses equality detection only between these degree-zero objects.
The composition identification is the canonical derived-direct-image comparison supplied on tower
section models by [lem-coef-semilinear-derived-sections].

6. Fix $n\geq1$ and put $N=\ell^n$, $B=\mathcal O_E/\ell^n$. This is a finite torsion ring and $N$
is invertible on $S$. Exact evaluation and the canonical direct-image comparison identify the
level of $c_i$ from step 5 with the pro-etale image of the finite etale composite $t_P\circ
Rp_{i*}(\delta_B)\circ\alpha_i$: [sk-lem-sp-tower-levels] and
[lem-coef-semilinear-derived-sections] identify the actual direct-image and composition maps,
[lem-weil-pbc-comparison-direct-image-canonical-mate] specifies the comparison, and
[det-sp-tower-classes] identifies the evaluated splitting, trace and supported class. The finite
identity is exactly [lem-sp-tower-p1-arbitrary-base-integrals], which assumes neither a Noetherian
nor a finite-type base. Applying $\nu_P^*$ gives $(c_i)_n=1$ for both $i$. Step 5 now gives
$c_1=c_2=1$ in the ordinary derived category of towers.

7. *First triangle, integrating along $p_1$.* Expand $F\eta_M$ using its definition, replace
$qp_2$ by $qp_1$, and then apply $\varepsilon_{FM}$. With the canonical direct-image composition
maps and the projection formula established in step 3 this gives
$$FM=R(qp_1)_{*,\bullet}\Delta_*M\longrightarrow R(qp_1)_{*,\bullet}p_1^*M(1)[2]\simeq
F\bigl(M\otimes^LRp_{1*,\bullet}A_W(1)[2]\bigr)\xrightarrow{F(1_M\otimes t_1)}FM.$$ Here $t_1$ is
the base-changed trace identified in step 4. The first arrow is $\delta_\bullet\otimes p_1^*M$.
Naturality of the projection comparison identifies its pushforward along $p_1$, including the
source identification $\Delta^*p_1^*M=M$, with $1_M\otimes Rp_{1*,\bullet}\delta_\bullet$. The
exchange and projection reordering is the equality in
[lem-weil-pbc-ringed-exchange-tensor-coherence] on the tower-topos ring object $A_\bullet$;
[lem-coef-semilinear-derived-sections] supplies the specified composition comparisons on this
model. Thus the entire composite is $F(1_M\otimes c_1)=1_{FM}$ by step 6, rather than merely a map
which becomes an identity on evaluation.

8. *Second triangle, integrating along $p_2$.* Put $M=GK$. On $W$ both $p_1^*M$ and $p_2^*M$ equal
$(qp_1)^*K(1)[2]$, since $qp_1=qp_2$ and the twist pulls back from $S$. Factor $p_2^*M$ out of
$Rp_{2*,\bullet}(A_W\otimes^Lp_2^*M)(1)[2]$ using the projection formula established in step 3.
The arrow induced by $\delta_\bullet$ becomes $1_M\otimes Rp_{2*,\bullet}\delta_\bullet$, with
source $M\otimes A_P$. Under proper exchange, $G\varepsilon_K$ contracts the remaining factor
$Rp_{2*,\bullet}A_W(1)[2]$ by $t_2$, by step 4. The exchange/projection compatibility
[lem-weil-pbc-ringed-exchange-tensor-coherence] on the same tower ringed topos verifies these are
the canonical maps. Hence $G\varepsilon_K\circ\eta_{GK}=1_{GK}\otimes c_2=1_{GK}$. Only even
shifts have been moved past tensor factors, so their Koszul signs are $(-1)^{2j}=1$. The
interchange of the two unshifted twist lines is also the identity: locally choose a generator $e$;
the symmetry sends $ae\otimes be$ to $be\otimes ae=ab(e\otimes e)$ over the commutative
coefficient ring. These local equalities give the stated canonical symmetry globally.

9. *Adjunction from the two triangles.* For a tower map $u:FM\to K$ define
$\Phi(u)=G(u)\circ\eta_M$, and for $v:M\to GK$ define $\Psi(v)=\varepsilon_K\circ F(v)$.
Naturality and step 7 give $\Psi\Phi(u)=u\circ\varepsilon_{FM}\circ F\eta_M=u$. Naturality and
step 8 give $\Phi\Psi(v)=G\varepsilon_K\circ\eta_{GK}\circ v=v$. These operations are natural in
$M,K$, so they are the Hom bijection exhibiting $F\dashv G$ with the specified unit and counit.

10. *Evaluation and restriction.* For each $n\geq1$, exact evaluation sends $A_\bullet$ to
$(\mathcal O_E/\ell^n)_T$, sends $\delta_\bullet$ to the finite supported diagonal class, and
sends the splitting inverse followed by its second projection to the finite trace, by
[det-sp-tower-classes]. The specified tensor, direct-image, exchange and projection comparisons
evaluate to their finite comparisons by the section models [lem-coef-semilinear-derived-sections]
and the maps constructed in step 3; shifts and inverse image are termwise. Substituting these in
the displayed formulas gives the finite diagonal-defined unit and splitting-trace-defined counit
with the actual coefficients $B=\mathcal O_E/\ell^n$.

11. Here is an explicit verification that these maps form the finite adjunction on bounded-below
etale-origin levels. Given a bounded-below complex $L$ of etale $B$-module sheaves on a scheme
$T$, put $\nu_T^*L$ at level $n$ and the zero complex at every other level, with every transition
zero. This is a bounded-below complex of towers by the componentwise definition
[sk-def-sp-coefficient-towers], and is in $\mathscr C^+(T)$. Denote its derived object by $J_nL$.
Write $F_n=Rq_{*,B}$ and $G_n=q^{-1}(-)(1)[2]$ on the finite etale categories. Evaluate the first
tower triangle of step 7 on $J_nM$, for arbitrary $M\in D^+(P_{\mathrm{et}},B)$: the specified
comparisons give $$\nu_S^*\bigl(\varepsilon_{n,F_nM}\circ F_n(\eta_{n,M})\bigr)=1_{\nu_S^*F_nM}.$$
Evaluate the second tower triangle of step 8 on $J_nK$, for arbitrary $K\in
D^+(S_{\mathrm{et}},B)$: they give
$$\nu_P^*\bigl(G_n(\varepsilon_{n,K})\circ\eta_{n,G_nK}\bigr)=1_{\nu_P^*G_nK}.$$ Full faithfulness
[sk-prop-sf-comparison] removes $\nu^*$ from both equalities. Thus the finite maps satisfy both
triangles for every finite bounded-below input. Explicitly the inverse Hom operations are
$u\mapsto G_n(u)\eta_{n,M}$ and $v\mapsto\varepsilon_{n,K}F_n(v)$, whose composites are
$u\varepsilon_{n,F_nM}F_n\eta_{n,M}=u$ and $G_n\varepsilon_{n,K}\eta_{n,G_nK}v=v$. This proves the
finite adjunction over the arbitrary base using the evaluated maps.

12. Now assume the standing setting [sk-def-sfb-dc-setting]: $S$ is separated and of finite type
over a field of characteristic $p>0$, with $p\ne\ell$. To see that the full uniformly bounded
constructible finite-Tor subcategories lie in $\mathscr C^+$, use
[sk-thm-pe-constructible-comparison] locally on affine $U$ and
[det-pe-classical-derived-equivalence] with [sk-prop-sf-comparison]: the classical cohomology
condition is local, so the bounded-below equivalence gives a global etale-origin witness for each
bounded constructible level. Uniform cohomological bounds give a bounded-below tower because tower
cohomology and vanishing are levelwise [det-sp-coefficient-towers-abelian].

13. [sk-lem-sp-tower-bound], with $f=q$, preserves uniformly bounded constructible finite-Tor
towers under $F$. The map $q$ is a separated finite-type morphism of the standing schemes, smooth
of relative dimension one, so this application satisfies the hypotheses of
[sk-lem-sp-tower-bound].

14. For $G$ the bounds can be checked locally over each affine open $U\subseteq S$, where both $U$
and $\mathbf P^1_U$ are quasi-compact and quasi-separated. With $B=\mathcal O_E/\ell^n$, the
constructible comparison [sk-thm-pe-constructible-comparison] gives a bounded constructible etale
representative $L_n$ of $K_n|_U$. The same fixed Tor interval $[a,b]$ holds for $L_n$ by
[lem-exc-comparison-tor-interval]. Choose its flat representative supported in $[a,b]$ using
[lem-sf-etale-flat-model]. A bounded complex of flat sheaves is K-flat: tensoring each flat term
with an acyclic complex is acyclic, and the finite filtration by shifted terms gives the assertion
for the complex. The termwise pullback along $q$ is K-flat with flat terms by
[lem-weil-pbc-ringed-topos-kflat-pullback], and remains supported in $[a,b]$. Tensor with the
locally free rank-one twist of [lem-asd-finite-etale-twist-line] and shift by $[2]$ gives a flat
complex supported in $[a-2,b-2]$; its tensor with any degree-zero test sheaf has no other terms,
so this is its Tor interval. Transfer the interval back to the pro-etale site by
[lem-exc-comparison-tor-interval]. Exact inverse image preserves the cohomological interval, and
inverse-image strata and their pulled-back finite constant trivializations show constructibility.
These bounds hold for every $n$ and every $U$; vanishing is local, so they hold globally, with the
shift moving both bounds by $-2$. Hence both functors preserve the full tower subcategories
[sk-def-sp-normalized-towers], and the same Hom bijection restricts to them.
-/
theorem exists_towerP1Adjunction (S : Scheme.{u}) (hS : IsUnit (l : Γ(S, ⊤))) :
    ∀ p : Presentation l E S hS, ∃ d : Maps l E p, Nonempty (AdjunctionData l E d) := by
  sorry

end AlgebraicGeometry.ProEtale.SpTowerP1

attribute [instance high] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
