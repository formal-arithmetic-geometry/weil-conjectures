/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q53
-/
module

public import Sheaf.Paper.RamifiedRootTower
public import Sheaf.Paper.CartierDualKummerNormalization
public import Sheaf.AlgebraicGeometry.OrdinarySupportedCartierKummer
public import WeilConjectures.SixFunctors.OpenClosed.SupportedSections
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperLowerStar
public import Sheaf.AlgebraicGeometry.ExactUnboundedExchange
public import WeilConjectures.SixFunctors.ProEtale.Comparison.LowerStarAcyclic
import Sheaf.AlgebraicGeometry.ProEtaleDirectImageComparison
public import Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions
public import WeilConjectures.SixFunctors.BaseChange.Derived
import Sheaf.AlgebraicGeometry.RelativeHigherDirectImageContinuity
import Sheaf.AlgebraicGeometry.ExchangeForgetCoefficients
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence

/-! # Finite torsion on ramified regular root limits

Source: Stacks Project, Tag 0EYM; ILO Expose XVI, Section 2.1 and Theorem 3.1.1;
blueprint main-20261015, discrete direct-image comparison
(blueprint: lem-sfb-ramified-root-limit-torsion-unit).

## Main definitions and statement

- `support`, `inclusion`, `unit`: the canonical supported model of the actual unit's fibre.
- `KummerNormalized`, `closedExchange`: relative Kummer orientation and closed Tate exchange.
- `OpenSystem`, `limitTransition`: the actual punctured system and its cohomology transitions.
- `sitePullback`, `siteMate`: the canonical ordinary etale-to-proetale derived comparisons.
- `RootLimitAssertion`: all finite-stage, transition, colimit, vanishing and unit clauses.
- `ramifiedRootLimitTorsionUnit`: puncture invariance for finite torsion on the full root limit.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite
open CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale.RamifiedRoot

/-- Finite coefficients in the site's coefficient universe. Source: Stacks 0EYM
(blueprint: lem-sfb-ramified-root-limit-torsion-unit). -/
abbrev Coeff (ℓ s : ℕ) := ULift.{u + 1} (ZMod (ℓ ^ s))

variable (A : Type (u + 1)) [CommRing A]

/-- The existing derived supported-sections functor, applied to the constant object.
It is the fibre of the actual open unit, rather than a chosen unrelated cone.
Source: Stacks 0EYM, fibre triangle (blueprint: lem-sfb-ramified-root-limit-torsion-unit). -/
def support {U X : Scheme.{u}} (j : U ⟶ X) : DerivedCategoryModule A X :=
  (sectionsWithSupport (ModuleCat.{u + 1} A) j).rightDerivedFunctor.obj
    (ordinaryFiniteUnit A X)

/-- The canonical forget-support map, obtained by deriving the kernel inclusion.
Source: Stacks 0EYM, fibre triangle (blueprint: lem-sfb-ramified-root-limit-torsion-unit). -/
def inclusion {U X : Scheme.{u}} (j : U ⟶ X) : support A j ⟶ ordinaryFiniteUnit A X :=
  (Functor.rightDerivedFunctorNatTrans
    (sectionsWithSupportι (ModuleCat.{u + 1} A) j)).app (ordinaryFiniteUnit A X) ≫
      (Functor.rightDerivedFunctorIsoMapDerivedCategory
        (𝟭 (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)))).hom.app (ordinaryFiniteUnit A X) ≫
      (Functor.mapDerivedCategoryIdIso _).hom.app (ordinaryFiniteUnit A X)

/-- The actual open adjunction unit on the coefficient object.
Source: Stacks 0EYM, unit normalization
(blueprint: lem-sfb-ramified-root-limit-torsion-unit). -/
def unit {U X : Scheme.{u}} (j : U ⟶ X) :=
  (mapDerivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) j).unit.app
    (ordinaryFiniteUnit A X)

/-- Canonical constant identification for exact derived pullback.
Source: Stacks 0EYM, coefficient diagram
(blueprint: lem-sfb-ramified-root-limit-torsion-unit). -/
def constantPullback {X Y : Scheme.{u}} (h : X ⟶ Y) :
    (upperStar (ModuleCat.{u + 1} A) h).mapDerivedCategory.obj
      (ordinaryFiniteUnit A Y) ≅ ordinaryFiniteUnit A X :=
  ((upperStar (ModuleCat.{u + 1} A) h).mapDerivedCategorySingleFunctor 0).app _ ≪≫
    (DerivedCategory.singleFunctor _ 0).mapIso
      ((Scheme.upperStarConstantSheafIso (ModuleCat.{u + 1} A) h).app (ModuleCat.of A A))

/-- The coefficient object of the ordinary uncompleted pro-etale category.
Source: blueprint sk-thm-pe-direct-image-comparison, discrete coefficients
(blueprint: lem-sfb-ramified-root-limit-torsion-unit). -/
def proetaleConstant (X : Scheme.{u}) :=
  (DerivedCategory.singleFunctor
    (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)) 0).obj
    ((constantSheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)).obj (ModuleCat.of A A))

/-- The actual K-injective total-derived pro-etale open adjunction unit.
Source: blueprint sk-thm-pe-direct-image-comparison
(blueprint: lem-sfb-ramified-root-limit-torsion-unit). -/
def proetaleUnit {U X : Scheme.{u}} (j : U ⟶ X) :=
  (ProEtale.derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) j).unit.app
    (proetaleConstant A X)

/-- The canonical supported arrow is characterized by its forget-support square.
For objects supported on the closed complement, the support counit has exactly
this universal property; this prevents an arbitrary transition being substituted.
Source: Stacks 0EYM (blueprint: lem-sfb-ramified-root-limit-torsion-unit). -/
def SupportExchange {U U' X X' : Scheme.{u}} (j : U ⟶ X) (j' : U' ⟶ X')
    (h : X' ⟶ X)
    (θ : (upperStar (ModuleCat.{u + 1} A) h).mapDerivedCategory.obj (support A j) ⟶
      support A j') : Prop :=
  θ ≫ inclusion A j' =
    (upperStar (ModuleCat.{u + 1} A) h).mapDerivedCategory.map (inclusion A j) ≫
      (constantPullback A h).hom

/-- Exact pullback of supported cohomology followed by the chosen supported exchange.
Source: Stacks 0EYM, actual continuity legs
(blueprint: lem-sfb-ramified-root-limit-torsion-unit). -/
def cohomologyExchange {U U' X X' : Scheme.{u}} (j : U ⟶ X) (j' : U' ⟶ X')
    (h : X' ⟶ X)
    (θ : (upperStar (ModuleCat.{u + 1} A) h).mapDerivedCategory.obj (support A j) ⟶
      support A j') (q : ℤ) :
    (upperStar (ModuleCat.{u + 1} A) h).obj
        ((DerivedCategory.homologyFunctor _ q).obj (support A j)) ⟶
      (DerivedCategory.homologyFunctor _ q).obj (support A j') :=
  ((upperStar (ModuleCat.{u + 1} A) h).mapDerivedCategoryHomologyFunctorIso q).hom.app _ ≫
    (DerivedCategory.homologyFunctor _ q).map θ

/-- The restricted inverse system and its cone, with each arrow fixed by its
commuting inclusion square. Monicity makes these maps unique, including the
maps out of the limit. Source: Stacks 0EYM
(blueprint: lem-sfb-ramified-root-limit-torsion-unit). -/
structure OpenSystem {p ℓ : ℕ} (T : RamifiedRootTower.{u} p ℓ) where
  map : ∀ {n m : RamifiedRootIndex p} (_a : n ⟶ m), T.puncture m ⟶ T.puncture n
  square : ∀ {n m : RamifiedRootIndex p} (a : n ⟶ m),
    map a ≫ T.open n = T.open m ≫ T.diagram.map a.op
  leg : ∀ n : RamifiedRootIndex p, T.limitOpen ⟶ T.puncture n
  leg_square : ∀ n : RamifiedRootIndex p,
    leg n ≫ T.open n = T.limitInclusion ≫ T.cone.π.app (op n)

/-- The genuine functor of the punctured stages, whose laws follow from the
inclusion squares. Source: Stacks 0EYM
(blueprint: lem-sfb-ramified-root-limit-torsion-unit). -/
def OpenSystem.diagram {p ℓ : ℕ} {T : RamifiedRootTower.{u} p ℓ} (O : OpenSystem T) :
    (RamifiedRootIndex p)ᵒᵖ ⥤ Scheme.{u} where
  obj n := T.puncture n.unop
  map a := O.map a.unop
  map_id n := by
    apply (cancel_mono (T.open n.unop)).1
    simp [O.square]
  map_comp a b := by
    apply (cancel_mono (T.open _)).1
    simp only [Category.assoc, O.square]
    rw [← Category.assoc, O.square, Category.assoc, ← T.diagram.map_comp]
    rfl

/-- The canonical cone on the punctured stages. Source: Stacks 0EYM
(blueprint: lem-sfb-ramified-root-limit-torsion-unit). -/
def OpenSystem.cone {p ℓ : ℕ} {T : RamifiedRootTower.{u} p ℓ} (O : OpenSystem T) :
    Cone O.diagram where
  pt := T.limitOpen
  π := {
    app n := O.leg n.unop
    naturality n m a := by
      apply (cancel_mono (T.open m.unop)).1
      change (𝟙 _ ≫ O.leg m.unop) ≫ T.open m.unop =
        (O.leg n.unop ≫ O.map a.unop) ≫ T.open m.unop
      rw [Category.id_comp, Category.assoc, O.square, ← Category.assoc, O.leg_square n.unop,
        Category.assoc, T.cone.w]
      exact O.leg_square m.unop }


/-- The transition on the cohomology diagram pulled to the limit, using the
canonical inverse-image composition comparison and the limit cone equation.
Source: Stacks 0EYM (blueprint: lem-sfb-ramified-root-limit-torsion-unit). -/
def limitTransition {p ℓ : ℕ} (T : RamifiedRootTower.{u} p ℓ)
    {n m : RamifiedRootIndex p} (a : n ⟶ m)
    (θ : (upperStar (ModuleCat.{u + 1} A) (T.diagram.map a.op)).mapDerivedCategory.obj
      (support A (T.open n)) ⟶ support A (T.open m)) (q : ℤ) :
    (upperStar (ModuleCat.{u + 1} A) (T.cone.π.app (op n))).obj
        ((DerivedCategory.homologyFunctor _ q).obj (support A (T.open n))) ⟶
      (upperStar (ModuleCat.{u + 1} A) (T.cone.π.app (op m))).obj
        ((DerivedCategory.homologyFunctor _ q).obj (support A (T.open m))) :=
  ((eqToIso (congrArg (upperStar (ModuleCat.{u + 1} A)) (T.cone.w a.op).symm)) ≪≫
    upperStarComp (ModuleCat.{u + 1} A) (T.cone.π.app (op m))
      (T.diagram.map a.op)).hom.app _ ≫
    (upperStar (ModuleCat.{u + 1} A) (T.cone.π.app (op m))).map
      (cohomologyExchange A (T.open n) (T.open m) (T.diagram.map a.op) θ q)

/-- The actual open exchange on the last terms of the unit triangles.
Source: Stacks 0EYM, exchange mate
(blueprint: lem-sfb-ramified-root-limit-torsion-unit). -/
def openExchange {U U' X X' : Scheme.{u}} {j : U ⟶ X} {j' : U' ⟶ X'}
    {h : X' ⟶ X} {w : U' ⟶ U} (sq : CommSq w j' j h) :
    (upperStar (ModuleCat.{u + 1} A) h).mapDerivedCategory.obj
        ((lowerStar (ModuleCat.{u + 1} A) j).rightDerivedFunctor.obj
          ((upperStar (ModuleCat.{u + 1} A) j).mapDerivedCategory.obj
            (ordinaryFiniteUnit A X))) ⟶
      (lowerStar (ModuleCat.{u + 1} A) j').rightDerivedFunctor.obj
        ((upperStar (ModuleCat.{u + 1} A) j').mapDerivedCategory.obj
          (ordinaryFiniteUnit A X')) :=
  (exactDerivedBaseChangeMap (ModuleCat.{u + 1} A) sq).app _ ≫
    (lowerStar (ModuleCat.{u + 1} A) j').rightDerivedFunctor.map
      ((exactDerivedSquareUpperStarIso (ModuleCat.{u + 1} A) sq).inv.app _ ≫
        (upperStar (ModuleCat.{u + 1} A) j').mapDerivedCategory.map
          (constantPullback A h).hom)

/-- The unit's actual target, retained to state the full fibre triangle.
Source: Stacks 0EYM (blueprint: lem-sfb-ramified-root-limit-torsion-unit). -/
abbrev openTarget {U X : Scheme.{u}} (j : U ⟶ X) :=
  (lowerStar (ModuleCat.{u + 1} A) j).rightDerivedFunctor.obj
    ((upperStar (ModuleCat.{u + 1} A) j).mapDerivedCategory.obj (ordinaryFiniteUnit A X))

/-- The support triangle is the fibre triangle of the actual unit, including
its signed connecting map. Source: Stacks 0EYM
(blueprint: lem-sfb-ramified-root-limit-torsion-unit). -/
def IsFibreTriangle {U X : Scheme.{u}} (j : U ⟶ X)
    (δ : openTarget A j ⟶ (support A j)⟦(1 : ℤ)⟧) : Prop :=
  Pretriangulated.Triangle.mk (inclusion A j) (unit A j) δ ∈ distTriang _

/-- Derived inverse-image comparison for the two ordinary sites. Exact inverse
images are descended termwise, with the published comparison to left derivation.
Source: blueprint discrete comparison
(blueprint: lem-sfb-ramified-root-limit-torsion-unit). -/
def sitePullback {U X : Scheme.{u}} (j : U ⟶ X) :
    (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory ⋙
        (ProEtale.upperStar (ModuleCat.{u + 1} A) j).leftDerivedFunctor ≅
      (upperStar (ModuleCat.{u + 1} A) j).mapDerivedCategory ⋙
        (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) U).mapDerivedCategory :=
  Functor.isoWhiskerLeft _ (ProEtale.leftDerivedUpperStarIsoMapDerivedCategory
    (ModuleCat.{u + 1} A) j) ≪≫
    (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryNatIso
      (ProEtale.comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} A) j) ≪≫
    Functor.mapDerivedCategoryCompIso _ _

/-- The comparison is the actual adjunction mate, in the uncompleted derived
categories, rather than a selected isomorphism. Source: blueprint discrete comparison
(blueprint: lem-sfb-ramified-root-limit-torsion-unit). -/
def siteMate {U X : Scheme.{u}} (j : U ⟶ X) :
    (lowerStar (ModuleCat.{u + 1} A) j).rightDerivedFunctor ⋙
        (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory ⟶
      (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) U).mapDerivedCategory ⋙
        (ProEtale.lowerStar (ModuleCat.{u + 1} A) j).rightDerivedFunctor :=
  (mateEquiv (mapDerivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) j)
    (ProEtale.derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) j)
    (TwoSquare.mk _ _ _ _ (sitePullback A j).hom)).natTrans

/-- The full derived ramification formula, with the nonreduced inverse-image
divisor and its actual reduction retained as distinct schemes.
Source: ILO XVI 2.1 (blueprint: lem-sfb-ramified-root-limit-torsion-unit). -/
def TransitionFormula {p ℓ : ℕ} (T : RamifiedRootTower.{u} p ℓ)
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    (hD : ∀ n, IsUnit (N : Γ(T.divisor n, ⊤)))
    (P : ∀ n, closedDual A N hA (T.closed n) ≅ (support A (T.open n))⟦(2 : ℤ)⟧)
    (θ : ∀ {n m : RamifiedRootIndex p} (a : n ⟶ m),
      (upperStar (ModuleCat.{u + 1} A) (T.diagram.map a.op)).mapDerivedCategory.obj
        (support A (T.open n)) ⟶ support A (T.open m)) : Prop :=
  ∀ {n m : RamifiedRootIndex p} (a : n ⟶ m),
    let e := m.val / n.val
    let E := (T.stage m).zeroLocusSubscheme {T.parameter m ^ e}
    let k := (T.stage m).zeroLocusSubschemeι {T.parameter m ^ e}
    ∃ (r : T.divisor m ⟶ E) (d : E ⟶ T.divisor n)
      (hr : r ≫ k = T.closed m)
      (hd : d ≫ T.closed n = k ≫ T.diagram.map a.op),
      (upperStar (ModuleCat.{u + 1} A) (T.diagram.map a.op)).mapDerivedCategory.map
          (P n).hom ≫
        ((upperStar (ModuleCat.{u + 1} A) (T.diagram.map a.op)).mapDerivedCategory.commShiftIso
          (2 : ℤ)).hom.app _ ≫ (θ a)⟦(2 : ℤ)⟧' =
      (e • closedExchange A N hN hA
        (CommSq.mk (show (r ≫ d) ≫ T.closed n = T.closed m ≫ T.diagram.map a.op from by
          rw [Category.assoc, hd, ← Category.assoc, hr])) (hD n) (hD m)) ≫ (P m).hom

/-- All clauses of root-limit puncture invariance, with the finite coefficient
ring supplied explicitly. This is a transparent statement predicate, not additional
hypotheses or chosen comparison data. Source: Stacks 0EYM; ILO XVI 2.1 and 3.1.1
(blueprint: lem-sfb-ramified-root-limit-torsion-unit). -/
def RootLimitAssertion {p ℓ : ℕ} (T : RamifiedRootTower.{u} p ℓ)
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0) : Prop :=
    ∃ O : OpenSystem T,
      Nonempty (IsLimit O.cone) ∧
      (∀ {n m : RamifiedRootIndex p} (a : n ⟶ m),
        IsPullback (O.map a) (T.open m) (T.open n) (T.diagram.map a.op)) ∧
      (∀ n : RamifiedRootIndex p,
        IsPullback (O.leg n) T.limitInclusion (T.open n) (T.cone.π.app (op n))) ∧
      ∃ (hI : ∀ n, (T.closed n).ker.IsInvertible)
        (hX : ∀ n, IsUnit (N : Γ(T.stage n, ⊤)))
        (hD : ∀ n, IsUnit (N : Γ(T.divisor n, ⊤)))
        (P : ∀ n, closedDual A N hA (T.closed n) ≅
          (support A (T.open n))⟦(2 : ℤ)⟧)
        (θ : ∀ {n m : RamifiedRootIndex p} (a : n ⟶ m),
          (upperStar (ModuleCat.{u + 1} A) (T.diagram.map a.op)).mapDerivedCategory.obj
            (support A (T.open n)) ⟶ support A (T.open m))
        (β : ∀ n : RamifiedRootIndex p,
          (upperStar (ModuleCat.{u + 1} A) (T.cone.π.app (op n))).mapDerivedCategory.obj
            (support A (T.open n)) ⟶ support A T.limitInclusion)
        (δ : ∀ n, openTarget A (T.open n) ⟶ (support A (T.open n))⟦(1 : ℤ)⟧)
        (δlim : openTarget A T.limitInclusion ⟶
          (support A T.limitInclusion)⟦(1 : ℤ)⟧),
        (∀ n, KummerNormalized A N hN hA (T.closed n)
          (hI n) (hX n) (hD n) (support A (T.open n)) (inclusion A (T.open n)) (P n)) ∧
        (∀ n, IsFibreTriangle A (T.open n) (δ n)) ∧
        IsFibreTriangle A T.limitInclusion δlim ∧
        (∀ {n m : RamifiedRootIndex p} (a : n ⟶ m),
          SupportExchange A (T.open n) (T.open m) (T.diagram.map a.op) (θ a) ∧
          (∀ θ', SupportExchange A (T.open n) (T.open m) (T.diagram.map a.op) θ' →
            θ' = θ a) ∧
          (upperStar (ModuleCat.{u + 1} A) (T.diagram.map a.op)).mapDerivedCategory.map
              (δ n) ≫
            ((upperStar (ModuleCat.{u + 1} A)
              (T.diagram.map a.op)).mapDerivedCategory.commShiftIso (1 : ℤ)).hom.app _ ≫
            (θ a)⟦(1 : ℤ)⟧' =
          openExchange A (CommSq.mk (O.square a)) ≫ δ m) ∧
        (∀ n : RamifiedRootIndex p,
          SupportExchange A (T.open n) T.limitInclusion (T.cone.π.app (op n)) (β n) ∧
          (∀ β', SupportExchange A (T.open n) T.limitInclusion
            (T.cone.π.app (op n)) β' → β' = β n) ∧
          (upperStar (ModuleCat.{u + 1} A) (T.cone.π.app (op n))).mapDerivedCategory.map
              (δ n) ≫
            ((upperStar (ModuleCat.{u + 1} A)
              (T.cone.π.app (op n))).mapDerivedCategory.commShiftIso (1 : ℤ)).hom.app _ ≫
            (β n)⟦(1 : ℤ)⟧' =
          openExchange A (CommSq.mk (O.leg_square n)) ≫ δlim) ∧
        TransitionFormula A T N hN hA hD P θ ∧
        (∀ (n : RamifiedRootIndex p) (q : ℤ), q ≠ 2 →
          IsZero ((DerivedCategory.homologyFunctor _ q).obj (support A (T.open n)))) ∧
        (∀ {n m : RamifiedRootIndex p} (a : n ⟶ m), m.val = n.val * N →
          cohomologyExchange A (T.open n) (T.open m) (T.diagram.map a.op) (θ a) 2 = 0) ∧
        (∀ q : ℤ,
          ∃ (F : RamifiedRootIndex p ⥤
              Sheaf T.cone.pt.smallEtaleTopology (ModuleCat.{u + 1} A))
            (E : ∀ n, F.obj n ≅
              (upperStar (ModuleCat.{u + 1} A) (T.cone.π.app (op n))).obj
                ((DerivedCategory.homologyFunctor _ q).obj (support A (T.open n))))
            (c : F ⟶ (Functor.const (RamifiedRootIndex p)).obj
              ((DerivedCategory.homologyFunctor _ q).obj (support A T.limitInclusion))),
            (∀ {n m : RamifiedRootIndex p} (a : n ⟶ m),
              F.map a ≫ (E m).hom = (E n).hom ≫ limitTransition A T a (θ a) q) ∧
            (∀ n, c.app n = (E n).hom ≫ cohomologyExchange A (T.open n)
              T.limitInclusion (T.cone.π.app (op n)) (β n) q) ∧
            IsIso (colimit.desc F (Cocone.mk _ c)) ∧ IsZero (colimit F) ∧
            IsZero ((DerivedCategory.homologyFunctor _ q).obj
              (support A T.limitInclusion))) ∧
        IsIso (unit A T.limitInclusion) ∧ IsIso (proetaleUnit A T.limitInclusion) ∧
        IsIso ((siteMate A T.limitInclusion).app
          ((upperStar (ModuleCat.{u + 1} A) T.limitInclusion).mapDerivedCategory.obj
            (ordinaryFiniteUnit A T.cone.pt))) ∧
        (∀ L : DerivedCategoryModule A T.cone.pt,
          (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A)
            T.cone.pt).mapDerivedCategory.map
              ((mapDerivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A)
                T.limitInclusion).unit.app L) ≫
            (siteMate A T.limitInclusion).app
              ((upperStar (ModuleCat.{u + 1} A) T.limitInclusion).mapDerivedCategory.obj L) =
          (ProEtale.derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A)
            T.limitInclusion).unit.app
              ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A)
                T.cone.pt).mapDerivedCategory.obj L) ≫
            (ProEtale.lowerStar (ModuleCat.{u + 1} A)
              T.limitInclusion).rightDerivedFunctor.map
                ((sitePullback A T.limitInclusion).hom.app L))

/-- Finite torsion puncture invariance on the full prime-to-p ramified root tower.
The purity isomorphisms are normalized by the existing supported relative Kummer
boundary. All exchanges are characterized by the support inclusion AND the full
unit triangle, using the adjunction mate for the open square. The limit comparison
is the colimit descent of those same legs. All categories are ordinary uncompleted
categories of modules over the discrete finite coefficient ring.

Source: Stacks 0EYM, lemma-relative-colimit-general; ILO XVI 2.1 and 3.1.1;
blueprint main-20261015, discrete direct-image comparison.
(blueprint: lem-sfb-ramified-root-limit-torsion-unit).

Proof:
1. Divisibility is directed by multiplication. Parameter power identities identify
all inverse-image principal opens, so the open squares are Cartesian. Localization
of affine ring colimits identifies their inverse limit with X[1/f_1].
2. Apply lem-sfb-ramified-cartier-supported-purity at every pair of stages. It gives
the supported Kummer-normalized derived purity isomorphisms and the multiplicity
formula with reduction from V(f_m^e), including the e=1 normalization.
3. Exact inverse image commutes with homology. Transition to n ell^s multiplies by
the zero scalar ell^s. Every colimit leg is therefore zero by its cocone relation;
the universal property shows the colimit is the zero sheaf.
4. The fibre long exact sequence identifies R^r j_* A with H^(r+1)K for r≥1.
Its connecting maps commute with the actual open exchanges. Higher direct images
vanish for r≥2, and the degree-one transition is eventually zero.
5. Apply lem-kun-0eym to the qcqs principal opens, with affine transitions. The
constant-coefficient diagram is constant and the continuity legs are the actual
mates. Forget-coefficients compatibility gives the module statement. The limit
unit is an isomorphism in every degree; its fibre is acyclic and hence zero.
6. The discrete site comparison for qcqs j and bounded-below A[0] is an isomorphism.
Its adjunction-unit compatibility carries the etale unit to the pro-etale unit.
Empty schemes, empty divisors and identity transitions satisfy the same argument.
-/
theorem ramifiedRootLimitTorsionUnit (p ℓ : ℕ) (hp : p.Prime) (hℓ : ℓ.Prime)
    (hne : p ≠ ℓ) (T : RamifiedRootTower.{u} p ℓ) (s : ℕ) (hs : 1 ≤ s) :
    RootLimitAssertion (Coeff.{u} ℓ s) T (ℓ ^ s) (pow_pos hℓ.pos s)
      (congrArg (ULift.up : ZMod (ℓ ^ s) → Coeff.{u} ℓ s)
        (ZMod.natCast_self (ℓ ^ s))) := by
  sorry

end AlgebraicGeometry.Etale.RamifiedRoot
