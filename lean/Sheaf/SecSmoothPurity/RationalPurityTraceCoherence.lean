/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NE
-/
module

public import Sheaf.Paper.RationalSmoothPurityCanonical
public import Sheaf.Paper.FieldShriekCompositionQcqs
public import Sheaf.Paper.FieldWeilShriekShiftData
public import Sheaf.SixFunctors.IntegralOperationShiftData
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import Sheaf.Paper.PurityCompositionCoherence
import Sheaf.Paper.FiniteSmoothPullbackExchange

/-! # Trace and geometric coherence of rational smooth purity

Source: main-20261015, sec-smooth-purity/sk-thm-purity-transport,
prop-pur-rational-purity-trace-coherence (blueprint: prop-pur-rational-purity-trace-coherence).

The geometric source comparisons use root-normalized line maps, completed tensor,
and the actual pullback compositors. Exceptional composition is the counit mate
of compact-support composition. The rational and common-stage purity maps are the
published trace-normalized constructions.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme
open WeilConjectures

attribute [local irreducible] AlgebraicGeometry.Scheme.residueField

namespace WeilConjectures.RationalPurityCoherence
open FrobeniusCoefficientTwists RationalSmoothPurityCanonical

section Lines
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- The cartesian root-line map at any morphism, fixed on local scalar/root tensors.
Source: proof Step 4, geometric source comparisons
(blueprint: prop-pur-rational-purity-trace-coherence).
Proof: pull back the Kummer root tower, extend coefficients using the specified
coefficient map, and take tensor powers. At zero use the coefficient unit. The
root line is locally free of rank one and its root projections are cartesian,
so these maps are invertible. Local pure tensors determine the maps uniquely. -/
theorem linePull_existsUnique {X Y : Scheme.{u}} (f : X ⟶ Y)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)] :
    ∃! τ : ∀ d : ℕ, (modulePull l E f).obj (positiveLine l E Y d) ≅
        positiveLine l E X d,
      ∀ (d : ℕ) (V : Y.ProEt)
        (a : (completedIntegralCoefficientSheafUnrestricted l E Y).obj.obj (op V))
        (x : Fin d → (purTwistZlOne Y l).obj.obj (op V)),
        (τ d).hom.val.app (op ((proEtaleBaseChange f).obj V))
            (moduleSection l E f (positiveLine l E Y d) V
              (generator l E Y (op V) a d x)) =
          generator l E X (op ((proEtaleBaseChange f).obj V))
            ((sfCompletedCoefficientMap l E f).hom.app (op V) a)
            d (fun i ↦ rootSection l f V (x i)) := by
  sorry

/-- The uniquely root-normalized nonnegative line pullback.
Source: proof Step 4 (blueprint: prop-pur-rational-purity-trace-coherence). -/
@[irreducible]
def linePull {X Y : Scheme.{u}} (f : X ⟶ Y)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)] (d : ℕ) :=
  (linePull_existsUnique l E f).exists.choose d

/-- Concatenation of root powers, including the coefficient unit at either zero.
Source: proof Step 4, tensor and shift associators
(blueprint: prop-pur-rational-purity-trace-coherence).
Proof: concatenate local pure root tensors. Balanced tensor relations make this
linear, and sheafification gives the indicated map. Reassociate and split the
ordered powers for its inverse. The two local tensor formulas are inverse;
local pure tensors generate, proving uniqueness as well as the inverse equations. -/
theorem lineAdd_existsUnique (T : Scheme.{u}) (d e : ℕ) :
    ∃! a : positiveLine l E T (d + e) ≅
        ((proEtaleOrdinaryTensor T
          (completedIntegralCommRingSheafUnrestricted l E T)).obj
            (positiveLine l E T d)).obj (positiveLine l E T e),
      ∀ (U : T.ProEtᵒᵖ)
        (b : (completedIntegralCoefficientSheafUnrestricted l E T).obj.obj U)
        (x : Fin (d + e) → (purTwistZlOne T l).obj.obj U),
        a.hom.val.app U (generator l E T U b (d + e) x) =
          proEtaleTensorPair T
            (completedIntegralCommRingSheafUnrestricted l E T)
            (positiveLine l E T d) (positiveLine l E T e) U
            (generator l E T U b d (fun i ↦ x (Fin.castAdd e i)))
            (generator l E T U 1 e (fun i ↦ x (Fin.natAdd d i))) := by
  sorry

/-- The actual concatenation map, selected from its uniquely determining formula.
Source: proof Step 4 (blueprint: prop-pur-rational-purity-trace-coherence). -/
@[irreducible]
def lineAdd (T : Scheme.{u}) (d e : ℕ) :=
  (lineAdd_existsUnique l E T d e).exists.choose

/-- Rank-one root lines are flat-term K-flat representatives.
Source: proof Step 1, uniform finite-Tor domain
(blueprint: prop-pur-rational-purity-trace-coherence).
Proof: trivialize the root line on a pro-etale cover. Each power is the coefficient
unit there, hence flat. A degree-zero flat complex is K-flat; these are exactly
the two clauses of integralOperationsGoodComplex. -/
theorem lineSingle_good (T : Scheme.{u})
    [∀ x : T, Invertible (l : T.residueField x)] (d : ℕ) :
    integralOperationsGoodComplex l E T
      ((CochainComplex.singleFunctor _ 0).obj (positiveLine l E T d)) := by
  sorry

/-- The same complete line has uniform finite-Tor amplitude [0,0].
Source: proof Step 1 (blueprint: prop-pur-rational-purity-trace-coherence).
Proof: the compatible Kummer tower recovers the complete line. Every quotient
is locally a free rank-one coefficient module, in degree zero; therefore the
constructibility, completeness and uniform finite-Tor clauses all hold. -/
theorem lineSingle_finiteTor (T : Scheme.{u})
    [∀ x : T, Invertible (l : T.residueField x)] (d : ℕ) :
    finiteTorConstructibleIntegral l E T
      (DerivedCategory.Q.obj
        ((CochainComplex.singleFunctor _ 0).obj (positiveLine l E T d))) := by
  sorry

/-- Pullback of a complete rank-one root line has the specified complete augmentation.
Source: proof Step 4, arbitrary geometric base change
(blueprint: prop-pur-rational-purity-trace-coherence).
Proof: linePull identifies ordinary inverse image with the target complete line.
Under that identification the strict quotient augmentation is the completeness
unit, whose product projections and second cone component are prescribed. Thus
its localization is invertible, for arbitrary f, without smoothness of f. -/
theorem linePullAugmentation_isIso {X Y : Scheme.{u}} (f : X ⟶ Y)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)] (d : ℕ) :
    IsIso (DerivedCategory.Q.map ((pullbackAugmentation l E f).app
      ((CochainComplex.singleFunctor _ 0).obj (positiveLine l E Y d)))) := by
  sorry

/-- Integral line pullback from the fixed strict augmentation and local root map.
Source: proof Step 4 (blueprint: prop-pur-rational-purity-trace-coherence). -/
@[irreducible]
def integralLinePull {X Y : Scheme.{u}} (f : X ⟶ Y)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)] (d : ℕ) :
    (integralDerivedPullback l E f).obj (sfIntegralTwistingObject l E Y (d : ℤ)) ≅
      sfIntegralTwistingObject l E X (d : ℤ) :=
  (integralDerivedPullback l E f).mapIso
      ((DerivedCategory.singleFunctorIsoCompQ _ 0).app (positiveLine l E Y d)) ≪≫
    (integralDerivedPullbackComparison l E f).app
      ⟨_, lineSingle_good l E Y d⟩ ≪≫
    (@asIso _ _ _ _ (DerivedCategory.Q.map ((pullbackAugmentation l E f).app
      ((CochainComplex.singleFunctor _ 0).obj (positiveLine l E Y d))))
        (linePullAugmentation_isIso l E f d)).symm ≪≫
    ((modulePull l E f).mapDerivedCategoryFactors.app _).symm ≪≫
    ((modulePull l E f).mapDerivedCategorySingleFunctor 0).app (positiveLine l E Y d) ≪≫
    (DerivedCategory.singleFunctor _ 0).mapIso (linePull l E f d)

/-- Rationalization of the specified integral line pullback.
Source: proof Steps 2 and 4 (blueprint: prop-pur-rational-purity-trace-coherence). -/
@[irreducible]
def rationalLinePull {X Y : Scheme.{u}} (f : X ⟶ Y)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)] (d : ℕ) :
    (rationalDerivedPullback l E f).obj (sfRationalTwistingCoefficient l E Y (d : ℤ)) ≅
      sfRationalTwistingCoefficient l E X (d : ℤ) :=
  eqToIso ((rationalDerivedPullback_existsUnique l E f).exists.choose_spec.2.1 _) ≪≫
    (sfRationalConstructibleLocalization l E X).mapIso
      (ObjectProperty.isoMk _ (integralLinePull l E f d))

/-- The total tensor of degree-zero lines is the degree-zero ordinary tensor.
Source: proof Step 4 (blueprint: prop-pur-rational-purity-trace-coherence). -/
@[irreducible]
def lineSingleTensor (T : Scheme.{u}) (d e : ℕ) :
    (ordinaryTotal l E T).obj
      ((CochainComplex.singleFunctor _ 0).obj (positiveLine l E T d),
        (CochainComplex.singleFunctor _ 0).obj (positiveLine l E T e)) ≅
      (CochainComplex.singleFunctor _ 0).obj
        (((proEtaleOrdinaryTensor T
          (completedIntegralCommRingSheafUnrestricted l E T)).obj
            (positiveLine l E T d)).obj (positiveLine l E T e)) :=
  (CochainComplex.map₂HomologicalComplexFlipObjSingleIso
    (proEtaleOrdinaryTensor T (completedIntegralCommRingSheafUnrestricted l E T))
      (positiveLine l E T e)).app
        ((CochainComplex.singleFunctor _ 0).obj (positiveLine l E T d)) ≪≫
    (HomologicalComplex.singleMapHomologicalComplex
      ((proEtaleOrdinaryTensor T
        (completedIntegralCommRingSheafUnrestricted l E T)).flip.obj (positiveLine l E T e))
        (.up ℤ) 0).app (positiveLine l E T d)

/-- Concatenation in the completed derived tensor, through the fixed strict tensor unit.
Source: proof Step 4 (blueprint: prop-pur-rational-purity-trace-coherence). -/
@[irreducible]
def integralLineAdd (T : Scheme.{u})
    [∀ x : T, Invertible (l : T.residueField x)] (d e : ℕ) :
    sfIntegralTwistingObject l E T ((d + e : ℕ) : ℤ) ≅
      (integralCompletedTensor l E T).obj
        (sfIntegralTwistingObject l E T (d : ℤ), sfIntegralTwistingObject l E T (e : ℤ)) :=
  (DerivedCategory.singleFunctor _ 0).mapIso (lineAdd l E T d e) ≪≫
    (DerivedCategory.singleFunctorIsoCompQ _ 0).app _ ≪≫
    DerivedCategory.Q.mapIso (lineSingleTensor l E T d e).symm ≪≫
    (@asIso _ _ _ _ (DerivedCategory.Q.map ((tensorAugmentation l E T).app
      ((CochainComplex.singleFunctor _ 0).obj (positiveLine l E T d),
        (CochainComplex.singleFunctor _ 0).obj (positiveLine l E T e))))
      (tensorAugmentation_isIso l E T _ _ (lineSingle_good l E T d)
        (lineSingle_good l E T e) (lineSingle_finiteTor l E T d)
        (lineSingle_finiteTor l E T e))) ≪≫
    ((integralCompletedTensorComparison l E T).app
      (⟨_, lineSingle_good l E T d⟩, ⟨_, lineSingle_good l E T e⟩)).symm ≪≫
    (integralCompletedTensor l E T).mapIso
      (Iso.prod ((DerivedCategory.singleFunctorIsoCompQ _ 0).app _).symm
        ((DerivedCategory.singleFunctorIsoCompQ _ 0).app _).symm)

/-- The standard arithmetic equality for the two even shifts.
Source: proof Step 4 (blueprint: prop-pur-rational-purity-trace-coherence).
Proof: cast addition from natural numbers to integers and distribute multiplication. -/
theorem evenShift_add (d e : ℕ) :
    2 * ((d + e : ℕ) : ℤ) = 2 * (d : ℤ) + 2 * (e : ℤ) := by
  sorry

/-- Reassociate the two completed tensor shifts, retaining their signed Roos maps.
Source: proof Step 4 (blueprint: prop-pur-rational-purity-trace-coherence). -/
@[irreducible]
def integralTensorBothShift (T : Scheme.{u})
    (M N : DerivedCategory (integralTowerModules l E T)) (r s : ℤ) :
    (integralCompletedTensor l E T).obj (M⟦r⟧, N⟦s⟧) ≅
      ((integralCompletedTensor l E T).obj (M,N))⟦r + s⟧ :=
  ((IntegralSystemRealization.tensorShifts l E).integralLeft T r).app (M,N⟦s⟧) ≪≫
    (shiftFunctor _ r).mapIso
      (((IntegralSystemRealization.tensorShifts l E).integralRight T s).app (M,N)) ≪≫
    (shiftFunctorAdd' _ s r (r + s) (Int.add_comm s r)).symm.app _

/-- The shifted integral line concatenation in the actual intrinsic category.
Source: proof Step 4 (blueprint: prop-pur-rational-purity-trace-coherence). -/
@[irreducible]
def integralShiftedLineAdd (T : Scheme.{u})
    [∀ x : T, Invertible (l : T.residueField x)] (d e : ℕ) :
    (sfIntegralTwistingCoefficient l E T ((d + e : ℕ) : ℤ))⟦2*((d+e : ℕ) : ℤ)⟧ ≅
      (constructibleIntegralTensor l E T).obj
        ((sfIntegralTwistingCoefficient l E T (d : ℤ))⟦2*(d : ℤ)⟧,
          (sfIntegralTwistingCoefficient l E T (e : ℤ))⟦2*(e : ℤ)⟧) :=
  (sfIntegralConstructible l E T).isoMk
    ((((sfIntegralConstructible l E T).ι.commShiftIso (2*((d+e : ℕ) : ℤ))).app _) ≪≫
      (shiftFunctor _ (2*((d+e : ℕ) : ℤ))).mapIso (integralLineAdd l E T d e) ≪≫
      (eqToIso (congrArg (fun n : ℤ ↦
        ((integralCompletedTensor l E T).obj
          (sfIntegralTwistingObject l E T (d : ℤ),
            sfIntegralTwistingObject l E T (e : ℤ)))⟦n⟧)
              (evenShift_add d e))) ≪≫
      (integralTensorBothShift l E T _ _ (2*(d : ℤ)) (2*(e : ℤ))).symm ≪≫
      (integralCompletedTensor l E T).mapIso
        (Iso.prod (((sfIntegralConstructible l E T).ι.commShiftIso (2*(d : ℤ))).app
          (sfIntegralTwistingCoefficient l E T (d : ℤ))).symm
          (((sfIntegralConstructible l E T).ι.commShiftIso (2*(e : ℤ))).app
            (sfIntegralTwistingCoefficient l E T (e : ℤ))).symm))

/-- Even-shifted line concatenation after actual scalar localization.
Source: proof Steps 2 and 4 (blueprint: prop-pur-rational-purity-trace-coherence). -/
@[irreducible]
def rationalShiftedLineAdd (T : Scheme.{u})
    [∀ x : T, Invertible (l : T.residueField x)] (d e : ℕ) :
    (sfRationalTwistingCoefficient l E T ((d + e : ℕ) : ℤ))⟦2*((d+e : ℕ) : ℤ)⟧ ≅
      (rationalDerivedTensor l E T).obj
        ((sfRationalTwistingCoefficient l E T (d : ℤ))⟦2*(d : ℤ)⟧,
          (sfRationalTwistingCoefficient l E T (e : ℤ))⟦2*(e : ℤ)⟧) :=
  ((sfRationalConstructibleLocalization l E T).commShiftIso
      (2*((d+e : ℕ) : ℤ))).symm.app _ ≪≫
    (sfRationalConstructibleLocalization l E T).mapIso (integralShiftedLineAdd l E T d e) ≪≫
    (eqToIso ((rationalDerivedTensor_existsUnique l E T).exists.choose_spec.1
      ((sfRationalConstructibleLocalization l E T).obj
          ((sfIntegralTwistingCoefficient l E T (d : ℤ))⟦2*(d : ℤ)⟧),
        (sfRationalConstructibleLocalization l E T).obj
          ((sfIntegralTwistingCoefficient l E T (e : ℤ))⟦2*(e : ℤ)⟧)))).symm ≪≫
    (rationalDerivedTensor l E T).mapIso
      (Iso.prod (((sfRationalConstructibleLocalization l E T).commShiftIso
        (2*(d : ℤ))).app _) (((sfRationalConstructibleLocalization l E T).commShiftIso
          (2*(e : ℤ))).app _))

/-- Pullback of the shifted line, using the normalized pullback shift comparison.
Source: proof Step 4 (blueprint: prop-pur-rational-purity-trace-coherence). -/
@[irreducible]
def rationalShiftedLinePull {X Y : Scheme.{u}} (f : X ⟶ Y)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)] (d : ℕ) :
    (rationalDerivedPullback l E f).obj
        ((sfRationalTwistingCoefficient l E Y (d : ℤ))⟦2*(d : ℤ)⟧) ≅
      (sfRationalTwistingCoefficient l E X (d : ℤ))⟦2*(d : ℤ)⟧ :=
  ((rationalDerivedPullback l E f).commShiftIso (2*(d : ℤ))).app _ ≪≫
    (shiftFunctor _ (2*(d : ℤ))).mapIso (rationalLinePull l E f d)

/-- The geometric source compositor, assembled from root concatenation, tensor
associativity, pullback composition and the normalized cartesian line comparison.
Source: proof Step 4 (blueprint: prop-pur-rational-purity-trace-coherence). -/
@[irreducible]
def rationalSourceComposition {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    [∀ z : Z, Invertible (l : Z.residueField z)] (d e : ℕ)
    (K : sfRationalConstructibleCategory l E Z) :
    (rationalSource l E (f ≫ g) (d + e)).obj K ≅
      (rationalSource l E f d).obj ((rationalSource l E g e).obj K) :=
  (rationalDerivedTensor l E X).mapIso
      (Iso.prod (rationalShiftedLineAdd l E X d e)
        ((fieldRationalPullComp l E f g).app K)) ≪≫
    pullbackTensorRationalAssociator l E X _ _ _ ≪≫
    (rationalDerivedTensor l E X).mapIso
      (Iso.prod (Iso.refl _)
        ((rationalDerivedTensor l E X).mapIso
          (Iso.prod (rationalShiftedLinePull l E f e).symm (Iso.refl _)) ≪≫
          (canonicalRationalPullbackTensor l E f
            ((sfRationalTwistingCoefficient l E Y (e : ℤ))⟦2*(e : ℤ)⟧)
              ((rationalDerivedPullback l E g).obj K)).symm))

/-- Pullback around the given Cartesian square, from the two actual compositors.
Source: proof Step 4 (blueprint: prop-pur-rational-purity-trace-coherence). -/
@[irreducible]
def rationalSquarePull {X' X Y' Y : Scheme.{u}}
    (a : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (b : Y' ⟶ Y)
    [∀ x : X', Invertible (l : X'.residueField x)]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y', Invertible (l : Y'.residueField y)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (sq : IsPullback a f' f b) :
    rationalDerivedPullback l E f ⋙ rationalDerivedPullback l E a ≅
      rationalDerivedPullback l E b ⋙ rationalDerivedPullback l E f' :=
  (fieldRationalPullComp l E a f).symm ≪≫
    eqToIso (congrArg (fun h : X' ⟶ Y ↦ rationalDerivedPullback l E h) sq.w) ≪≫
    fieldRationalPullComp l E f' b

/-- The source base-change isomorphism for any Cartesian square. It uses no purity
map and imposes no smoothness on the horizontal base-change morphism.
Source: proof Step 4 (blueprint: prop-pur-rational-purity-trace-coherence). -/
@[irreducible]
def rationalSourceBaseChange {X' X Y' Y : Scheme.{u}}
    (a : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (b : Y' ⟶ Y)
    [∀ x : X', Invertible (l : X'.residueField x)]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y', Invertible (l : Y'.residueField y)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (sq : IsPullback a f' f b) (d : ℕ)
    (K : sfRationalConstructibleCategory l E Y) :
    (rationalDerivedPullback l E a).obj ((rationalSource l E f d).obj K) ≅
      (rationalSource l E f' d).obj ((rationalDerivedPullback l E b).obj K) :=
  canonicalRationalPullbackTensor l E a _ _ ≪≫
    (rationalDerivedTensor l E X').mapIso
      (Iso.prod (rationalShiftedLinePull l E a d)
        ((rationalSquarePull l E a f' f b sq).app K))

end Lines

section Composition
open ConstructibleExceptionalCoefficients
variable (P : PurityFiniteSetting.{u})
  {X Y Z : Scheme.{u}}
  [X.Over (Spec (.of P.field.k))] [Y.Over (Spec (.of P.field.k))]
  [Z.Over (Spec (.of P.field.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
  [QuasiCompact (X ↘ Spec (.of P.field.k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
  [QuasiCompact (Y ↘ Spec (.of P.field.k))]
  [LocallyOfFiniteType (Z ↘ Spec (.of P.field.k))]
  [QuasiCompact (Z ↘ Spec (.of P.field.k))]
  (f : X ⟶ Y) (g : Y ⟶ Z)
  [f.IsOver (Spec (.of P.field.k))] [g.IsOver (Spec (.of P.field.k))]
  [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
  [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
  (cf : Compactification f) (cg : Compactification g) (cfg : Compactification (f ≫ g))
  (Sf : System P.coefficients.l P.coefficients.Qbar P.field P.coefficients.different (f := f))
  (Sg : System P.coefficients.l P.coefficients.Qbar P.field P.coefficients.different (f := g))
  (Sfg : System P.coefficients.l P.coefficients.Qbar P.field
    P.coefficients.different (f := f ≫ g))

/-- Compact-support composition in the same adjunction coordinates as purity.
Source: proof Step 4, canonical c_g,f
(blueprint: prop-pur-rational-purity-trace-coherence). -/
@[irreducible]
def rationalSupportComposition (s : FieldStage.{u} P.coefficients.l) :
    (Sf.ring.operation cf (.rational s)).F ⋙ (Sg.ring.operation cg (.rational s)).F ≅
      (Sfg.ring.operation cfg (.rational s)).F :=
  Functor.isoWhiskerRight (Sf.ring.rationalLeft cf s) _ ≪≫
    Functor.isoWhiskerLeft _ (Sg.ring.rationalLeft cg s) ≪≫
    sfFieldShriekCompositionRational P.field P.coefficients.l P.coefficients.different
      cf cg cfg s.carrier ≪≫ (Sfg.ring.rationalLeft cfg s).symm

/-- The canonical exceptional compositor c_g,f, namely the counit mate of the actual
proper/open compact-support compositor. It is defined independently of gamma.
Source: proof Step 4 (blueprint: prop-pur-rational-purity-trace-coherence). -/
@[irreducible]
def rationalExceptionalComposition (s : FieldStage.{u} P.coefficients.l) :
    (Sfg.ring.operation cfg (.rational s)).G ≅
      (Sg.ring.operation cg (.rational s)).G ⋙ (Sf.ring.operation cf (.rational s)).G :=
  conjugateIsoEquiv (Sfg.ring.operation cfg (.rational s)).adjunction
    ((Sf.ring.operation cf (.rational s)).adjunction.comp
      (Sg.ring.operation cg (.rational s)).adjunction)
    (rationalSupportComposition P f g cf cg cfg Sf Sg Sfg s)

end Composition

section CommonSources
open AlgebraicallyClosedCoefficients GeneralAlgebraicallyClosedCoefficients
variable (l : ℕ) [Fact l.Prime]
  (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]

/-- Pullback at a literal finite stage, from its published object formula.
Source: proof Step 6 (blueprint: prop-pur-rational-purity-trace-coherence). -/
@[irreducible]
def commonPullInclusion {X Y : Scheme.{u}} (f : X ⟶ Y)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (i : Index l Ω) (K : Stage l Ω Y i) :
    (commonStageDerivedPullback l Ω f).obj ⟨i,K⟩ ≅
      (GeneralAlgebraicallyClosedCoefficients.inclusion i).obj
        ((rationalDerivedPullback l (Coefficient.{u} l Ω i) f).obj K) :=
  eqToIso ((commonStageDerivedPullback_existsUnique l Ω f).exists.choose_spec.1 _)

/-- The geometric source compositor at Qbar, represented by the rational compositor
at the input's own finite field and the prescribed source comparisons.
Source: proof Step 6 (blueprint: prop-pur-rational-purity-trace-coherence). -/
@[irreducible]
def commonSourceComposition {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    [∀ z : Z, Invertible (l : Z.residueField z)] (d e : ℕ)
    (K : generalAlgebraicallyClosedConstructibleCategory l Ω Z) :
    (commonSource l Ω (f ≫ g) (d + e)).obj K ≅
      (commonSource l Ω f d).obj ((commonSource l Ω g e).obj K) :=
  commonSourceComparison l Ω (f ≫ g) (d + e) K ≪≫
    (GeneralAlgebraicallyClosedCoefficients.inclusion K.stage).mapIso
      (rationalSourceComposition l (Coefficient.{u} l Ω K.stage) f g d e K.obj) ≪≫
    (commonSourceComparison l Ω f d
      ⟨K.stage,(rationalSource l (Coefficient.{u} l Ω K.stage) g e).obj K.obj⟩).symm ≪≫
    (commonSource l Ω f d).mapIso (commonSourceComparison l Ω g e K).symm

/-- The source comparison around an arbitrary Cartesian square at Qbar, represented
by the rational root/tensor/pullback comparison and the actual stage inclusions.
Source: proof Step 6 (blueprint: prop-pur-rational-purity-trace-coherence). -/
@[irreducible]
def commonSourceBaseChange {X' X Y' Y : Scheme.{u}}
    (a : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (b : Y' ⟶ Y)
    [∀ x : X', Invertible (l : X'.residueField x)]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y', Invertible (l : Y'.residueField y)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (sq : IsPullback a f' f b) (d : ℕ)
    (K : generalAlgebraicallyClosedConstructibleCategory l Ω Y) :
    (commonStageDerivedPullback l Ω a).obj ((commonSource l Ω f d).obj K) ≅
      (commonSource l Ω f' d).obj ((commonStageDerivedPullback l Ω b).obj K) :=
  (commonStageDerivedPullback l Ω a).mapIso (commonSourceComparison l Ω f d K) ≪≫
    commonPullInclusion l Ω a K.stage _ ≪≫
    (GeneralAlgebraicallyClosedCoefficients.inclusion K.stage).mapIso
      (rationalSourceBaseChange l (Coefficient.{u} l Ω K.stage) a f' f b sq d K.obj) ≪≫
    (commonSourceComparison l Ω f' d
      ⟨K.stage,(rationalDerivedPullback l (Coefficient.{u} l Ω K.stage) b).obj K.obj⟩).symm ≪≫
    (commonSource l Ω f' d).mapIso (commonPullInclusion l Ω b K.stage K.obj).symm

end CommonSources

section GeometricComposition
open ConstructibleExceptionalCoefficients
open AlgebraicallyClosedCoefficients GeneralAlgebraicallyClosedCoefficients
variable (P : PurityFiniteSetting.{u}) {X Y Z : Scheme.{u}}
  [X.Over (Spec (.of P.field.k))] [Y.Over (Spec (.of P.field.k))]
  [Z.Over (Spec (.of P.field.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
  [QuasiCompact (X ↘ Spec (.of P.field.k))]
  [IsSeparated (X ↘ Spec (.of P.field.k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
  [QuasiCompact (Y ↘ Spec (.of P.field.k))]
  [IsSeparated (Y ↘ Spec (.of P.field.k))]
  [LocallyOfFiniteType (Z ↘ Spec (.of P.field.k))]
  [QuasiCompact (Z ↘ Spec (.of P.field.k))]
  [IsSeparated (Z ↘ Spec (.of P.field.k))]
  [∀ x : X, Invertible (P.coefficients.l : X.residueField x)]
  [∀ y : Y, Invertible (P.coefficients.l : Y.residueField y)]
  [∀ z : Z, Invertible (P.coefficients.l : Z.residueField z)]
  (f : X ⟶ Y) (g : Y ⟶ Z)
  [f.IsOver (Spec (.of P.field.k))] [g.IsOver (Spec (.of P.field.k))]
  [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
  [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
  (cf : Compactification f) (cg : Compactification g) (cfg : Compactification (f ≫ g))
  (Sf : System P.coefficients.l P.coefficients.Qbar P.field P.coefficients.different (f := f))
  (Sg : System P.coefficients.l P.coefficients.Qbar P.field P.coefficients.different (f := g))
  (Sfg : System P.coefficients.l P.coefficients.Qbar P.field
    P.coefficients.different (f := f ≫ g))

/-- The common-stage support compositor is uniquely fixed by the rational compositor
and the counit-normalized inclusion comparisons. This does not use purity.
Source: proof Steps 4--6 (blueprint: prop-pur-rational-purity-trace-coherence).
Proof: at (i,K), conjugate the inclusion of the rational support compositor by
q_f, q_g and q_gf. Their scalar cocycles and the proper/open coefficient comparison
identify these maps after every enlargement. Every common-stage arrow has a finite
representative, so rational naturality gives naturality. Descend the inverse formula
as well. Every object is a literal pair, so the component formula gives uniqueness. -/
theorem commonSupportComposition_existsUnique :
    ∃! c : (Sf.ring.operation cf .closed).F ⋙ (Sg.ring.operation cg .closed).F ≅
        (Sfg.ring.operation cfg .closed).F,
      ∀ (i : Index P.coefficients.l P.coefficients.Qbar)
        (K : Stage P.coefficients.l P.coefficients.Qbar X i),
        (c.hom.app ⟨i,K⟩) =
          (Sg.ring.operation cg .closed).F.map ((Sf.common.commonComparison cf i).q.inv.app K) ≫
          (Sg.common.commonComparison cg i).q.inv.app
            ((Sf.ring.operation cf (.rational
              (commonField P.coefficients.l P.coefficients.Qbar i))).F.obj K) ≫
          (GeneralAlgebraicallyClosedCoefficients.inclusion i).map
            ((rationalSupportComposition P f g cf cg cfg Sf Sg Sfg
              (commonField P.coefficients.l P.coefficients.Qbar i)).hom.app K) ≫
          (Sfg.common.commonComparison cfg i).q.hom.app K := by
  sorry

/-- The specified common-stage compact-support compositor.
Source: proof Step 6 (blueprint: prop-pur-rational-purity-trace-coherence). -/
@[irreducible]
def commonSupportComposition :=
  (commonSupportComposition_existsUnique P f g cf cg cfg Sf Sg Sfg).exists.choose

/-- The Qbar exceptional compositor is the adjunction mate of support composition.
Source: proof Steps 4--6 (blueprint: prop-pur-rational-purity-trace-coherence). -/
@[irreducible]
def commonExceptionalComposition :
    (Sfg.ring.operation cfg .closed).G ≅
      (Sg.ring.operation cg .closed).G ⋙ (Sf.ring.operation cf .closed).G :=
  conjugateIsoEquiv (Sfg.ring.operation cfg .closed).adjunction
    ((Sf.ring.operation cf .closed).adjunction.comp
      (Sg.ring.operation cg .closed).adjunction)
    (commonSupportComposition P f g cf cg cfg Sf Sg Sfg)

/-- The two geometric composition paths for the canonical rational purity maps.
Source: thm-pur-composition-coherence, rationalization
(blueprint: prop-pur-rational-purity-trace-coherence). -/
@[irreducible]
def RationalCompositionClause (d e : ℕ)
    [SmoothOfRelativeDimension d f] [SmoothOfRelativeDimension e g]
    [SmoothOfRelativeDimension (d + e) (f ≫ g)] : Prop :=
  ∀ K : sfRationalConstructibleCategory P.coefficients.l P.extension Z,
    (rationalIso P (f ≫ g) cfg Sfg (d + e) K).hom =
      (rationalSourceComposition P.coefficients.l P.extension f g d e K).hom ≫
      (rationalSource P.coefficients.l P.extension f d).map
        (rationalIso P g cg Sg e K).hom ≫
      (rationalIso P f cf Sf d
        ((Sg.ring.operation cg (.rational (AdicSmoothDualizing.fieldStage P))).G.obj K)).hom ≫
      (rationalExceptionalComposition P f g cf cg cfg Sf Sg Sfg
        (AdicSmoothDualizing.fieldStage P)).inv.app K

/-- Both composition paths in the actual common-stage category, with the counit mate
c_g,f and the root-normalized source compositor.
Source: thm-pur-composition-coherence, common-stage descent
(blueprint: prop-pur-rational-purity-trace-coherence). -/
@[irreducible]
def CommonCompositionClause (d e : ℕ)
    [SmoothOfRelativeDimension d f] [SmoothOfRelativeDimension e g]
    [SmoothOfRelativeDimension (d + e) (f ≫ g)] : Prop :=
  ∀ K : generalAlgebraicallyClosedConstructibleCategory
      P.coefficients.l P.coefficients.Qbar Z,
    (commonIso P (f ≫ g) cfg Sfg (d + e) K).hom =
      (commonSourceComposition P.coefficients.l P.coefficients.Qbar f g d e K).hom ≫
      (commonSource P.coefficients.l P.coefficients.Qbar f d).map
        (commonIso P g cg Sg e K).hom ≫
      (commonIso P f cf Sf d ((Sg.ring.operation cg .closed).G.obj K)).hom ≫
      (commonExceptionalComposition P f g cf cg cfg Sf Sg Sfg).inv.app K

end GeometricComposition

section Trace
open ConstructibleExceptionalCoefficients
open AlgebraicallyClosedCoefficients GeneralAlgebraicallyClosedCoefficients
variable (P : PurityFiniteSetting.{u}) {X Y : Scheme.{u}}
  [X.Over (Spec (.of P.field.k))] [Y.Over (Spec (.of P.field.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
  [QuasiCompact (X ↘ Spec (.of P.field.k))]
  [IsSeparated (X ↘ Spec (.of P.field.k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
  [QuasiCompact (Y ↘ Spec (.of P.field.k))]
  [IsSeparated (Y ↘ Spec (.of P.field.k))]
  [∀ x : X, Invertible (P.coefficients.l : X.residueField x)]
  [∀ y : Y, Invertible (P.coefficients.l : Y.residueField y)]
  (f : X ⟶ Y) [f.IsOver (Spec (.of P.field.k))]
  [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
  (c : Compactification f)
  (S : System P.coefficients.l P.coefficients.Qbar P.field P.coefficients.different (f := f))
  (d : ℕ) [SmoothOfRelativeDimension d f]

/-- The rational trace is the localization of the integral smooth trace, through
its actual source, support and representative comparisons. The integral trace is
already constructed from finite smooth trace and the projection formula.
Source: proof Steps 1--3 (blueprint: prop-pur-rational-purity-trace-coherence). -/
@[irreducible]
def localizedSmoothTrace
    (K : sfRationalConstructibleCategory P.coefficients.l P.extension Y) :=
  (operation P f c S (.rational (AdicSmoothDualizing.fieldStage P))).F.map
      (rationalSourceComparison P f d K).hom ≫
    (S.fields.rationalizationComparison c (AdicSmoothDualizing.fieldStage P)).q.inv.app
      (integralSource P f d (representative P K)) ≫
    (rationalization P.coefficients.l P.coefficients.Qbar
      (AdicSmoothDualizing.fieldStage P) Y).map
        (integralTraceTranspose P f c S d (representative P K)) ≫
    (eqToIso (representative_eq P K)).hom

/-- The rational smooth trace in the small finite-field coefficient model: the
model purity map followed by the counit of the same support adjunction, i.e. the
adjoint transpose of the purity map.
Source: proof Steps 3 and 6 (blueprint: prop-pur-rational-purity-trace-coherence). -/
@[irreducible]
def modelSmoothTrace
    (K : sfRationalConstructibleCategory P.coefficients.l
      (Coefficient.{u} P.coefficients.l P.coefficients.Qbar
        (AdicSmoothDualizing.fieldIndex P)) Y) :=
  ((S.ring.operation c (.rational
      (commonField P.coefficients.l P.coefficients.Qbar
        (AdicSmoothDualizing.fieldIndex P)))).adjunction.homEquiv _ _).symm
    (smallModelIso P f c S d K).hom

/-- The Qbar trace is the descended finite-stage trace: at a common-stage object of
finite stage i (written through the index of the stage setting, which is i itself),
the model trace at that literal finite field, included through the source comparison
and the support comparison q of that stage. It does not use the common-stage
exceptional functor, adjunction or purity map.
Source: proof Steps 3--6 (blueprint: prop-pur-rational-purity-trace-coherence). -/
@[irreducible]
def descendedSmoothTrace (i : Index P.coefficients.l P.coefficients.Qbar)
    (K : sfRationalConstructibleCategory P.coefficients.l
      (Coefficient.{u} P.coefficients.l P.coefficients.Qbar
        (AdicSmoothDualizing.fieldIndex (stageSetting P i))) Y) :=
  (operation P f c S .closed).F.map
      (commonSourceComparison P.coefficients.l P.coefficients.Qbar f d
        ⟨AdicSmoothDualizing.fieldIndex (stageSetting P i), K⟩).hom ≫
    (S.common.commonComparison c (AdicSmoothDualizing.fieldIndex (stageSetting P i))).q.inv.app
      ((rationalSource P.coefficients.l
        (Coefficient.{u} P.coefficients.l P.coefficients.Qbar
          (AdicSmoothDualizing.fieldIndex (stageSetting P i))) f d).obj K) ≫
    (GeneralAlgebraicallyClosedCoefficients.inclusion
        (AdicSmoothDualizing.fieldIndex (stageSetting P i))).map
      (modelSmoothTrace (stageSetting P i) f c S d K)

/-- Existential presentation of the canonical rational and Qbar purity data, together
with the counit trace equations. Equality to the published trace-normalized maps
pins every witness; arbitrary rescalings of gamma or of the adjunction are excluded.
Source: proof Steps 1--6 (blueprint: prop-pur-rational-purity-trace-coherence). -/
@[irreducible]
def TraceClause : Prop :=
  (∃ G : sfRationalConstructibleCategory P.coefficients.l P.extension Y ⥤
        sfRationalConstructibleCategory P.coefficients.l P.extension X,
    ∃ adj : (operation P f c S (.rational (AdicSmoothDualizing.fieldStage P))).F ⊣ G,
    ∃ γ : ∀ K : sfRationalConstructibleCategory P.coefficients.l P.extension Y,
        (rationalSource P.coefficients.l P.extension f d).obj K ≅ G.obj K,
      G = (operation P f c S (.rational (AdicSmoothDualizing.fieldStage P))).G ∧
      HEq adj (operation P f c S (.rational (AdicSmoothDualizing.fieldStage P))).adjunction ∧
      (∀ K, HEq (γ K) (rationalIso P f c S d K)) ∧
      ∀ K, (operation P f c S (.rational (AdicSmoothDualizing.fieldStage P))).F.map
          (γ K).hom ≫ adj.counit.app K = localizedSmoothTrace P f c S d K) ∧
  (∃ GQ : generalAlgebraicallyClosedConstructibleCategory
        P.coefficients.l P.coefficients.Qbar Y ⥤
        generalAlgebraicallyClosedConstructibleCategory
          P.coefficients.l P.coefficients.Qbar X,
    ∃ adjQ : (operation P f c S .closed).F ⊣ GQ,
    ∃ γQ : ∀ K : generalAlgebraicallyClosedConstructibleCategory
        P.coefficients.l P.coefficients.Qbar Y,
        (commonSource P.coefficients.l P.coefficients.Qbar f d).obj K ≅ GQ.obj K,
      GQ = (operation P f c S .closed).G ∧
      HEq adjQ (operation P f c S .closed).adjunction ∧
      (∀ K, HEq (γQ K) (commonIso P f c S d K)) ∧
      ∀ (i : Index P.coefficients.l P.coefficients.Qbar)
        (K : sfRationalConstructibleCategory P.coefficients.l
          (Coefficient.{u} P.coefficients.l P.coefficients.Qbar
            (AdicSmoothDualizing.fieldIndex (stageSetting P i))) Y),
        (operation P f c S .closed).F.map
            (γQ ⟨AdicSmoothDualizing.fieldIndex (stageSetting P i), K⟩).hom ≫
          adjQ.counit.app ⟨AdicSmoothDualizing.fieldIndex (stageSetting P i), K⟩ =
        descendedSmoothTrace P f c S d i K)

end Trace

section BaseChange
open ConstructibleExceptionalCoefficients
variable (P : PurityFiniteSetting.{u}) {X' X Y' Y : Scheme.{u}}
  [X'.Over (Spec (.of P.field.k))] [X.Over (Spec (.of P.field.k))]
  [Y'.Over (Spec (.of P.field.k))] [Y.Over (Spec (.of P.field.k))]
  [LocallyOfFiniteType (X' ↘ Spec (.of P.field.k))]
  [QuasiCompact (X' ↘ Spec (.of P.field.k))]
  [IsSeparated (X' ↘ Spec (.of P.field.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
  [QuasiCompact (X ↘ Spec (.of P.field.k))]
  [IsSeparated (X ↘ Spec (.of P.field.k))]
  [LocallyOfFiniteType (Y' ↘ Spec (.of P.field.k))]
  [QuasiCompact (Y' ↘ Spec (.of P.field.k))]
  [IsSeparated (Y' ↘ Spec (.of P.field.k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
  [QuasiCompact (Y ↘ Spec (.of P.field.k))]
  [IsSeparated (Y ↘ Spec (.of P.field.k))]
  [∀ x : X', Invertible (P.coefficients.l : X'.residueField x)]
  [∀ x : X, Invertible (P.coefficients.l : X.residueField x)]
  [∀ y : Y', Invertible (P.coefficients.l : Y'.residueField y)]
  [∀ y : Y, Invertible (P.coefficients.l : Y.residueField y)]
  (a : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (b : Y' ⟶ Y)
  [a.IsOver (Spec (.of P.field.k))] [f'.IsOver (Spec (.of P.field.k))]
  [f.IsOver (Spec (.of P.field.k))] [b.IsOver (Spec (.of P.field.k))]
  [IsSeparated f'] [LocallyOfFiniteType f'] [QuasiCompact f']
  [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
  (sq : IsPullback a f' f b) (c' : Compactification f') (c : Compactification f)
  (S' : System P.coefficients.l P.coefficients.Qbar P.field P.coefficients.different (f := f'))
  (S : System P.coefficients.l P.coefficients.Qbar P.field P.coefficients.different (f := f))
  (d : ℕ) [SmoothOfRelativeDimension d f'] [SmoothOfRelativeDimension d f]

/-- Rational smooth exchange: inverse pulled-back purity, the canonical source
comparison, then base-changed purity. This is precisely the defining smooth exchange
of def-pur-smooth-pullback-exchange, transported to rational coefficients.
Source: thm-pur-smooth-base-change-coherence
(blueprint: prop-pur-rational-purity-trace-coherence). -/
@[irreducible]
def rationalSmoothExchange
    (K : sfRationalConstructibleCategory P.coefficients.l P.extension Y) :
    (rationalDerivedPullback P.coefficients.l P.extension a).obj
        ((operation P f c S (.rational (AdicSmoothDualizing.fieldStage P))).G.obj K) ≅
      (operation P f' c' S' (.rational (AdicSmoothDualizing.fieldStage P))).G.obj
        ((rationalDerivedPullback P.coefficients.l P.extension b).obj K) :=
  (rationalDerivedPullback P.coefficients.l P.extension a).mapIso
      (rationalIso P f c S d K).symm ≪≫
    rationalSourceBaseChange P.coefficients.l P.extension a f' f b sq d K ≪≫
    rationalIso P f' c' S' d
      ((rationalDerivedPullback P.coefficients.l P.extension b).obj K)

/-- The same prescribed smooth exchange in the common-stage category.
Source: thm-pur-smooth-base-change-coherence and proof Step 6
(blueprint: prop-pur-rational-purity-trace-coherence). -/
@[irreducible]
def commonSmoothExchange
    (K : generalAlgebraicallyClosedConstructibleCategory
      P.coefficients.l P.coefficients.Qbar Y) :
    (commonStageDerivedPullback P.coefficients.l P.coefficients.Qbar a).obj
        ((operation P f c S .closed).G.obj K) ≅
      (operation P f' c' S' .closed).G.obj
        ((commonStageDerivedPullback P.coefficients.l P.coefficients.Qbar b).obj K) :=
  (commonStageDerivedPullback P.coefficients.l P.coefficients.Qbar a).mapIso
      (commonIso P f c S d K).symm ≪≫
    commonSourceBaseChange P.coefficients.l P.coefficients.Qbar a f' f b sq d K ≪≫
    commonIso P f' c' S' d
      ((commonStageDerivedPullback P.coefficients.l P.coefficients.Qbar b).obj K)

/-- The two paths around every Cartesian square commute, with no restriction on b.
Source: thm-pur-smooth-base-change-coherence, at both field coefficient stages
(blueprint: prop-pur-rational-purity-trace-coherence). -/
@[irreducible]
def BaseChangeClause : Prop :=
  (∀ K : sfRationalConstructibleCategory P.coefficients.l P.extension Y,
    (rationalDerivedPullback P.coefficients.l P.extension a).map
        (rationalIso P f c S d K).hom ≫
        (rationalSmoothExchange P a f' f b sq c' c S' S d K).hom =
      (rationalSourceBaseChange P.coefficients.l P.extension a f' f b sq d K).hom ≫
        (rationalIso P f' c' S' d
          ((rationalDerivedPullback P.coefficients.l P.extension b).obj K)).hom) ∧
  ∀ K : generalAlgebraicallyClosedConstructibleCategory
      P.coefficients.l P.coefficients.Qbar Y,
    (commonStageDerivedPullback P.coefficients.l P.coefficients.Qbar a).map
        (commonIso P f c S d K).hom ≫
        (commonSmoothExchange P a f' f b sq c' c S' S d K).hom =
      (commonSourceBaseChange P.coefficients.l P.coefficients.Qbar a f' f b sq d K).hom ≫
        (commonIso P f' c' S' d
          ((commonStageDerivedPullback P.coefficients.l P.coefficients.Qbar b).obj K)).hom

end BaseChange

open ConstructibleExceptionalCoefficients

/-- All source settings for CompositionCoherence, including zero dimension and every object.
Source: proof Steps 1--7 (blueprint: prop-pur-rational-purity-trace-coherence). -/
@[irreducible]
def CompositionCoherence (P : PurityFiniteSetting.{u}) : Prop :=
  ∀ {X Y Z : Scheme.{u}}
  [X.Over (Spec (.of P.field.k))] [Y.Over (Spec (.of P.field.k))]
  [Z.Over (Spec (.of P.field.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
  [QuasiCompact (X ↘ Spec (.of P.field.k))]
  [IsSeparated (X ↘ Spec (.of P.field.k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
  [QuasiCompact (Y ↘ Spec (.of P.field.k))]
  [IsSeparated (Y ↘ Spec (.of P.field.k))]
  [LocallyOfFiniteType (Z ↘ Spec (.of P.field.k))]
  [QuasiCompact (Z ↘ Spec (.of P.field.k))]
  [IsSeparated (Z ↘ Spec (.of P.field.k))]
  [∀ x : X, Invertible (P.coefficients.l : X.residueField x)]
  [∀ y : Y, Invertible (P.coefficients.l : Y.residueField y)]
  [∀ z : Z, Invertible (P.coefficients.l : Z.residueField z)]
  (f : X ⟶ Y) (g : Y ⟶ Z)
  [f.IsOver (Spec (.of P.field.k))] [g.IsOver (Spec (.of P.field.k))]
  [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
  [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
  (cf : Compactification f) (cg : Compactification g) (cfg : Compactification (f ≫ g))
  (Sf : System P.coefficients.l P.coefficients.Qbar P.field P.coefficients.different (f := f))
  (Sg : System P.coefficients.l P.coefficients.Qbar P.field P.coefficients.different (f := g))
  (Sfg : System P.coefficients.l P.coefficients.Qbar P.field
    P.coefficients.different (f := f ≫ g))
  (d e : ℕ) [SmoothOfRelativeDimension d f] [SmoothOfRelativeDimension e g]
  [SmoothOfRelativeDimension (d + e) (f ≫ g)],
  RationalCompositionClause P f g cf cg cfg Sf Sg Sfg d e ∧
    CommonCompositionClause P f g cf cg cfg Sf Sg Sfg d e

/-- All source settings for TraceCoherence, including zero dimension and every object.
Source: proof Steps 1--7 (blueprint: prop-pur-rational-purity-trace-coherence). -/
@[irreducible]
def TraceCoherence (P : PurityFiniteSetting.{u}) : Prop :=
  ∀ {X Y : Scheme.{u}}
  [X.Over (Spec (.of P.field.k))] [Y.Over (Spec (.of P.field.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
  [QuasiCompact (X ↘ Spec (.of P.field.k))]
  [IsSeparated (X ↘ Spec (.of P.field.k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
  [QuasiCompact (Y ↘ Spec (.of P.field.k))]
  [IsSeparated (Y ↘ Spec (.of P.field.k))]
  [∀ x : X, Invertible (P.coefficients.l : X.residueField x)]
  [∀ y : Y, Invertible (P.coefficients.l : Y.residueField y)]
  (f : X ⟶ Y) [f.IsOver (Spec (.of P.field.k))]
  [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
  (c : Compactification f)
  (S : System P.coefficients.l P.coefficients.Qbar P.field P.coefficients.different (f := f))
  (d : ℕ) [SmoothOfRelativeDimension d f],
  TraceClause P f c S d

/-- All source settings for BaseChangeCoherence, including zero dimension and every object.
Source: proof Steps 1--7 (blueprint: prop-pur-rational-purity-trace-coherence). -/
@[irreducible]
def BaseChangeCoherence (P : PurityFiniteSetting.{u}) : Prop :=
  ∀ {X' X Y' Y : Scheme.{u}}
  [X'.Over (Spec (.of P.field.k))] [X.Over (Spec (.of P.field.k))]
  [Y'.Over (Spec (.of P.field.k))] [Y.Over (Spec (.of P.field.k))]
  [LocallyOfFiniteType (X' ↘ Spec (.of P.field.k))]
  [QuasiCompact (X' ↘ Spec (.of P.field.k))]
  [IsSeparated (X' ↘ Spec (.of P.field.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
  [QuasiCompact (X ↘ Spec (.of P.field.k))]
  [IsSeparated (X ↘ Spec (.of P.field.k))]
  [LocallyOfFiniteType (Y' ↘ Spec (.of P.field.k))]
  [QuasiCompact (Y' ↘ Spec (.of P.field.k))]
  [IsSeparated (Y' ↘ Spec (.of P.field.k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
  [QuasiCompact (Y ↘ Spec (.of P.field.k))]
  [IsSeparated (Y ↘ Spec (.of P.field.k))]
  [∀ x : X', Invertible (P.coefficients.l : X'.residueField x)]
  [∀ x : X, Invertible (P.coefficients.l : X.residueField x)]
  [∀ y : Y', Invertible (P.coefficients.l : Y'.residueField y)]
  [∀ y : Y, Invertible (P.coefficients.l : Y.residueField y)]
  (a : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (b : Y' ⟶ Y)
  [a.IsOver (Spec (.of P.field.k))] [f'.IsOver (Spec (.of P.field.k))]
  [f.IsOver (Spec (.of P.field.k))] [b.IsOver (Spec (.of P.field.k))]
  [IsSeparated f'] [LocallyOfFiniteType f'] [QuasiCompact f']
  [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
  (sq : IsPullback a f' f b) (c' : Compactification f') (c : Compactification f)
  (S' : System P.coefficients.l P.coefficients.Qbar P.field P.coefficients.different (f := f'))
  (S : System P.coefficients.l P.coefficients.Qbar P.field P.coefficients.different (f := f))
  (d : ℕ) [SmoothOfRelativeDimension d f'] [SmoothOfRelativeDimension d f],
  BaseChangeClause P a f' f b sq c' c S' S d

/-- Trace, geometric composition and arbitrary Cartesian base-change coherence for
one canonical purity family. This package does not reassert existence of purity.
Source: main-20261015, prop-pur-rational-purity-trace-coherence
(blueprint: prop-pur-rational-purity-trace-coherence). -/
structure RationalPurityTraceCoherence (P : PurityFiniteSetting.{u}) : Prop where
  trace : TraceCoherence P
  composition : CompositionCoherence P
  baseChange : BaseChangeCoherence P

/-- The canonical rational and Qbar purity isomorphisms preserve smooth trace,
geometric composition, and arbitrary Cartesian base change.
Source: main-20261015, sec-smooth-purity/sk-thm-purity-transport,
prop-pur-rational-purity-trace-coherence, proof Steps 1--7
(blueprint: prop-pur-rational-purity-trace-coherence).
Proof: finite type over the field gives noetherian finite-dimensional schemes and
invertibility of l. Integral residue-Tor places each lattice in the uniform
finite-Tor domain. Apply the supplied integral reconstruction trace/coherence
diagrams, with the simultaneous scalar-compatible purity family. The canonical
unit orientation and its trace transpose identify this family with rationalIso.
Rational transport preserves functors, transformations, units, counits and their
equations. Hence the localized trace is F(gamma) followed by the same counit.
The exceptional geometric compositor is the adjunction mate of the proper/open
support compositor. Transport of the integral composition diagram therefore gives
RationalCompositionClause with this actual c_g,f. Smooth exchange is the specified
inverse-purity/source/purity composite; its inverse identity gives BaseChangeClause
for every Cartesian square, without any condition on the base-change map.
The scalar source, support and counit-mate comparisons preserve these paths and
their equality in every coefficient tower. Descend their common-stage representatives
using those same comparisons. This gives the common trace and composition equations,
and the common source/base-change square. Naturality at a split inclusion and
projection sandwiches both paths by the same endpoint maps, preserving all three
equations on direct summands, including zero and identity summands. -/
theorem rationalPurityTraceCoherence (P : PurityFiniteSetting.{u}) :
    RationalPurityTraceCoherence P := by
  sorry

end WeilConjectures.RationalPurityCoherence
