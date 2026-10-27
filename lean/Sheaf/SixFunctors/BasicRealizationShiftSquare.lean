/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q05
-/
module

public import Sheaf.SixFunctors.IntegralOperationShiftData
public import Sheaf.SixFunctors.GeneratorReductionStatement
public import Sheaf.Paper.CompletedPullbackTensorComparison
public import Sheaf.Paper.CompletedPrimitiveCounitComparison
public import Sheaf.SixFunctors.IntegralOpenReductionComparison
public import Sheaf.Paper.PurReductionLimitShiftAdjunction
public import Sheaf.SixFunctors.BasicSystemShiftResolutionCalculus
public import Sheaf.SixFunctors.OpenSemilinearTensorModel
public import Sheaf.Algebra.Homology.RoosConeCalculus
public import Sheaf.CategoryTheory.StrictRoosComparison
import Sheaf.SixFunctors.IntegralCompactificationSystemRealization
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.Paper.QuotientSystemFlatModels
import Sheaf.Paper.PurSequenceKFlatComparisonShifts
import Sheaf.Paper.SequenceKInjectiveComparisonShifts
import Sheaf.CategoryTheory.InjectiveTowerRoosShifts
import Sheaf.CategoryTheory.FlatRoosFunctorDescent
import Sheaf.AlgebraicGeometry.ProEtaleCountableProductsExact

/-! # Strict quotient shift squares and their normalized realization

Source: current blueprint sec-six-functors/sk-thm-sf-compatibility,
fix-prop-coherence.proof.md, maps-used coefficient-comparison sentence;
Stacks 011G, 014E and 0941 (blueprint: lem-pur-basic-realization-shift-square).

The finite tower comparisons below are the existing unit-normalized comparisons.
The two tensor slots are separate. Natural-number level n denotes exponent n+1.

## Main definitions

* `BasicStrictPullSquare`, `BasicStrictTensorSquares`, `BasicStrictOpenSquare`:
  strict squares for the existing quotient comparisons.
* `BasicRoosShiftSquares`: the signed cone square and its normalized total limit.
* `BasicDerivedRealizationSquares`: the whole derived squares and naturality.

## Main statements

* `basicRealizationShiftSquare`: simultaneous strict squares and their realization.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096
set_option genSizeOf false
set_option genInjectivity false

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme Opposite
namespace WeilConjectures.IntegralSystemRealization

attribute [local irreducible] roosF roosConeFunctor

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The canonical shift of the total derived coefficient limit.
Source: Stacks 0941 (blueprint: lem-pur-basic-realization-shift-square). -/
@[instance_reducible] def basicConstantLimitShift (W : Scheme.{u}) :
    (coefficientConstantTowerLimit l E W).CommShift ℤ :=
  inferInstanceAs ((lim : (ℕᵒᵖ ⥤ scalarReductionSource l E W) ⥤
    scalarReductionSource l E W).rightDerivedFunctor.CommShift ℤ)

/-- The prescribed composite source shift: reduction, operation, then actual total limit.
Source: blueprint coefficient-comparison sentence
(blueprint: lem-pur-basic-realization-shift-square). -/
def basicRealizationSourceShift {X Y : Scheme.{u}}
    (A : System l E X ⥤ System l E Y)
    (s : ∀ (r : ℤ) (M : System l E X), A.obj (M⟦r⟧) ≅ (A.obj M)⟦r⟧)
    (K : Integral l E X) (r : ℤ) :
    (coefficientSequenceLimit l E Y).obj (A.obj ((calculus l E X).reduction.obj (K⟦r⟧))) ≅
      ((coefficientSequenceLimit l E Y).obj (A.obj ((calculus l E X).reduction.obj K)))⟦r⟧ :=
  (coefficientSequenceLimit l E Y).mapIso
    (A.mapIso ((Functor.commShiftIso _ (self := reductionShift l E X) r).app K) ≪≫
      s r ((calculus l E X).reduction.obj K)) ≪≫
    (Functor.commShiftIso _ (self := limitShift l E Y) r).app
      (A.obj ((calculus l E X).reduction.obj K))

/-- The whole integral derived-category square for specified maps and specified shifts.
Source: blueprint coefficient-comparison sentence
(blueprint: lem-pur-basic-realization-shift-square). -/
def BasicRealizationSquare {X Y : Scheme.{u}}
    (A : System l E X ⥤ System l E Y) (G : Integral l E X ⥤ Integral l E Y)
    (s : ∀ (r : ℤ) (M : System l E X), A.obj (M⟦r⟧) ≅ (A.obj M)⟦r⟧)
    (g : ∀ (r : ℤ) (K : Integral l E X), G.obj (K⟦r⟧) ≅ (G.obj K)⟦r⟧)
    (d : ∀ K : Integral l E X,
      (coefficientSequenceLimit l E Y).obj (A.obj ((calculus l E X).reduction.obj K)) ⟶
        G.obj K) (K : Integral l E X) (r : ℤ) : Prop :=
  d (K⟦r⟧) ≫ (g r K).hom = (basicRealizationSourceShift l E A s K r).hom ≫ (d K)⟦r⟧'

/-- Naturality of an actual realized comparison, before any finite evaluation.
Source: blueprint coefficient-comparison sentence
(blueprint: lem-pur-basic-realization-shift-square). -/
def BasicRealizationNaturality {X Y : Scheme.{u}}
    (A : System l E X ⥤ System l E Y) (G : Integral l E X ⥤ Integral l E Y)
    (d : ∀ K : Integral l E X,
      (coefficientSequenceLimit l E Y).obj (A.obj ((calculus l E X).reduction.obj K)) ⟶
        G.obj K) (K N : Integral l E X) (f : K ⟶ N) : Prop :=
  (coefficientSequenceLimit l E Y).map (A.map ((calculus l E X).reduction.map f)) ≫ d N =
    d K ≫ G.map f

/-- Ordinary reduction complex used by the recorded completed pullback/tensor model.
Source: Stacks 06YY, 0941 (blueprint: lem-pur-basic-realization-shift-square). -/
abbrev basicReductionComplex (W : Scheme.{u}) :=
  (pullbackTensorOrdinaryReduction l E W).mapHomologicalComplex (.up ℤ)

/-- The coherent strict tensor tower, before its recorded comparison to finite tensors.
Source: Stacks 07A4, 0941 (blueprint: lem-pur-basic-realization-shift-square). -/
abbrev basicSystemTensorTower (W : Scheme.{u})
    (P Q : CochainComplex (scalarReductionSource l E W) ℤ) :=
  restrictedTower l E W ((systemTotalTensor l E W).obj
    ((basicReductionComplex l E W).obj P, (basicReductionComplex l E W).obj Q))

/-- Strict pullback quotient squares. Both vertical maps are degree-zero reindexing;
the equality is between tower maps, so includes every quotient transition.
Source: Stacks 011G, 0941 (blueprint: lem-pur-basic-realization-shift-square). -/
def BasicStrictPullSquare {X Y : Scheme.{u}} (v : X ⟶ Y)
    (P : CochainComplex (scalarReductionSource l E Y) ℤ) (r : ℤ) : Prop :=
  ∃ (a : restrictedTower l E X
        (((pullbackTensorSequenceInverse l E v).mapHomologicalComplex (.up ℤ)).obj
          ((basicReductionComplex l E Y).obj (P⟦r⟧))) ≅
      restrictedTower l E X
        (((pullbackTensorSequenceInverse l E v).mapHomologicalComplex (.up ℤ)).obj
          ((basicReductionComplex l E Y).obj P)) ⋙ shiftFunctor _ r)
    (b : (integralOperationsPullbackTowerFunctor l E v).obj (P⟦r⟧) ≅
      (integralOperationsPullbackTowerFunctor l E v).obj P ⋙ shiftFunctor _ r),
    (∀ (n : ℕ) (i : ℤ), HEq ((a.hom.app (op n)).f i)
      (𝟙 (((restrictedTower l E X
        (((pullbackTensorSequenceInverse l E v).mapHomologicalComplex (.up ℤ)).obj
          ((basicReductionComplex l E Y).obj (P⟦r⟧)))).obj (op n)).X i))) ∧
    (∀ (n : ℕ) (i : ℤ), HEq ((b.hom.app (op n)).f i)
      (𝟙 (((integralOperationsPullbackTowerFunctor l E v).obj (P⟦r⟧)).obj (op n)).X i)) ∧
    (pullbackTensorPullbackTower l E v (P⟦r⟧)).hom ≫ b.hom =
      a.hom ≫ ((Functor.whiskeringRight _ _ _).obj (shiftFunctor _ r)).map
        (pullbackTensorPullbackTower l E v P).hom

/-- Strict tensor quotient squares, using coefficient 1 in the left slot and
(-1)^(ri) in the right slot on first degree i. Both source shifts are pinned by
ordinary reduction, the existing signed tensor formulas, and scalar restriction.
Source: Stacks 011G, 012Z, 0941 (blueprint: lem-pur-basic-realization-shift-square). -/
def BasicStrictTensorSquares (W : Scheme.{u})
    (P Q : CochainComplex (scalarReductionSource l E W) ℤ) (r : ℤ) : Prop :=
  ∃ (cL : (systemTotalTensor l E W).obj
        (((basicReductionComplex l E W).obj P)⟦r⟧,
          (basicReductionComplex l E W).obj Q) ≅
      ((systemTotalTensor l E W).obj
        ((basicReductionComplex l E W).obj P, (basicReductionComplex l E W).obj Q))⟦r⟧)
    (cR : (systemTotalTensor l E W).obj
        ((basicReductionComplex l E W).obj P,
          ((basicReductionComplex l E W).obj Q)⟦r⟧) ≅
      ((systemTotalTensor l E W).obj
        ((basicReductionComplex l E W).obj P, (basicReductionComplex l E W).obj Q))⟦r⟧)
    (aL : basicSystemTensorTower l E W (P⟦r⟧) Q ≅
      basicSystemTensorTower l E W P Q ⋙ shiftFunctor _ r)
    (aR : basicSystemTensorTower l E W P (Q⟦r⟧) ≅
      basicSystemTensorTower l E W P Q ⋙ shiftFunctor _ r)
    (bL : (integralOperationsTensorTowerFunctor l E W).obj (P⟦r⟧, Q) ≅
      (integralOperationsTensorTowerFunctor l E W).obj (P, Q) ⋙ shiftFunctor _ r)
    (bR : (integralOperationsTensorTowerFunctor l E W).obj (P, Q⟦r⟧) ≅
      (integralOperationsTensorTowerFunctor l E W).obj (P, Q) ⋙ shiftFunctor _ r),
    systemTensorLeftFormula l E W ((basicReductionComplex l E W).obj P)
      ((basicReductionComplex l E W).obj Q) r cL ∧
    systemTensorRightFormula l E W ((basicReductionComplex l E W).obj P)
      ((basicReductionComplex l E W).obj Q) r cR ∧
    integralTensorLeftFormula l E W P Q r bL ∧
    integralCompletedTensorFiniteShiftFormula l E W P Q r bR ∧
    (∀ n : ℕ, aL.hom.app (op n) =
      ((levelRestriction l E W n).mapHomologicalComplex (.up ℤ)).map
        ((systemTotalTensor l E W).map
          (Prod.mkHom (((basicReductionComplex l E W).commShiftIso r).hom.app P) (𝟙 _)) ≫
            cL.hom) ≫
      (((levelRestriction l E W n).mapHomologicalComplex (.up ℤ)).commShiftIso r).hom.app
        ((systemTotalTensor l E W).obj
          ((basicReductionComplex l E W).obj P, (basicReductionComplex l E W).obj Q))) ∧
    (∀ n : ℕ, aR.hom.app (op n) =
      ((levelRestriction l E W n).mapHomologicalComplex (.up ℤ)).map
        ((systemTotalTensor l E W).map
          (Prod.mkHom (𝟙 _) (((basicReductionComplex l E W).commShiftIso r).hom.app Q)) ≫
            cR.hom) ≫
      (((levelRestriction l E W n).mapHomologicalComplex (.up ℤ)).commShiftIso r).hom.app
        ((systemTotalTensor l E W).obj
          ((basicReductionComplex l E W).obj P, (basicReductionComplex l E W).obj Q))) ∧
    ((pullbackTensorTensorTower l E W (P⟦r⟧) Q).hom ≫ bL.hom =
      aL.hom ≫ ((Functor.whiskeringRight _ _ _).obj (shiftFunctor _ r)).map
        (pullbackTensorTensorTower l E W P Q).hom) ∧
    ((pullbackTensorTensorTower l E W P (Q⟦r⟧)).hom ≫ bR.hom =
      aR.hom ≫ ((Functor.whiskeringRight _ _ _).obj (shiftFunctor _ r)).map
        (pullbackTensorTensorTower l E W P Q).hom)

/-- The actual ordinary open reduction comparison, on a representative and its shift.
The whole-system degree components are reindexed unchanged; its localization is the
specified r_j by the supplied representative-normalized Comparison.model.
Source: Stacks 0GL1 and 011G (blueprint: lem-pur-basic-realization-shift-square). -/
def BasicStrictOpenSquare {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (o : IntegralOpenReduction.Operations l E j)
    (SX : CoefficientDerivedSystemCalculus l E X)
    (SU : CoefficientDerivedSystemCalculus l E U)
    (AX : OpenSemilinearTensor.OrdinaryReduction l E X)
    (AU : OpenSemilinearTensor.OrdinaryReduction l E U)
    (tc : IntegralOpenReduction.TensorComparison l E j o)
    (c : OpenSemilinearTensor.Comparison l E j o SX SU AX AU tc)
    (Q : CochainComplex (scalarReductionSource l E U) ℤ) (r : ℤ) : Prop :=
  (∀ i : ℤ, HEq ((OpenSemilinearTensor.ordinaryChain l E j o AX AU c.ordinary
      (Q⟦r⟧)).hom.f i)
    ((OpenSemilinearTensor.ordinaryChain l E j o AX AU c.ordinary Q).hom.f (i + r))) ∧
  ∀ (hQ : CochainComplex.IsKFlatIndependentCoefficients
      (R := completedIntegralCommRingSheafUnrestricted l E U) Q)
    (hf : SemilinearSections.flatTerms.{u + 1, u, u + 1} (ProEt.topology U)
      (completedIntegralCommRingSheafUnrestricted l E U) Q),
    ∃ (cU : OpenSemilinearTensor.Computation l E SU AU Q hQ)
      (cX : OpenSemilinearTensor.Computation l E SX AX
        ((OpenSemilinearTensor.extensionComplex l E j o).obj Q) (c.kflat Q hQ hf)),
      c.r.hom.app (DerivedCategory.Q.obj Q) ≫
          (IntegralOpenReduction.J l E j o).map cU.iso.hom ≫
          (IntegralOpenReduction.systemExtension l E j o).mapDerivedCategoryFactors.hom.app
            ((AU.functor.mapHomologicalComplex (.up ℤ)).obj Q) =
        SX.reduction.map
            ((IntegralOpenReduction.extension l E j o).mapDerivedCategoryFactors.hom.app Q) ≫
          cX.iso.hom ≫ DerivedCategory.Q.map
            (OpenSemilinearTensor.ordinaryChain l E j o AX AU c.ordinary Q).hom

/-- The signed cone square and its transport through every normalized whole-tower rho.
The existing ShiftFormula uses the order (unshifted product, shifted product), with
coefficients (1,(-1)^r). Naturality includes every strict tower comparison, and hence
both signed tensor slots after their tower identifications.
Source: Stacks 011G, 014E, 0941 (blueprint: lem-pur-basic-realization-shift-square). -/
def BasicRoosShiftSquares (W : Scheme.{u}) : Prop :=
  ∃ cs : (roosF (A := scalarReductionSource l E W)).CommShift ℤ,
    RoosConeCalculus.ShiftFormula cs ∧
    (∀ (X Y : CochainComplex (ℕᵒᵖ ⥤ scalarReductionSource l E W) ℤ)
      (f : X ⟶ Y) (r : ℤ),
      roosF.map (f⟦r⟧') ≫ (Functor.commShiftIso roosF (self := cs) r).hom.app Y =
        (Functor.commShiftIso roosF (self := cs) r).hom.app X ≫ (roosF.map f)⟦r⟧') ∧
    ∀ (ρ : PrimitiveCounit.RoosRealization l E W)
      (X : CochainComplex (ℕᵒᵖ ⥤ scalarReductionSource l E W) ℤ) (r : ℤ),
      DerivedCategory.Q.map ((Functor.commShiftIso roosF (self := cs) r).hom.app X) ≫
          (DerivedCategory.Q.commShiftIso r).hom.app (roosF.obj X) ≫
          (ρ.comparison.hom.app X)⟦r⟧' =
        ρ.comparison.hom.app (X⟦r⟧) ≫
          (coefficientConstantTowerLimit l E W).map
            ((DerivedCategory.Q.commShiftIso r).hom.app X) ≫
          (Functor.commShiftIso _ (self := basicConstantLimitShift l E W) r).hom.app
            (DerivedCategory.Q.obj X)

/-- The actual derived squares for the five choices of operation and input slot.
Admissibility is exactly the dependency's complete constructible, normalized,
compatible-etale-origin, common finite cohomological and Tor interval predicate.
Source: blueprint maps-used sentence
(blueprint: lem-pur-basic-realization-shift-square). -/
structure BasicDerivedRealizationSquares (D : FiniteFieldDatum.{u})
    (o : GeneratorReduction.Operations l E) : Prop where
  reconstruction : ∀ (W : Over (Spec (.of D.k)))
    [LocallyOfFiniteType W.hom] [QuasiCompact W.hom] (r : ℤ),
    Adjunction.CommShift.CompatibilityUnit (calculus l E W.left).adjunction
      (Functor.commShiftIso _ (self := reductionShift l E W.left) r)
      (Functor.commShiftIso _ (self := limitShift l E W.left) r)
  pull : ∀ {U V : Over (Spec (.of D.k))}
    [LocallyOfFiniteType U.hom] [QuasiCompact U.hom]
    [LocallyOfFiniteType V.hom] [QuasiCompact V.hom] (v : U ⟶ V)
    [IsSeparated v.left] [LocallyOfFiniteType v.left] [QuasiCompact v.left]
    (K : Integral l E V.left) (lo hi torLo torHi : ℤ),
    GeneratorReduction.Admissible l E (calculus l E V.left) K lo hi torLo torHi →
    GeneratorReduction.SystemAdmissible l E U.left
      ((IntegralSystemRealization.pull l E v.left).obj ((calculus l E V.left).reduction.obj K))
      lo hi torLo torHi → ∀ r : ℤ,
    BasicRealizationSquare l E (IntegralSystemRealization.pull l E v.left)
      (integralDerivedPullback l E v.left)
      (fun r M ↦ (Functor.commShiftIso _ (self := systemPullShift l E v.left) r).app M)
      (fun r K ↦ (Functor.commShiftIso _ (self := (integralShifts l E).pull v.left) r).app K)
      (fun K ↦ (GeneratorReduction.pullD l E v.left).hom.app K) K r
  proper : ∀ {U V : Over (Spec (.of D.k))}
    [LocallyOfFiniteType U.hom] [QuasiCompact U.hom]
    [LocallyOfFiniteType V.hom] [QuasiCompact V.hom] (p : U ⟶ V) [IsProper p.left]
    (K : Integral l E U.left) (lo hi torLo torHi : ℤ),
    GeneratorReduction.Admissible l E (calculus l E U.left) K lo hi torLo torHi →
    GeneratorReduction.SystemAdmissible l E V.left
      ((Operations.push l E o.system p.left).obj ((calculus l E U.left).reduction.obj K))
      lo hi torLo torHi → ∀ r : ℤ,
    BasicRealizationSquare l E (Operations.push l E o.system p.left)
      (GeneratorReduction.integralPush l E o p.left)
      (fun r M ↦ (Functor.commShiftIso _ (self := systemPushShift l E o.system p.left) r).app M)
      (fun r K ↦ basicRealizationSourceShift l E (Operations.push l E o.system p.left)
        (fun r M ↦ (Functor.commShiftIso _ (self := systemPushShift l E o.system p.left) r).app M)
        K r) (fun _ ↦ 𝟙 _) K r
  shriek : ∀ {U V : Over (Spec (.of D.k))}
    [LocallyOfFiniteType U.hom] [QuasiCompact U.hom]
    [LocallyOfFiniteType V.hom] [QuasiCompact V.hom] (j : U ⟶ V)
    [IsOpenImmersion j.left] [QuasiCompact j.left]
    (K : Integral l E U.left) (lo hi torLo torHi : ℤ),
    GeneratorReduction.Admissible l E (calculus l E U.left) K lo hi torLo torHi →
    GeneratorReduction.SystemAdmissible l E V.left
      ((Operations.shriek l E o.system j.left).obj ((calculus l E U.left).reduction.obj K))
      lo hi torLo torHi → ∀ r : ℤ,
    BasicRealizationSquare l E (Operations.shriek l E o.system j.left) (ringedOpen l E j.left)
      (fun r M ↦ (Functor.commShiftIso _ (self := systemOpenShift l E o.system j.left) r).app M)
      (fun r K ↦ (Functor.commShiftIso _ (self := (integralShifts l E).shriek j.left) r).app K)
      (GeneratorReduction.openD l E o j.left) K r
  tensor : ∀ (W : Over (Spec (.of D.k)))
    [LocallyOfFiniteType W.hom] [QuasiCompact W.hom]
    (K N : Integral l E W.left) (lo hi torLo torHi : ℤ),
    GeneratorReduction.Admissible l E (calculus l E W.left) K lo hi torLo torHi →
    GeneratorReduction.Admissible l E (calculus l E W.left) N lo hi torLo torHi →
    GeneratorReduction.SystemAdmissible l E W.left
      ((calculus l E W.left).systemClosed.tensor.obj
        ((calculus l E W.left).reduction.obj K, (calculus l E W.left).reduction.obj N))
      lo hi torLo torHi → ∀ r : ℤ,
    (BasicRealizationSquare l E
      ((Functor.curry.obj (calculus l E W.left).systemClosed.tensor).flip.obj
        ((calculus l E W.left).reduction.obj N))
      ((Functor.curry.obj (integralCompletedTensor l E W.left)).flip.obj N)
      (fun r M ↦ ((tensorShifts l E).systemLeft W.left r).app
        (M, (calculus l E W.left).reduction.obj N))
      (fun r K ↦ ((tensorShifts l E).integralLeft W.left r).app (K, N))
      (fun K ↦ (GeneratorReduction.tensorD l E W.left).hom.app (K, N)) K r) ∧
    (BasicRealizationSquare l E
      ((Functor.curry.obj (calculus l E W.left).systemClosed.tensor).obj
        ((calculus l E W.left).reduction.obj K))
      ((Functor.curry.obj (integralCompletedTensor l E W.left)).obj K)
      (fun r M ↦ ((tensorShifts l E).systemRight W.left r).app
        ((calculus l E W.left).reduction.obj K, M))
      (fun r N ↦ ((tensorShifts l E).integralRight W.left r).app (K, N))
      (fun N ↦ (GeneratorReduction.tensorD l E W.left).hom.app (K, N)) N r)
  pull_natural : ∀ {U V : Over (Spec (.of D.k))}
    [LocallyOfFiniteType U.hom] [QuasiCompact U.hom]
    [LocallyOfFiniteType V.hom] [QuasiCompact V.hom]
    (v : U ⟶ V) (K N : Integral l E V.left) (f : K ⟶ N),
    BasicRealizationNaturality l E (IntegralSystemRealization.pull l E v.left)
      (integralDerivedPullback l E v.left) (fun K ↦ (GeneratorReduction.pullD l E v.left).hom.app K)
      K N f
  open_natural : ∀ {U V : Over (Spec (.of D.k))}
    [LocallyOfFiniteType U.hom] [QuasiCompact U.hom]
    [LocallyOfFiniteType V.hom] [QuasiCompact V.hom] (j : U ⟶ V)
    [IsOpenImmersion j.left] [QuasiCompact j.left]
    (K N : Integral l E U.left) (f : K ⟶ N) (lo hi torLo torHi : ℤ),
    GeneratorReduction.Admissible l E (calculus l E U.left) K lo hi torLo torHi →
    GeneratorReduction.Admissible l E (calculus l E U.left) N lo hi torLo torHi →
    BasicRealizationNaturality l E (Operations.shriek l E o.system j.left) (ringedOpen l E j.left)
      (GeneratorReduction.openD l E o j.left) K N f
  tensor_natural : ∀ (W : Over (Spec (.of D.k)))
    [LocallyOfFiniteType W.hom] [QuasiCompact W.hom] (K K' N N' : Integral l E W.left)
    (f : K ⟶ K') (g : N ⟶ N'),
    (coefficientSequenceLimit l E W.left).map ((calculus l E W.left).systemClosed.tensor.map
      (Prod.mkHom ((calculus l E W.left).reduction.map f)
        ((calculus l E W.left).reduction.map g))) ≫
        (GeneratorReduction.tensorD l E W.left).hom.app (K', N') =
      (GeneratorReduction.tensorD l E W.left).hom.app (K, N) ≫
        (integralCompletedTensor l E W.left).map (Prod.mkHom f g)

/-- Simultaneous strict quotient squares, signed Roos realization, and the actual d_A.
Source: current blueprint sec-six-functors/sk-thm-sf-compatibility,
fix-prop-coherence.proof.md, maps-used sentence; Stacks 011G, 014E and 0941
(blueprint: lem-pur-basic-realization-shift-square).

Proof:
1. Choose good flat-term K-flat integral representatives by lem-pc-kflat-resolution.
   The quotient systems and their true transitions compute reduction, pullback and
   tensor by lem-pur-quotient-system-flat-models. Shift them using
   lem-pur-sequence-kflat-comparison-shifts and the simultaneous operation models of
   lem-pur-basic-system-shift-resolution-calculus. For proper image shift a whole
   K-injective system resolution, never its separate finite evaluations.
2. Scalar reduction and unary operation maps have degree zero, so their shift
   components are their original components in degree i+r. In a tensor slot use
   coefficient 1 on the left and (-1)^(ri) on the right. Every quotient transition
   preserves both degrees. These are the specified r_F,r_T models of
   lem-pur-completed-primitive-counit-comparison and the defining proper realization
   of lem-sf-primitive-reduction-transpose, not independently lifted finite arrows.
3. Use lem-sf-open-semilinear-tensor-model: the ordinary open coefficient comparison
   sends [x] tensor a to [x tensor a restricted to the open]. The scalar a has degree
   zero, so the strict square is unchanged on reindexed components and transitions.
   Its augmented computation square localizes to the specified r_j of
   lem-sf-integral-open-reduction-comparison.
4. Write h=1-s. The fibre differential in coordinates (b,a) is
   (db,-da-hb). For epsilon=(-1)^r, (b,a) mapped to (b,epsilon a) intertwines the
   shifted differentials. A strict tower map acts by (ub,ua), so both routes of
   its cone square are (ub,epsilon ua). Apply this also to the two tensor squares.
5. By lem-weil-strict-roos-comparison the normalized rho on a resolution a:X to I
   is eta_I inverse composed with C(a). The zero-shifted-coordinate inclusion eta
   commutes with this diagonal shift by lem-pur-injective-tower-roos-shifts.
   Thus the same shift square holds for the actual derived limit. On semilinear
   restriction use the shifted replacement of lem-pur-sequence-kinjective-comparison-shifts.
6. Pullback and tensor d_A are the inverses of these quotient/Roos identifications;
   proper d_A is identity on its defining L S R tower. Invert the preceding squares
   to obtain sigma_G d_A(K[r]) = d_A(K)[r] sigma_F for the prescribed shifts of
   def-pur-integral-operation-shift-data and the comparisons of
   lem-sf-generator-reduction-coherence.
7. In the open case d_j inverse is L(r_j) followed after the actual reconstruction
   unit. Use lem-pur-reduction-limit-shift-adjunction for that unit and Step 3 for
   r_j, then invert the composite square. Completeness is only used where the
   dependency asserts it; no inverse-limit preservation by open extension is used.
8. The quotient and operation model squares are natural for all representatives.
   lem-pur-flat-roos-functor-descent descends them independently of representatives,
   including derived roofs. The comparison squares are equalities in the entire
   integral derived category, with no cohomology or finite-evaluation faithfulness.
-/
theorem basicRealizationShiftSquare (D : FiniteFieldDatum.{u}) (_hl : l ≠ D.p)
    (o : GeneratorReduction.Operations l E) :
    (∀ {U V : Over (Spec (.of D.k))}
      [LocallyOfFiniteType U.hom] [QuasiCompact U.hom]
      [LocallyOfFiniteType V.hom] [QuasiCompact V.hom]
      (v : U ⟶ V) [IsSeparated v.left] [LocallyOfFiniteType v.left] [QuasiCompact v.left]
      (P : (integralOperationsGoodComplex l E V.left).FullSubcategory) (r : ℤ),
      BasicStrictPullSquare l E v.left P.obj r) ∧
    (∀ (W : Over (Spec (.of D.k))) [LocallyOfFiniteType W.hom] [QuasiCompact W.hom]
      (P Q : (integralOperationsGoodComplex l E W.left).FullSubcategory) (r : ℤ),
      BasicStrictTensorSquares l E W.left P.obj Q.obj r) ∧
    (∀ {U V : Over (Spec (.of D.k))}
      [LocallyOfFiniteType U.hom] [QuasiCompact U.hom]
      [LocallyOfFiniteType V.hom] [QuasiCompact V.hom]
      (p : U ⟶ V) [IsProper p.left], BasicSystemImageShiftModels l E o.system p.left) ∧
    (∀ {U V : Over (Spec (.of D.k))}
      [LocallyOfFiniteType U.hom] [QuasiCompact U.hom]
      [LocallyOfFiniteType V.hom] [QuasiCompact V.hom]
      (j : U ⟶ V) [IsOpenImmersion j.left] [QuasiCompact j.left]
      (a : IntegralOpenReduction.Operations l E j.left)
      (SV : CoefficientDerivedSystemCalculus l E V.left)
      (SU : CoefficientDerivedSystemCalculus l E U.left)
      (AV : OpenSemilinearTensor.OrdinaryReduction l E V.left)
      (AU : OpenSemilinearTensor.OrdinaryReduction l E U.left)
      (tc : IntegralOpenReduction.TensorComparison l E j.left a)
      (c : OpenSemilinearTensor.Comparison l E j.left a SV SU AV AU tc)
      (Q : (integralOperationsGoodComplex l E U.left).FullSubcategory) (r : ℤ),
      BasicStrictOpenSquare l E j.left a SV SU AV AU tc c Q.obj r) ∧
    (∀ (W : Over (Spec (.of D.k))) [LocallyOfFiniteType W.hom] [QuasiCompact W.hom],
      BasicRoosShiftSquares l E W.left) ∧
    Nonempty (BasicDerivedRealizationSquares l E D o) := by
  sorry

end WeilConjectures.IntegralSystemRealization
