/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q51
-/
module

public import Sheaf.Paper.SixFunctorDualNotation
public import Sheaf.Paper.CanonicalOriginCompactSupportComposition
public import Sheaf.Paper.ConstructibleProjectionMates
public import Sheaf.Paper.FiniteProjectionActionLaws
public import Sheaf.Paper.ProjectionFiniteBaseChangeCoordinates
import Sheaf.Paper.CompactSupportProjectionCoherenceLaws
import Sheaf.SixFunctors.OpenBaseChangeSquare
import Sheaf.Paper.CompactificationProjectionPasting

public import Sheaf.Paper.SixFunctorDatum
import Sheaf.Paper.ProjectionFiniteBaseChangeTransport
import Sheaf.Paper.ProjectionTensorActionExpansion
import Sheaf.Paper.ProjectionIdentityAssembly
import Sheaf.Paper.ProjectionFiniteReduction
import Sheaf.Paper.SfProEtaleProjectionFormula

/-! # Coherence of the projection transformation

Source: current blueprint, sec-six-functors/sk-prop-sf-pf-coherence,
statement and proof (blueprint: prop-sf-pf-coherence).
The equations use the recorded projection components and composition comparisons.

## Main statements

* `sixFunctorProjection_naturality`, `sixFunctorProjection_composition`,
  `sixFunctorProjection_pentagon`, `sixFunctorProjection_compactification` and
  `sixFunctorProjection_proper` give the four-stage structural equations.
* `sixFunctorProjection_baseChange_integral`, `sixFunctorProjection_baseChange_rational`
  and `sixFunctorProjection_baseChange_common` give the higher-coefficient squares.
* `sixFunctorProjection_identity` gives the normalized identity equation.
* `sixFunctorProjection_realization` gives the finite realization equation.

The finite square uses `S.finiteExchangeProjection` and the actual full-domain
`CompactSupportFiniteProjection.component`, with canonical endpoint transports.
The final clause follows the current blueprint_update: all-ideal finite reduction.
The reduction equation is written on the original coefficient category, where
reduction is right tensor by the constant quotient; higher stages retain the same
associativity equation with completed tensor and its normalized associator.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096

universe u v w

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Functor
open WeilConjectures.GeneralAlgebraicallyClosedCoefficients

namespace WeilConjectures

attribute [-instance] WeilConjectures.IntegralHom.derivedCategory

attribute [local irreducible] Scheme.residueField

section
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

private theorem projectionGeometry {D : FiniteFieldDatum.{u}}
    {X Y : SixFunctorSpace D} (f : X ⟶ Y) (c : Compactification f.hom.left) :
    LocallyOfFiniteType f.hom.left ∧ QuasiCompact f.hom.left := by
  let : IsOpenImmersion c.i := c.isOpenImmersion
  let : IsProper c.g := c.isProper
  have hf : LocallyOfFiniteType f.hom.left := by
    rw [c.comm]
    exact locallyOfFiniteType_comp c.i c.g
  let : LocallyOfFiniteType X.obj.hom := X.property.1
  let : QuasiCompact X.obj.hom := X.property.2
  let : IsNoetherian X.obj.left := isNoetherian_of_locallyOfFiniteType X.obj.hom
  exact ⟨hf, quasiCompact_of_noetherianSpace_source _⟩

end

variable {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
  {E : Type u} [Field E] [Algebra (Padic C.l) E]
  [FiniteDimensional (Padic C.l) E] {n : ℕ} {hn : 1 ≤ n}

/-- Naturality of the supplied projection maps at all four coefficient stages.
Source: current blueprint prop-sf-pf-coherence, naturality clause
(blueprint: prop-sf-pf-coherence).
Proof: Naturality of the adjunction unit and counit gives naturality of the proper
projection mate. The open tensor comparison is natural in both inputs. Composing
these equalities and conjugating by the recorded support realizations gives the
finite equation. The same construction on completed systems gives the integral
equation before evaluation; rationalization and common-stage inclusion preserve it. -/
theorem sixFunctorProjection_naturality (S : SixFunctorDatum D C E n hn) :
    (∀ {X Y : SixFunctorSpace D} (f : X ⟶ Y)
    [IsSeparated f.hom.left] [LocallyOfFiniteType f.hom.left] [QuasiCompact f.hom.left]
    (c : Compactification f.hom.left) {K K' : sixFunctorFiniteCategory D C E n hn X}
    {L L' : finiteTorConstructibleCategory C.l E n hn Y.obj.left},
    ∀ (a : K ⟶ K') (b : L ⟶ L'),
      ((CompactSupportFiniteProjection.partialTensor S.toSixFunctorFiniteOperations Y).map
        ((S.toSixFunctorFiniteOperations.finite.support f c).map a)).app L ≫
          ((CompactSupportFiniteProjection.partialTensor S.toSixFunctorFiniteOperations Y).obj
            ((S.toSixFunctorFiniteOperations.finite.support f c).obj K')).map b ≫
          CompactSupportFiniteProjection.component S.toSixFunctorFiniteOperations f c K' L' =
        CompactSupportFiniteProjection.component S.toSixFunctorFiniteOperations f c K L ≫
          (S.toSixFunctorFiniteOperations.finite.support f c).map
            (((CompactSupportFiniteProjection.partialTensor S.toSixFunctorFiniteOperations X).map
              a).app ((CompactSupportFiniteProjection.torPull S.toSixFunctorFiniteOperations
              f).obj L) ≫
              ((CompactSupportFiniteProjection.partialTensor S.toSixFunctorFiniteOperations X).obj
                K').map ((CompactSupportFiniteProjection.torPull S.toSixFunctorFiniteOperations
                f).map b))) ∧
    (∀ {X Y : SixFunctorSpace D} (f : X ⟶ Y)
    [IsSeparated f.hom.left] [LocallyOfFiniteType f.hom.left] [QuasiCompact f.hom.left]
    (c : Compactification f.hom.left) {K K' : sfIntegralConstructibleCategory C.l E X.obj.left} {L
      L' : sfIntegralConstructibleCategory C.l E Y.obj.left},
    S.toSixFunctorOperationDatum.integralFiniteTorDomain Y L →
      S.toSixFunctorOperationDatum.integralFiniteTorDomain Y L' → ∀ (a : K ⟶ K') (b : L ⟶ L'),
      ((S.higher.integralTensor Y).map ((S.higher.integral.support f c).map a)).app L ≫
          ((S.higher.integralTensor Y).obj ((S.higher.integral.support f c).obj K')).map b ≫
          compactSupportProjectionComponent S.higher.integralExchange f c K' L' =
        compactSupportProjectionComponent S.higher.integralExchange f c K L ≫
          (S.higher.integral.support f c).map
            (((S.higher.integralTensor X).map a).app ((S.higher.integral.pull f).obj L) ≫
              ((S.higher.integralTensor X).obj K').map ((S.higher.integral.pull f).map b))) ∧
    (∀ {X Y : SixFunctorSpace D} (f : X ⟶ Y)
    [IsSeparated f.hom.left] [LocallyOfFiniteType f.hom.left] [QuasiCompact f.hom.left]
    (c : Compactification f.hom.left) {K K' : sfRationalConstructibleCategory C.l E X.obj.left} {L
      L' : sfRationalConstructibleCategory C.l E Y.obj.left},
    ∀ (a : K ⟶ K') (b : L ⟶ L'),
      ((S.higher.rationalTensor Y).map ((S.higher.rational.support f c).map a)).app L ≫
          ((S.higher.rationalTensor Y).obj ((S.higher.rational.support f c).obj K')).map b ≫
          compactSupportProjectionComponent S.higher.rationalExchange f c K' L' =
        compactSupportProjectionComponent S.higher.rationalExchange f c K L ≫
          (S.higher.rational.support f c).map
            (((S.higher.rationalTensor X).map a).app ((S.higher.rational.pull f).obj L) ≫
              ((S.higher.rationalTensor X).obj K').map ((S.higher.rational.pull f).map b))) ∧
    (∀ {X Y : SixFunctorSpace D} (f : X ⟶ Y)
    [IsSeparated f.hom.left] [LocallyOfFiniteType f.hom.left] [QuasiCompact f.hom.left]
    (c : Compactification f.hom.left) {K K' : generalAlgebraicallyClosedConstructibleCategory C.l
      C.Qbar X.obj.left} {L L' : generalAlgebraicallyClosedConstructibleCategory C.l C.Qbar
      Y.obj.left},
    ∀ (a : K ⟶ K') (b : L ⟶ L'),
      ((S.closure.commonStageTensor Y).map ((S.closure.commonStage.support f c).map a)).app L ≫
          ((S.closure.commonStageTensor Y).obj ((S.closure.commonStage.support f c).obj K')).map b ≫
          compactSupportProjectionComponent S.closure.commonStageExchange f c K' L' =
        compactSupportProjectionComponent S.closure.commonStageExchange f c K L ≫
          (S.closure.commonStage.support f c).map
            (((S.closure.commonStageTensor X).map a).app ((S.closure.commonStage.pull f).obj L) ≫
              ((S.closure.commonStageTensor X).obj K').map ((S.closure.commonStage.pull f).map
                b))) := by
  have h := compactSupportProjection_coherenceLaws S.toSixFunctorOperationDatum
  refine ⟨h.1.naturality, ?_, ?_, ?_⟩
  · exact h.2.1.naturality
  · intro X Y f _ _ _ c K K' L L' a b
    exact h.2.2.1.naturality f c trivial trivial a b
  · intro X Y f _ _ _ c K K' L L' a b
    exact h.2.2.2.1.naturality f c trivial trivial a b

/-- Compactification of the supplied projection maps at all four coefficient stages.
Source: current blueprint prop-sf-pf-coherence, compactification clause
(blueprint: prop-sf-pf-coherence).
Proof: For a refinement, the specified proper and open comparisons intertwine the
counit mate and the open tensor map. Pasting the two factor squares gives the
projection square. Compare two compactifications through a common refinement
and use the comparison cocycle. Do this on coherent systems at the integral
stage, then apply rationalization and common-stage inclusion. -/
theorem sixFunctorProjection_compactification (S : SixFunctorDatum D C E n hn) :
    (∀ {X Y : SixFunctorSpace D} (f : X ⟶ Y)
    [IsSeparated f.hom.left] [LocallyOfFiniteType f.hom.left] [QuasiCompact f.hom.left]
    (c d : Compactification f.hom.left) (K : sixFunctorFiniteCategory D C E n hn X)
    (L : finiteTorConstructibleCategory C.l E n hn Y.obj.left),
      ((CompactSupportFiniteProjection.partialTensor S.toSixFunctorFiniteOperations Y).map
        ((S.toSixFunctorFiniteOperations.finite.comparison f c d).hom.app K)).app L ≫
          CompactSupportFiniteProjection.component S.toSixFunctorFiniteOperations f d K L =
        CompactSupportFiniteProjection.component S.toSixFunctorFiniteOperations f c K L ≫
          (S.toSixFunctorFiniteOperations.finite.comparison f c d).hom.app
            (((CompactSupportFiniteProjection.partialTensor S.toSixFunctorFiniteOperations X).obj
              K).obj ((CompactSupportFiniteProjection.torPull S.toSixFunctorFiniteOperations
              f).obj L))) ∧
    (∀ {X Y : SixFunctorSpace D} (f : X ⟶ Y)
    [IsSeparated f.hom.left] [LocallyOfFiniteType f.hom.left] [QuasiCompact f.hom.left]
    (c d : Compactification f.hom.left) (K : sfIntegralConstructibleCategory C.l E X.obj.left) (L
      : sfIntegralConstructibleCategory C.l E Y.obj.left),
      S.toSixFunctorOperationDatum.integralFiniteTorDomain Y L →
      ((S.higher.integralTensor Y).map ((S.higher.integral.comparison f c d).hom.app K)).app L ≫
          compactSupportProjectionComponent S.higher.integralExchange f d K L =
        compactSupportProjectionComponent S.higher.integralExchange f c K L ≫
          (S.higher.integral.comparison f c d).hom.app (((S.higher.integralTensor X).obj K).obj
            ((S.higher.integral.pull f).obj L))) ∧
    (∀ {X Y : SixFunctorSpace D} (f : X ⟶ Y)
    [IsSeparated f.hom.left] [LocallyOfFiniteType f.hom.left] [QuasiCompact f.hom.left]
    (c d : Compactification f.hom.left) (K : sfRationalConstructibleCategory C.l E X.obj.left) (L
      : sfRationalConstructibleCategory C.l E Y.obj.left), ((S.higher.rationalTensor Y).map
      ((S.higher.rational.comparison f c d).hom.app K)).app L ≫
          compactSupportProjectionComponent S.higher.rationalExchange f d K L =
        compactSupportProjectionComponent S.higher.rationalExchange f c K L ≫
          (S.higher.rational.comparison f c d).hom.app (((S.higher.rationalTensor X).obj K).obj
            ((S.higher.rational.pull f).obj L))) ∧
    (∀ {X Y : SixFunctorSpace D} (f : X ⟶ Y)
    [IsSeparated f.hom.left] [LocallyOfFiniteType f.hom.left] [QuasiCompact f.hom.left]
    (c d : Compactification f.hom.left) (K : generalAlgebraicallyClosedConstructibleCategory C.l
      C.Qbar X.obj.left) (L : generalAlgebraicallyClosedConstructibleCategory C.l C.Qbar
      Y.obj.left), ((S.closure.commonStageTensor Y).map ((S.closure.commonStage.comparison f c
      d).hom.app
        K)).app L ≫
          compactSupportProjectionComponent S.closure.commonStageExchange f d K L =
        compactSupportProjectionComponent S.closure.commonStageExchange f c K L ≫
          (S.closure.commonStage.comparison f c d).hom.app (((S.closure.commonStageTensor X).obj
            K).obj ((S.closure.commonStage.pull f).obj L))) := by
  have h := compactSupportProjection_coherenceLaws S.toSixFunctorOperationDatum
  refine ⟨h.1.compactification, ?_, ?_, ?_⟩
  · exact h.2.1.compactification
  · intro X Y f _ _ _ c d K L
    exact h.2.2.1.compactification f c d K L trivial
  · intro X Y f _ _ _ c d K L
    exact h.2.2.2.1.compactification f c d K L trivial

/-- Composition of the supplied projection maps at all four coefficient stages.
Source: current blueprint prop-sf-pf-coherence, composition clause
(blueprint: prop-sf-pf-coherence).
Proof: The proper-factor equations are the two transposes of the same composite
counit under the pasted adjunction. The open factor follows by restriction to
the open image. Paste them and use the normalized composition comparison; at
finite coefficients this is the recorded originComposition, not a chosen iso.
The integral system realization preserves the equation and the scalar functors
carry it to the rational and common stages. -/
theorem sixFunctorProjection_composition (S : SixFunctorDatum D C E n hn) :
    (∀ {X Y Z : SixFunctorSpace D} (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsSeparated f.hom.left] [LocallyOfFiniteType f.hom.left] [QuasiCompact f.hom.left]
    [IsSeparated g.hom.left] [LocallyOfFiniteType g.hom.left] [QuasiCompact g.hom.left]
    (cf : Compactification f.hom.left) (cg : Compactification g.hom.left)
    (cfg : Compactification (f ≫ g).hom.left) (K : sixFunctorFiniteCategory D C E n hn X)
    (L : finiteTorConstructibleCategory C.l E n hn Z.obj.left),
      ((CompactSupportFiniteProjection.partialTensor S.toSixFunctorFiniteOperations Z).map
        ((S.toSixFunctorFiniteOperations.finite.composition f g cf cg cfg).hom.app K)).app L ≫
          CompactSupportFiniteProjection.component S.toSixFunctorFiniteOperations g cg
            ((S.toSixFunctorFiniteOperations.finite.support f cf).obj K) L ≫
          (S.toSixFunctorFiniteOperations.finite.support g cg).map
            (CompactSupportFiniteProjection.component S.toSixFunctorFiniteOperations f cf K
              ((CompactSupportFiniteProjection.torPull S.toSixFunctorFiniteOperations g).obj L)) =
        CompactSupportFiniteProjection.component S.toSixFunctorFiniteOperations (f ≫ g) cfg K L ≫
          (S.toSixFunctorFiniteOperations.finite.composition f g cf cg cfg).hom.app
            (((CompactSupportFiniteProjection.partialTensor S.toSixFunctorFiniteOperations X).obj
              K).obj ((CompactSupportFiniteProjection.torPull S.toSixFunctorFiniteOperations (f ≫
              g)).obj L)) ≫
          (S.toSixFunctorFiniteOperations.finite.support g cg).map
            ((S.toSixFunctorFiniteOperations.finite.support f cf).map
            (((CompactSupportFiniteProjection.partialTensor S.toSixFunctorFiniteOperations X).obj
              K).map (CompactSupportFiniteProjection.torPullComposition
              S.toSixFunctorFiniteOperations f g L).hom))) ∧
    (∀ {X Y Z : SixFunctorSpace D} (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsSeparated f.hom.left] [LocallyOfFiniteType f.hom.left] [QuasiCompact f.hom.left]
    [IsSeparated g.hom.left] [LocallyOfFiniteType g.hom.left] [QuasiCompact g.hom.left]
    (cf : Compactification f.hom.left) (cg : Compactification g.hom.left)
    (cfg : Compactification (f ≫ g).hom.left) (K : sfIntegralConstructibleCategory C.l E
      X.obj.left) (L : sfIntegralConstructibleCategory C.l E Z.obj.left),
      S.toSixFunctorOperationDatum.integralFiniteTorDomain Z L →
      ((S.higher.integralTensor Z).map ((S.higher.integral.composition f g cf cg cfg).hom.app
        K)).app L ≫
          compactSupportProjectionComponent S.higher.integralExchange g cg
            ((S.higher.integral.support f cf).obj K) L ≫
          (S.higher.integral.support g cg).map
            (compactSupportProjectionComponent S.higher.integralExchange f cf K
              ((S.higher.integral.pull g).obj L)) =
        compactSupportProjectionComponent S.higher.integralExchange (f ≫ g) cfg K L ≫
          (S.higher.integral.composition f g cf cg cfg).hom.app
            (((S.higher.integralTensor X).obj K).obj ((S.higher.integral.pull (f ≫ g)).obj L)) ≫
          (S.higher.integral.support g cg).map ((S.higher.integral.support f cf).map
            (((S.higher.integralTensor X).obj K).map ((S.higher.integral.pullComposition f
              g).hom.app L)))) ∧
    (∀ {X Y Z : SixFunctorSpace D} (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsSeparated f.hom.left] [LocallyOfFiniteType f.hom.left] [QuasiCompact f.hom.left]
    [IsSeparated g.hom.left] [LocallyOfFiniteType g.hom.left] [QuasiCompact g.hom.left]
    (cf : Compactification f.hom.left) (cg : Compactification g.hom.left)
    (cfg : Compactification (f ≫ g).hom.left) (K : sfRationalConstructibleCategory C.l E
      X.obj.left) (L : sfRationalConstructibleCategory C.l E Z.obj.left),
          ((S.higher.rationalTensor Z).map ((S.higher.rational.composition f g cf cg cfg).hom.app
        K)).app L ≫
          compactSupportProjectionComponent S.higher.rationalExchange g cg
            ((S.higher.rational.support f cf).obj K) L ≫
          (S.higher.rational.support g cg).map
            (compactSupportProjectionComponent S.higher.rationalExchange f cf K
              ((S.higher.rational.pull g).obj L)) =
        compactSupportProjectionComponent S.higher.rationalExchange (f ≫ g) cfg K L ≫
          (S.higher.rational.composition f g cf cg cfg).hom.app
            (((S.higher.rationalTensor X).obj K).obj ((S.higher.rational.pull (f ≫ g)).obj L)) ≫
          (S.higher.rational.support g cg).map ((S.higher.rational.support f cf).map
            (((S.higher.rationalTensor X).obj K).map ((S.higher.rational.pullComposition f
              g).hom.app L)))) ∧
    (∀ {X Y Z : SixFunctorSpace D} (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsSeparated f.hom.left] [LocallyOfFiniteType f.hom.left] [QuasiCompact f.hom.left]
    [IsSeparated g.hom.left] [LocallyOfFiniteType g.hom.left] [QuasiCompact g.hom.left]
    (cf : Compactification f.hom.left) (cg : Compactification g.hom.left)
    (cfg : Compactification (f ≫ g).hom.left) (K : generalAlgebraicallyClosedConstructibleCategory
      C.l C.Qbar X.obj.left) (L : generalAlgebraicallyClosedConstructibleCategory C.l C.Qbar
      Z.obj.left), ((S.closure.commonStageTensor Z).map ((S.closure.commonStage.composition f g
          cf cg
        cfg).hom.app K)).app L ≫
          compactSupportProjectionComponent S.closure.commonStageExchange g cg
            ((S.closure.commonStage.support f cf).obj K) L ≫
          (S.closure.commonStage.support g cg).map
            (compactSupportProjectionComponent S.closure.commonStageExchange f cf K
              ((S.closure.commonStage.pull g).obj L)) =
        compactSupportProjectionComponent S.closure.commonStageExchange (f ≫ g) cfg K L ≫
          (S.closure.commonStage.composition f g cf cg cfg).hom.app
            (((S.closure.commonStageTensor X).obj K).obj ((S.closure.commonStage.pull (f ≫ g)).obj
              L)) ≫
          (S.closure.commonStage.support g cg).map ((S.closure.commonStage.support f cf).map
            (((S.closure.commonStageTensor X).obj K).map ((S.closure.commonStage.pullComposition f
              g).hom.app L)))) := by
  have h := compactSupportProjection_coherenceLaws S.toSixFunctorOperationDatum
  refine ⟨h.1.composition, ?_, ?_, ?_⟩
  · exact h.2.1.composition
  · intro X Y Z f g _ _ _ _ _ _ cf cg cfg K L
    exact h.2.2.1.composition f g cf cg cfg K L trivial
  · intro X Y Z f g _ _ _ _ _ _ cf cg cfg K L
    exact h.2.2.2.1.composition f g cf cg cfg K L trivial

/-- Pentagon of the supplied projection maps at all four coefficient stages.
Source: current blueprint prop-sf-pf-coherence, pentagon clause
(blueprint: prop-sf-pf-coherence).
Proof: Apply the associativity of mate pasting to three proper factors and the
corresponding open restrictions. Both composites have the same counit transpose.
The canonical pullback and tensor associators identify their endpoints. The
finite compositor is normalized to originComposition_assoc; the completed system
identity, rationalization, and common-stage comparisons give the other equations. -/
theorem sixFunctorProjection_pentagon (S : SixFunctorDatum D C E n hn) :
    (∀ {X Y Z W : SixFunctorSpace D}
    (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ W)
    [IsSeparated f.hom.left] [LocallyOfFiniteType f.hom.left] [QuasiCompact f.hom.left]
    [IsSeparated g.hom.left] [LocallyOfFiniteType g.hom.left] [QuasiCompact g.hom.left]
    [IsSeparated h.hom.left] [LocallyOfFiniteType h.hom.left] [QuasiCompact h.hom.left]
    (cf : Compactification f.hom.left) (cg : Compactification g.hom.left)
    (ch : Compactification h.hom.left) (cfg : Compactification (f ≫ g).hom.left)
    (cgh : Compactification (g ≫ h).hom.left)
    (cfgh : Compactification ((f ≫ g) ≫ h).hom.left) (K : sixFunctorFiniteCategory D C E n hn X),
    HEq ((S.toSixFunctorFiniteOperations.finite.composition (f ≫ g) h cfg ch cfgh).hom.app K ≫
      (S.toSixFunctorFiniteOperations.finite.support h ch).map
        ((S.toSixFunctorFiniteOperations.finite.composition f g cf cg cfg).hom.app K))
      ((S.toSixFunctorFiniteOperations.finite.composition f (g ≫ h) cf cgh
        (Eq.mp (congrArg (fun t : X ⟶ W ↦ Compactification t.hom.left)
          (Category.assoc f g h)) cfgh)).hom.app K ≫
        (S.toSixFunctorFiniteOperations.finite.composition g h cg ch cgh).hom.app
          ((S.toSixFunctorFiniteOperations.finite.support f cf).obj K))) ∧
    (∀ {X Y Z W : SixFunctorSpace D}
    (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ W)
    [IsSeparated f.hom.left] [LocallyOfFiniteType f.hom.left] [QuasiCompact f.hom.left]
    [IsSeparated g.hom.left] [LocallyOfFiniteType g.hom.left] [QuasiCompact g.hom.left]
    [IsSeparated h.hom.left] [LocallyOfFiniteType h.hom.left] [QuasiCompact h.hom.left]
    (cf : Compactification f.hom.left) (cg : Compactification g.hom.left)
    (ch : Compactification h.hom.left) (cfg : Compactification (f ≫ g).hom.left)
    (cgh : Compactification (g ≫ h).hom.left)
    (cfgh : Compactification ((f ≫ g) ≫ h).hom.left) (K : sfIntegralConstructibleCategory C.l E
      X.obj.left),
    HEq ((S.higher.integral.composition (f ≫ g) h cfg ch cfgh).hom.app K ≫
      (S.higher.integral.support h ch).map ((S.higher.integral.composition f g cf cg cfg).hom.app
        K))
      ((S.higher.integral.composition f (g ≫ h) cf cgh
        (Eq.mp (congrArg (fun t : X ⟶ W ↦ Compactification t.hom.left)
          (Category.assoc f g h)) cfgh)).hom.app K ≫
        (S.higher.integral.composition g h cg ch cgh).hom.app ((S.higher.integral.support f
          cf).obj K))) ∧
    (∀ {X Y Z W : SixFunctorSpace D}
    (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ W)
    [IsSeparated f.hom.left] [LocallyOfFiniteType f.hom.left] [QuasiCompact f.hom.left]
    [IsSeparated g.hom.left] [LocallyOfFiniteType g.hom.left] [QuasiCompact g.hom.left]
    [IsSeparated h.hom.left] [LocallyOfFiniteType h.hom.left] [QuasiCompact h.hom.left]
    (cf : Compactification f.hom.left) (cg : Compactification g.hom.left)
    (ch : Compactification h.hom.left) (cfg : Compactification (f ≫ g).hom.left)
    (cgh : Compactification (g ≫ h).hom.left)
    (cfgh : Compactification ((f ≫ g) ≫ h).hom.left) (K : sfRationalConstructibleCategory C.l E
      X.obj.left),
    HEq ((S.higher.rational.composition (f ≫ g) h cfg ch cfgh).hom.app K ≫
      (S.higher.rational.support h ch).map ((S.higher.rational.composition f g cf cg cfg).hom.app
        K))
      ((S.higher.rational.composition f (g ≫ h) cf cgh
        (Eq.mp (congrArg (fun t : X ⟶ W ↦ Compactification t.hom.left)
          (Category.assoc f g h)) cfgh)).hom.app K ≫
        (S.higher.rational.composition g h cg ch cgh).hom.app ((S.higher.rational.support f
          cf).obj K))) ∧
    (∀ {X Y Z W : SixFunctorSpace D}
    (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ W)
    [IsSeparated f.hom.left] [LocallyOfFiniteType f.hom.left] [QuasiCompact f.hom.left]
    [IsSeparated g.hom.left] [LocallyOfFiniteType g.hom.left] [QuasiCompact g.hom.left]
    [IsSeparated h.hom.left] [LocallyOfFiniteType h.hom.left] [QuasiCompact h.hom.left]
    (cf : Compactification f.hom.left) (cg : Compactification g.hom.left)
    (ch : Compactification h.hom.left) (cfg : Compactification (f ≫ g).hom.left)
    (cgh : Compactification (g ≫ h).hom.left)
    (cfgh : Compactification ((f ≫ g) ≫ h).hom.left) (K :
      generalAlgebraicallyClosedConstructibleCategory C.l C.Qbar X.obj.left),
    HEq ((S.closure.commonStage.composition (f ≫ g) h cfg ch cfgh).hom.app K ≫
      (S.closure.commonStage.support h ch).map ((S.closure.commonStage.composition f g cf cg
        cfg).hom.app K))
      ((S.closure.commonStage.composition f (g ≫ h) cf cgh
        (Eq.mp (congrArg (fun t : X ⟶ W ↦ Compactification t.hom.left)
          (Category.assoc f g h)) cfgh)).hom.app K ≫
        (S.closure.commonStage.composition g h cg ch cgh).hom.app ((S.closure.commonStage.support
          f cf).obj K))) := by
  have h := compactSupportProjection_coherenceLaws S.toSixFunctorOperationDatum
  refine ⟨h.1.pentagon, ?_, ?_, ?_⟩
  · exact h.2.1.pentagon
  · exact h.2.2.1.pentagon
  · exact h.2.2.2.1.pentagon

/-- Proper of the supplied projection maps at all four coefficient stages.
Source: current blueprint prop-sf-pf-coherence, proper clause
(blueprint: prop-sf-pf-coherence).
Proof: Use the identity open compactification. Its open adjunction unit and tensor
map cancel, leaving the proper counit projection. The refinement comparison
intertwines this with the map for an arbitrary compactification. Transport the
identity through the recorded coefficient realizations, keeping the same counit. -/
theorem sixFunctorProjection_proper (S : SixFunctorDatum D C E n hn) :
    (∀ {X Y : SixFunctorSpace D} (f : X ⟶ Y) [IsProper f.hom.left]
    (c : Compactification f.hom.left) (K : sixFunctorFiniteCategory D C E n hn X)
    (L : finiteTorConstructibleCategory C.l E n hn Y.obj.left),
      ((CompactSupportFiniteProjection.partialTensor S.toSixFunctorFiniteOperations Y).map
        ((S.toSixFunctorFiniteOperations.finite.properIdentification f c).hom.app K)).app L ≫
          CompactSupportFiniteProjection.properComponent S.toSixFunctorFiniteOperations f K L =
        CompactSupportFiniteProjection.component S.toSixFunctorFiniteOperations f c K L ≫
          (S.toSixFunctorFiniteOperations.finite.properIdentification f c).hom.app
            (((CompactSupportFiniteProjection.partialTensor S.toSixFunctorFiniteOperations X).obj
              K).obj ((CompactSupportFiniteProjection.torPull S.toSixFunctorFiniteOperations
              f).obj L))) ∧
    (∀ {X Y : SixFunctorSpace D} (f : X ⟶ Y) [IsProper f.hom.left]
    (c : Compactification f.hom.left) (K : sfIntegralConstructibleCategory C.l E X.obj.left) (L :
      sfIntegralConstructibleCategory C.l E Y.obj.left),
      S.toSixFunctorOperationDatum.integralFiniteTorDomain Y L →
      ((S.higher.integralTensor Y).map ((S.higher.integral.properIdentification f c).hom.app
        K)).app L ≫
          compactSupportProperProjection S.higher.integralExchange f K L =
        compactSupportProjectionComponent S.higher.integralExchange f c K L ≫
          (S.higher.integral.properIdentification f c).hom.app
            (((S.higher.integralTensor X).obj K).obj ((S.higher.integral.pull f).obj L))) ∧
    (∀ {X Y : SixFunctorSpace D} (f : X ⟶ Y) [IsProper f.hom.left]
    (c : Compactification f.hom.left) (K : sfRationalConstructibleCategory C.l E X.obj.left) (L :
      sfRationalConstructibleCategory C.l E Y.obj.left), ((S.higher.rationalTensor Y).map
      ((S.higher.rational.properIdentification f c).hom.app
        K)).app L ≫
          compactSupportProperProjection S.higher.rationalExchange f K L =
        compactSupportProjectionComponent S.higher.rationalExchange f c K L ≫
          (S.higher.rational.properIdentification f c).hom.app
            (((S.higher.rationalTensor X).obj K).obj ((S.higher.rational.pull f).obj L))) ∧
    (∀ {X Y : SixFunctorSpace D} (f : X ⟶ Y) [IsProper f.hom.left]
    (c : Compactification f.hom.left) (K : generalAlgebraicallyClosedConstructibleCategory C.l
      C.Qbar X.obj.left) (L : generalAlgebraicallyClosedConstructibleCategory C.l C.Qbar
      Y.obj.left), ((S.closure.commonStageTensor Y).map
      ((S.closure.commonStage.properIdentification f
        c).hom.app K)).app L ≫
          compactSupportProperProjection S.closure.commonStageExchange f K L =
        compactSupportProjectionComponent S.closure.commonStageExchange f c K L ≫
          (S.closure.commonStage.properIdentification f c).hom.app
            (((S.closure.commonStageTensor X).obj K).obj ((S.closure.commonStage.pull f).obj L)))
              := by
  have h := compactSupportProjection_coherenceLaws S.toSixFunctorOperationDatum
  refine ⟨h.1.proper, ?_, ?_, ?_⟩
  · exact h.2.1.proper
  · intro X Y f _ c K L
    exact h.2.2.1.proper f c K L trivial
  · intro X Y f _ c K L
    exact h.2.2.2.1.proper f c K L trivial


/-- Compact-support exchange in the named operation coordinates. Only the endpoint
identifications recorded in the datum are inserted.
Source: current blueprint prop-sf-pf-coherence, vertical arrows
(blueprint: prop-sf-pf-coherence). -/
def sixFunctorProjectionExchange
    {B : SixFunctorSpace D → Type v} [∀ X, Category.{w} (B X)]
    {F : SixFunctorPushStage D B} {T : ∀ X, B X ⥤ B X ⥤ B X}
    {Q : SixFunctorCompactifiedSquare D} (A : SixFunctorExchangeData F T Q)
    (K : B Q.X) :
    (F.pull Q.g).obj ((F.support Q.f Q.compactification).obj K) ⟶
      (F.support Q.f' Q.compactification').obj ((F.pull Q.g').obj K) :=
  eqToHom (congrArg₂ (fun G H ↦ G.obj (H.obj K))
    A.horizontal A.compactSupport).symm ≫
    A.stage.compactExchange.app K ≫
    eqToHom (congrArg₂ (fun H G ↦ H.obj (G.obj K))
      A.compactSupport' A.horizontal')

/-- The canonical integral tensor-pullback comparison in the datum's coordinates.
This conjugates the recorded representative-normalized comparison by the datum's
functor equalities; it introduces no alternative monoidal comparison.
Source: current blueprint prop-sf-pf-coherence, monoidality identifications
(blueprint: prop-sf-pf-coherence). -/
def sixFunctorProjectionIntegralMu (S : SixFunctorDatum D C E n hn)
    {X Y : SixFunctorSpace D} (f : X ⟶ Y)
    (K L : sfIntegralConstructibleCategory C.l E Y.obj.left) :
    (S.higher.integral.pull f).obj (((S.higher.integralTensor Y).obj K).obj L) ≅
      ((S.higher.integralTensor X).obj ((S.higher.integral.pull f).obj K)).obj
        ((S.higher.integral.pull f).obj L) :=
  letI : ∀ x : X.obj.left, Invertible (C.l : X.obj.left.residueField x) :=
    fun x ↦ (map_natCast (X.obj.hom.residueFieldAlgebraMap x) C.l) ▸
      ((PurCompactSupport.coefficientPrimeUnit C.l D C.different).map
        (X.obj.hom.residueFieldAlgebraMap x)).invertible
  letI : ∀ x : Y.obj.left, Invertible (C.l : Y.obj.left.residueField x) :=
    fun x ↦ (map_natCast (Y.obj.hom.residueFieldAlgebraMap x) C.l) ▸
      ((PurCompactSupport.coefficientPrimeUnit C.l D C.different).map
        (Y.obj.hom.residueFieldAlgebraMap x)).invertible
  eqToIso (congrArg₂ (fun F T ↦ F.obj ((T.obj K).obj L))
    (S.higher.integralPullback f) (S.higher.integralTensorNormalization Y)) ≪≫
    canonicalIntegralPullbackTensor C.l E f.hom.left K L ≪≫
    eqToIso (congrArg₂ (fun F T ↦ ((T.obj (F.obj K)).obj (F.obj L)))
      (S.higher.integralPullback f) (S.higher.integralTensorNormalization X)).symm

/-- The displayed base-change square for the integral projection transformation.
Source: current blueprint prop-sf-pf-coherence, displayed square
(blueprint: prop-sf-pf-coherence).
Proof: choose the compactification retained in Q. Apply the open-factor equation
of lem-sf-pf-open-base-change-square. The proper-factor equation is the counit
projection/mate identity lem-sp-categorical-projection-mate-square, since the
canonical pullback square comparison is monoidal. The pasting lemma
lem-sf-pf-compactification-pasting gives the two displayed composites. At integral
coefficients this is an equality of completed arrows before finite evaluation;
rationalization and common-stage inclusion preserve the equality. The recorded
refinement comparisons remove dependence on the chosen compactification. -/
theorem sixFunctorProjection_baseChange_integral (S : SixFunctorDatum D C E n hn) :
    ∀ (Q : SixFunctorCompactifiedSquare D)
      [IsSeparated Q.f.hom.left]
      (K : sfIntegralConstructibleCategory C.l E Q.X.obj.left)
      (L : sfIntegralConstructibleCategory C.l E Q.Y.obj.left),
      S.toSixFunctorOperationDatum.integralFiniteTorDomain Q.Y L →
      (S.higher.integral.pull Q.g).map ((S.higher.integralExchange Q).projectionComponent K L) ≫
        sixFunctorProjectionExchange (S.higher.integralExchange Q)
          (((S.higher.integralTensor Q.X).obj K).obj ((S.higher.integral.pull Q.f).obj L)) ≫
        (S.higher.integral.support Q.f' Q.compactification').map
          ((sixFunctorProjectionIntegralMu S Q.g' K
            ((S.higher.integral.pull Q.f).obj L)).hom ≫
            ((S.higher.integralTensor Q.X').obj ((S.higher.integral.pull Q.g').obj K)).map
              (((S.higher.integral.pullComposition Q.g' Q.f).inv.app L) ≫
                eqToHom (congrArg
                  (fun f ↦ (S.higher.integral.pull f).obj L) Q.squareComm) ≫
                (S.higher.integral.pullComposition Q.f' Q.g).hom.app L)) =
      (sixFunctorProjectionIntegralMu S Q.g
        ((S.higher.integral.support Q.f Q.compactification).obj K) L).hom ≫
        ((S.higher.integralTensor Q.Y').map
          (sixFunctorProjectionExchange (S.higher.integralExchange Q) K)).app
            ((S.higher.integral.pull Q.g).obj L) ≫
        (S.higher.integralExchange (compactSupportProjectionSquare Q.f'
          Q.compactification')).projectionComponent
          ((S.higher.integral.pull Q.g').obj K) ((S.higher.integral.pull Q.g).obj L) := by
  sorry

/-- The canonical rational tensor-pullback comparison in the datum's coordinates.
This conjugates the recorded representative-normalized comparison by the datum's
functor equalities; it introduces no alternative monoidal comparison.
Source: current blueprint prop-sf-pf-coherence, monoidality identifications
(blueprint: prop-sf-pf-coherence). -/
def sixFunctorProjectionRationalMu (S : SixFunctorDatum D C E n hn)
    {X Y : SixFunctorSpace D} (f : X ⟶ Y)
    (K L : sfRationalConstructibleCategory C.l E Y.obj.left) :
    (S.higher.rational.pull f).obj (((S.higher.rationalTensor Y).obj K).obj L) ≅
      ((S.higher.rationalTensor X).obj ((S.higher.rational.pull f).obj K)).obj
        ((S.higher.rational.pull f).obj L) :=
  letI : ∀ x : X.obj.left, Invertible (C.l : X.obj.left.residueField x) :=
    fun x ↦ (map_natCast (X.obj.hom.residueFieldAlgebraMap x) C.l) ▸
      ((PurCompactSupport.coefficientPrimeUnit C.l D C.different).map
        (X.obj.hom.residueFieldAlgebraMap x)).invertible
  letI : ∀ x : Y.obj.left, Invertible (C.l : Y.obj.left.residueField x) :=
    fun x ↦ (map_natCast (Y.obj.hom.residueFieldAlgebraMap x) C.l) ▸
      ((PurCompactSupport.coefficientPrimeUnit C.l D C.different).map
        (Y.obj.hom.residueFieldAlgebraMap x)).invertible
  eqToIso (congrArg₂ (fun F T ↦ F.obj ((T.obj K).obj L))
    (S.higher.rationalPullback f) (S.higher.rationalTensorNormalization Y)) ≪≫
    canonicalRationalPullbackTensor C.l E f.hom.left K L ≪≫
    eqToIso (congrArg₂ (fun F T ↦ ((T.obj (F.obj K)).obj (F.obj L)))
      (S.higher.rationalPullback f) (S.higher.rationalTensorNormalization X)).symm

/-- The displayed base-change square for the rational projection transformation.
Source: current blueprint prop-sf-pf-coherence, displayed square
(blueprint: prop-sf-pf-coherence).
Proof: choose the compactification retained in Q. Apply the open-factor equation
of lem-sf-pf-open-base-change-square. The proper-factor equation is the counit
projection/mate identity lem-sp-categorical-projection-mate-square, since the
canonical pullback square comparison is monoidal. The pasting lemma
lem-sf-pf-compactification-pasting gives the two displayed composites. At integral
coefficients this is an equality of completed arrows before finite evaluation;
rationalization and common-stage inclusion preserve the equality. The recorded
refinement comparisons remove dependence on the chosen compactification. -/
theorem sixFunctorProjection_baseChange_rational (S : SixFunctorDatum D C E n hn) :
    ∀ (Q : SixFunctorCompactifiedSquare D)
      [IsSeparated Q.f.hom.left]
      (K : sfRationalConstructibleCategory C.l E Q.X.obj.left)
      (L : sfRationalConstructibleCategory C.l E Q.Y.obj.left),
      (S.higher.rational.pull Q.g).map ((S.higher.rationalExchange Q).projectionComponent K L) ≫
        sixFunctorProjectionExchange (S.higher.rationalExchange Q)
          (((S.higher.rationalTensor Q.X).obj K).obj ((S.higher.rational.pull Q.f).obj L)) ≫
        (S.higher.rational.support Q.f' Q.compactification').map
          ((sixFunctorProjectionRationalMu S Q.g' K
            ((S.higher.rational.pull Q.f).obj L)).hom ≫
            ((S.higher.rationalTensor Q.X').obj ((S.higher.rational.pull Q.g').obj K)).map
              (((S.higher.rational.pullComposition Q.g' Q.f).inv.app L) ≫
                eqToHom (congrArg
                  (fun f ↦ (S.higher.rational.pull f).obj L) Q.squareComm) ≫
                (S.higher.rational.pullComposition Q.f' Q.g).hom.app L)) =
      (sixFunctorProjectionRationalMu S Q.g
        ((S.higher.rational.support Q.f Q.compactification).obj K) L).hom ≫
        ((S.higher.rationalTensor Q.Y').map
          (sixFunctorProjectionExchange (S.higher.rationalExchange Q) K)).app
            ((S.higher.rational.pull Q.g).obj L) ≫
        (S.higher.rationalExchange (compactSupportProjectionSquare Q.f'
          Q.compactification')).projectionComponent
          ((S.higher.rational.pull Q.g').obj K) ((S.higher.rational.pull Q.g).obj L) := by
  sorry

/-- The canonical common tensor-pullback comparison in the datum's coordinates.
This conjugates the recorded representative-normalized comparison by the datum's
functor equalities; it introduces no alternative monoidal comparison.
Source: current blueprint prop-sf-pf-coherence, monoidality identifications
(blueprint: prop-sf-pf-coherence). -/
def sixFunctorProjectionCommonMu (S : SixFunctorDatum D C E n hn)
    {X Y : SixFunctorSpace D} (f : X ⟶ Y)
    (K L : generalAlgebraicallyClosedConstructibleCategory C.l C.Qbar Y.obj.left) :
    (S.closure.commonStage.pull f).obj (((S.closure.commonStageTensor Y).obj K).obj L) ≅
      ((S.closure.commonStageTensor X).obj ((S.closure.commonStage.pull f).obj K)).obj
        ((S.closure.commonStage.pull f).obj L) :=
  letI : ∀ x : X.obj.left, Invertible (C.l : X.obj.left.residueField x) :=
    fun x ↦ (map_natCast (X.obj.hom.residueFieldAlgebraMap x) C.l) ▸
      ((PurCompactSupport.coefficientPrimeUnit C.l D C.different).map
        (X.obj.hom.residueFieldAlgebraMap x)).invertible
  letI : ∀ x : Y.obj.left, Invertible (C.l : Y.obj.left.residueField x) :=
    fun x ↦ (map_natCast (Y.obj.hom.residueFieldAlgebraMap x) C.l) ▸
      ((PurCompactSupport.coefficientPrimeUnit C.l D C.different).map
        (Y.obj.hom.residueFieldAlgebraMap x)).invertible
  eqToIso (congrArg₂ (fun F T ↦ F.obj ((T.obj K).obj L))
    (S.closure.commonStagePullback f) (S.closure.commonStageTensorNormalization Y)) ≪≫
    canonicalCommonStagePullbackTensor C.l C.Qbar f.hom.left K L ≪≫
    eqToIso (congrArg₂ (fun F T ↦ ((T.obj (F.obj K)).obj (F.obj L)))
      (S.closure.commonStagePullback f) (S.closure.commonStageTensorNormalization X)).symm

/-- The displayed base-change square for the common projection transformation.
Source: current blueprint prop-sf-pf-coherence, displayed square
(blueprint: prop-sf-pf-coherence).
Proof: choose the compactification retained in Q. Apply the open-factor equation
of lem-sf-pf-open-base-change-square. The proper-factor equation is the counit
projection/mate identity lem-sp-categorical-projection-mate-square, since the
canonical pullback square comparison is monoidal. The pasting lemma
lem-sf-pf-compactification-pasting gives the two displayed composites. At integral
coefficients this is an equality of completed arrows before finite evaluation;
rationalization and common-stage inclusion preserve the equality. The recorded
refinement comparisons remove dependence on the chosen compactification. -/
theorem sixFunctorProjection_baseChange_common (S : SixFunctorDatum D C E n hn) :
    ∀ (Q : SixFunctorCompactifiedSquare D)
      [IsSeparated Q.f.hom.left]
      (K : generalAlgebraicallyClosedConstructibleCategory C.l C.Qbar Q.X.obj.left)
      (L : generalAlgebraicallyClosedConstructibleCategory C.l C.Qbar Q.Y.obj.left),
      (S.closure.commonStage.pull Q.g).map ((S.closure.commonStageExchange Q).projectionComponent
        K L) ≫
        sixFunctorProjectionExchange (S.closure.commonStageExchange Q)
          (((S.closure.commonStageTensor Q.X).obj K).obj ((S.closure.commonStage.pull Q.f).obj L)) ≫
        (S.closure.commonStage.support Q.f' Q.compactification').map
          ((sixFunctorProjectionCommonMu S Q.g' K
            ((S.closure.commonStage.pull Q.f).obj L)).hom ≫
            ((S.closure.commonStageTensor Q.X').obj ((S.closure.commonStage.pull Q.g').obj K)).map
              (((S.closure.commonStage.pullComposition Q.g' Q.f).inv.app L) ≫
                eqToHom (congrArg
                  (fun f ↦ (S.closure.commonStage.pull f).obj L) Q.squareComm) ≫
                (S.closure.commonStage.pullComposition Q.f' Q.g).hom.app L)) =
      (sixFunctorProjectionCommonMu S Q.g
        ((S.closure.commonStage.support Q.f Q.compactification).obj K) L).hom ≫
        ((S.closure.commonStageTensor Q.Y').map
          (sixFunctorProjectionExchange (S.closure.commonStageExchange Q) K)).app
            ((S.closure.commonStage.pull Q.g).obj L) ≫
        (S.closure.commonStageExchange (compactSupportProjectionSquare Q.f'
          Q.compactification')).projectionComponent
          ((S.closure.commonStage.pull Q.g').obj K) ((S.closure.commonStage.pull Q.g).obj L) := by
  sorry


/-- Identity support comparison obtained from the specified proper identification
and the right-adjoint mate of the identity pullback comparison.
Source: the identity clause of the current blueprint prop-sf-pf-coherence
(blueprint: prop-sf-pf-coherence). -/
def sixFunctorProjectionIdentitySupport
    {B : SixFunctorSpace D → Type v} [∀ X, Category.{w} (B X)]
    (F : SixFunctorPushStage D B) (X : SixFunctorSpace D)
    (e : F.pull (𝟙 X) ≅ 𝟭 (B X))
    (c : Compactification (𝟙 X : X ⟶ X).hom.left) : F.support (𝟙 X) c ≅ 𝟭 (B X) :=
  F.properIdentification (𝟙 X) c ≪≫
    ((F.pullDirectAdjunction (𝟙 X)).ofNatIsoLeft e).rightAdjointUniq Adjunction.id

/-- The finite-Tor restriction of the very same identity pullback comparison.
Source: identity clause of the current blueprint prop-sf-pf-coherence
(blueprint: prop-sf-pf-coherence). -/
def sixFunctorProjectionTorIdentity
    (S : SixFunctorDatum D C E n hn) (X : SixFunctorSpace D)
    (e : S.finite.pull (𝟙 X) ≅ 𝟭 (sixFunctorFiniteCategory D C E n hn X))
    (L : finiteTorConstructibleCategory C.l E n hn X.obj.left) :
    (CompactSupportFiniteProjection.torPull S.toSixFunctorFiniteOperations (𝟙 X)).obj L ≅ L :=
  ObjectProperty.isoMk _
    ((intrinsicFiniteTorsionConstructible C.l E n hn X.obj.left).ι.mapIso
      (e.app ⟨L.obj, L.property.1⟩))

private theorem identitySupport_eq
    {B : SixFunctorSpace D → Type v} [∀ X, Category.{w} (B X)]
    (F : SixFunctorPushStage D B) (X : SixFunctorSpace D)
    (e : F.pull (𝟙 X) ≅ 𝟭 (B X))
    (c : Compactification (𝟙 X : X ⟶ X).hom.left) :
    sixFunctorProjectionIdentitySupport F X e c =
      F.properIdentification (𝟙 X) c ≪≫
        ((F.pullDirectAdjunction (𝟙 X)).ofNatIsoLeft e).rightAdjointUniq Adjunction.id := by
  rfl

private theorem identityTor_eq
    (S : SixFunctorDatum D C E n hn) (X : SixFunctorSpace D)
    (e : S.finite.pull (𝟙 X) ≅ 𝟭 (sixFunctorFiniteCategory D C E n hn X))
    (L : finiteTorConstructibleCategory C.l E n hn X.obj.left) :
    sixFunctorProjectionTorIdentity S X e L =
      ObjectProperty.isoMk (finiteTorConstructible C.l E n hn X.obj.left)
        (X := (CompactSupportFiniteProjection.torPull
          S.toSixFunctorFiniteOperations (𝟙 X)).obj L) (Y := L)
        ((intrinsicFiniteTorsionConstructible C.l E n hn X.obj.left).ι.mapIso
          (e.app ⟨L.obj, L.property.1⟩)) := by
  rfl

/-- Identity coherence, with the unit characterized by the supplied compositor.
The unique unit is asserted, rather than an arbitrary endpoint identification being
assumed. The support identity is its specified adjunction mate. The displayed
triangle is precisely PF = identity after these identity identifications.
Source: current blueprint prop-sf-pf-coherence, identity clause
(blueprint: prop-sf-pf-coherence).
Proof: use the normalized identity inverse image and its adjunction mate. The
identity specialization of the compositor characterizes this unit uniquely.
At the identity-open/proper compactification the counit transpose and open-unit
transpose are the identity tensor map. Compactification compatibility transports
this equation to every c. The finite full inclusion reflects the equation; at
integral coefficients use the whole-system units before evaluation. Localize
that equation and pass to common stages for the two field clauses. -/
theorem sixFunctorProjection_identity (S : SixFunctorDatum D C E n hn) :
    (∀ X : SixFunctorSpace D,
      ∃! e : S.finite.pull (𝟙 X) ≅ 𝟭 (sixFunctorFiniteCategory D C E n hn X),
        (∀ M : sixFunctorFiniteCategory D C E n hn X,
          (S.finite.pullComposition (𝟙 X) (𝟙 X)).hom.app M ≫
              e.hom.app ((S.finite.pull (𝟙 X)).obj M) =
            eqToHom (congrArg (fun f ↦ (S.finite.pull f).obj M)
              (Category.id_comp (𝟙 X)))) ∧
        ∀ (c : Compactification (𝟙 X : X ⟶ X).hom.left) (K : sixFunctorFiniteCategory D C E n hn X)
          (L : finiteTorConstructibleCategory C.l E n hn X.obj.left),
          CompactSupportFiniteProjection.component S.toSixFunctorFiniteOperations (𝟙 X) c K L ≫
            (sixFunctorProjectionIdentitySupport S.finite X e c).hom.app
              (((CompactSupportFiniteProjection.partialTensor S.toSixFunctorFiniteOperations
          X).obj K).obj ((CompactSupportFiniteProjection.torPull S.toSixFunctorFiniteOperations
          (𝟙 X)).obj L)) ≫
            ((CompactSupportFiniteProjection.partialTensor S.toSixFunctorFiniteOperations X).obj
          K).map (sixFunctorProjectionTorIdentity S X e L).hom =
          ((CompactSupportFiniteProjection.partialTensor S.toSixFunctorFiniteOperations X).map
            ((sixFunctorProjectionIdentitySupport S.finite X e c).hom.app K)).app L) ∧
    (∀ X : SixFunctorSpace D,
      ∃! e : S.higher.integral.pull (𝟙 X) ≅ 𝟭 (sfIntegralConstructibleCategory C.l E X.obj.left),
        (∀ M : sfIntegralConstructibleCategory C.l E X.obj.left,
          (S.higher.integral.pullComposition (𝟙 X) (𝟙 X)).hom.app M ≫
              e.hom.app ((S.higher.integral.pull (𝟙 X)).obj M) =
            eqToHom (congrArg (fun f ↦ (S.higher.integral.pull f).obj M)
              (Category.id_comp (𝟙 X)))) ∧
        ∀ (c : Compactification (𝟙 X : X ⟶ X).hom.left) (K : sfIntegralConstructibleCategory C.l E
          X.obj.left)
          (L : sfIntegralConstructibleCategory C.l E X.obj.left),
          S.toSixFunctorOperationDatum.integralFiniteTorDomain X L →
          compactSupportProjectionComponent S.higher.integralExchange (𝟙 X) c K L ≫
            (sixFunctorProjectionIdentitySupport S.higher.integral X e c).hom.app
              (((S.higher.integralTensor X).obj K).obj ((S.higher.integral.pull (𝟙 X)).obj L)) ≫
            ((S.higher.integralTensor X).obj K).map (e.app L).hom =
          ((S.higher.integralTensor X).map
            ((sixFunctorProjectionIdentitySupport S.higher.integral X e c).hom.app K)).app L) ∧
    (∀ X : SixFunctorSpace D,
      ∃! e : S.higher.rational.pull (𝟙 X) ≅ 𝟭 (sfRationalConstructibleCategory C.l E X.obj.left),
        (∀ M : sfRationalConstructibleCategory C.l E X.obj.left,
          (S.higher.rational.pullComposition (𝟙 X) (𝟙 X)).hom.app M ≫
              e.hom.app ((S.higher.rational.pull (𝟙 X)).obj M) =
            eqToHom (congrArg (fun f ↦ (S.higher.rational.pull f).obj M)
              (Category.id_comp (𝟙 X)))) ∧
        ∀ (c : Compactification (𝟙 X : X ⟶ X).hom.left) (K : sfRationalConstructibleCategory C.l E
          X.obj.left)
          (L : sfRationalConstructibleCategory C.l E X.obj.left),
          compactSupportProjectionComponent S.higher.rationalExchange (𝟙 X) c K L ≫
            (sixFunctorProjectionIdentitySupport S.higher.rational X e c).hom.app
              (((S.higher.rationalTensor X).obj K).obj ((S.higher.rational.pull (𝟙 X)).obj L)) ≫
            ((S.higher.rationalTensor X).obj K).map (e.app L).hom =
          ((S.higher.rationalTensor X).map
            ((sixFunctorProjectionIdentitySupport S.higher.rational X e c).hom.app K)).app L) ∧
    (∀ X : SixFunctorSpace D,
      ∃! e : S.closure.commonStage.pull (𝟙 X) ≅ 𝟭
          (generalAlgebraicallyClosedConstructibleCategory C.l C.Qbar X.obj.left),
        (∀ M : generalAlgebraicallyClosedConstructibleCategory C.l C.Qbar X.obj.left,
          (S.closure.commonStage.pullComposition (𝟙 X) (𝟙 X)).hom.app M ≫
              e.hom.app ((S.closure.commonStage.pull (𝟙 X)).obj M) =
            eqToHom (congrArg (fun f ↦ (S.closure.commonStage.pull f).obj M)
              (Category.id_comp (𝟙 X)))) ∧
        ∀ (c : Compactification (𝟙 X : X ⟶ X).hom.left) (K :
          generalAlgebraicallyClosedConstructibleCategory C.l C.Qbar X.obj.left)
          (L : generalAlgebraicallyClosedConstructibleCategory C.l C.Qbar X.obj.left),
          compactSupportProjectionComponent S.closure.commonStageExchange (𝟙 X) c K L ≫
            (sixFunctorProjectionIdentitySupport S.closure.commonStage X e c).hom.app
              (((S.closure.commonStageTensor X).obj K).obj ((S.closure.commonStage.pull (𝟙
          X)).obj L)) ≫
            ((S.closure.commonStageTensor X).obj K).map (e.app L).hom =
          ((S.closure.commonStageTensor X).map
            ((sixFunctorProjectionIdentitySupport S.closure.commonStage X e c).hom.app K)).app L)
          := by
  simp only [identitySupport_eq, identityTor_eq]
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact projectionIdentity_finite S.toSixFunctorOperationDatum
  · exact projectionIdentity_integral S.toSixFunctorOperationDatum
  · exact projectionIdentity_rational S.toSixFunctorOperationDatum
  · exact projectionIdentity_common S.toSixFunctorOperationDatum

/-- The finite projection is carried by the prescribed pro-etale realization to
the same proper-counit/open projection, on the full bounded constructible first
input. The source and target are the recorded realization comparisons.
Source: current blueprint prop-sf-pf-coherence, pro-etale realization clause
(blueprint: prop-sf-pf-coherence).
Proof: unfold the finite component as full-subcategory conjugation. Its defining
full inclusion equation is exactly this equality. The comparisons cancel the
coefficient equivalence unit and counit. Thus this
identification preserves the coherence equalities, not merely invertibility. -/
theorem sixFunctorProjection_realization (S : SixFunctorDatum D C E n hn)
    {X Y : SixFunctorSpace D} (f : X ⟶ Y)
    (c : Compactification f.hom.left) (K : sixFunctorFiniteCategory D C E n hn X)
    (L : finiteTorConstructibleCategory C.l E n hn Y.obj.left) :
    (intrinsicFiniteTorsionConstructible C.l E n hn Y.obj.left).ι.map
        (CompactSupportFiniteProjection.component S.toSixFunctorFiniteOperations f c K L) ≫
      (CompactSupportFiniteProjection.targetComparison
        S.toSixFunctorFiniteOperations f c K L).hom =
    (CompactSupportFiniteProjection.sourceComparison
      S.toSixFunctorFiniteOperations f c K L).hom ≫
      (CompactSupportFiniteProjection.realization (C := C) (E := E) (n := n) (hn := hn)
        Y).functor.map
        (CompactSupportFiniteProjection.fixedComponent (C := C) (E := E) (n := n) (hn := hn)
          f c ((CompactSupportFiniteProjection.realization (C := C) (E := E) (n := n)
            (hn := hn) X).inverse.obj K.obj)
          ((CompactSupportFiniteProjection.realization (C := C) (E := E) (n := n)
            (hn := hn) Y).inverse.obj L.obj)) := by
  change (_ ≫ _ ≫ (CompactSupportFiniteProjection.targetComparison
    S.toSixFunctorFiniteOperations f c K L).inv) ≫ _ = _
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]



section
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

/-- The finite base-change square for the datum's projection and its A2 exchange.
Source: current blueprint prop-sf-pf-coherence, displayed square
(blueprint: prop-sf-pf-coherence).
Proof: write the supplied maps as the proper counit mate followed by the open tensor
map. The monoidal pullback compositor identifies the transposes of the proper-factor
routes. Restriction to the open identifies both open-factor routes with the same
unit-normalized tensor map. Paste these equalities and conjugate by finitePullback,
finiteSupport and the specified coefficient equivalence. The bottom compactification
is the Cartesian base change; refinement naturality gives every other choice. -/
theorem sixFunctorProjection_baseChange_finite (S : SixFunctorDatum D C E n hn)
    (Q : SixFunctorCompactifiedSquare D) [IsSeparated Q.f.hom.left]
    (K : sixFunctorFiniteCategory D C E n hn Q.X)
    (L : finiteTorConstructibleCategory C.l E n hn Q.Y.obj.left) :
    (S.finite.pull Q.g).map
      (CompactSupportFiniteProjection.component S.toSixFunctorFiniteOperations
        Q.f Q.compactification K L) ≫
      sixFunctorProjectionFiniteExchange S Q
        (((CompactSupportFiniteProjection.partialTensor S.toSixFunctorFiniteOperations Q.X).obj
          K).obj ((CompactSupportFiniteProjection.torPull S.toSixFunctorFiniteOperations
            Q.f).obj L)) ≫
      (S.finite.support Q.f' (Q.compactification.ofIsPullback Q.square)).map
        ((sixFunctorProjectionFiniteMu S Q.g' K
          ((CompactSupportFiniteProjection.torPull S.toSixFunctorFiniteOperations Q.f).obj
            L)).hom ≫
          ((CompactSupportFiniteProjection.partialTensor S.toSixFunctorFiniteOperations Q.X').obj
            ((S.finite.pull Q.g').obj K)).map
            ((CompactSupportFiniteProjection.torPullComposition S.toSixFunctorFiniteOperations
              Q.g' Q.f L).inv ≫
              ObjectProperty.homMk (eqToHom (congrArg
                (fun f ↦ ((CompactSupportFiniteProjection.torPull
                  S.toSixFunctorFiniteOperations f).obj L).obj) Q.squareComm)) ≫
              (CompactSupportFiniteProjection.torPullComposition S.toSixFunctorFiniteOperations
                Q.f' Q.g L).hom)) =
    (sixFunctorProjectionFiniteMu S Q.g
      ((S.finite.support Q.f Q.compactification).obj K) L).hom ≫
      ((CompactSupportFiniteProjection.partialTensor S.toSixFunctorFiniteOperations Q.Y').map
        (sixFunctorProjectionFiniteExchange S Q K)).app
          ((CompactSupportFiniteProjection.torPull S.toSixFunctorFiniteOperations Q.g).obj L) ≫
      CompactSupportFiniteProjection.component S.toSixFunctorFiniteOperations Q.f'
        (Q.compactification.ofIsPullback Q.square) ((S.finite.pull Q.g').obj K)
        ((CompactSupportFiniteProjection.torPull S.toSixFunctorFiniteOperations Q.g).obj L) := by
  exact sixFunctorProjectionFinite_baseChange_transport S Q K L


end

/-- The datum's finite projection in fixed-scalar coordinates. This is the actual
full-subcategory component, conjugated by its two recorded realization comparisons.
Source: current blueprint prop-sf-pf-coherence, finite reduction square
(blueprint: prop-sf-pf-coherence). -/
def sixFunctorProjectionFiniteInFixedCoordinates (S : SixFunctorDatum D C E n hn)
    {X Y : SixFunctorSpace D} (f : X ⟶ Y) (c : Compactification f.hom.left)
    (K : sixFunctorFiniteCategory D C E n hn X)
    (L : finiteTorConstructibleCategory C.l E n hn Y.obj.left) :=
  let R := CompactSupportFiniteProjection.realization
    (C := C) (E := E) (n := n) (hn := hn) Y
  (R.unitIso.app _).hom ≫
    R.inverse.map
      ((CompactSupportFiniteProjection.sourceComparison
        S.toSixFunctorFiniteOperations f c K L).inv ≫
        (intrinsicFiniteTorsionConstructible C.l E n hn Y.obj.left).ι.map
          (CompactSupportFiniteProjection.component S.toSixFunctorFiniteOperations f c K L) ≫
        (CompactSupportFiniteProjection.targetComparison
          S.toSixFunctorFiniteOperations f c K L).hom) ≫
    (R.unitIso.app _).inv

section
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [local instance high] SymmetricCategory.toBraidedCategory
attribute [local instance 20000] AlgebraicGeometry.ProEtale.sheafBraidedCategory

/-- The all-ideal reduction square for the datum's finite projection.
Reduction is retained as an endofunctor on the original coefficient category:
right tensor with the degree-zero constant quotient. The target reduction uses
the pullback of that quotient, canonically the constant quotient on X. The lower
projection is the same counit/open formula on the ambient derived category; this
retains nonperfect quotients whose reduction need not lie in the finite-Tor domain.
Source: current blueprint prop-sf-pf-coherence, last clause, and
prop-sf-pf-reduction (1) (blueprint: prop-sf-pf-coherence). -/
def sixFunctorProjectionFiniteReductionSquare (S : SixFunctorDatum D C E n hn)
    {X Y : SixFunctorSpace D} (f : X ⟶ Y) (c : Compactification f.hom.left)
    (K : sixFunctorFiniteCategory D C E n hn X)
    (L : finiteTorConstructibleCategory C.l E n hn Y.obj.left)
    (J : Ideal (ULift.{u + 1} (Padic.coefficientExtensionRing C.l E n))) : Prop :=
  -- Construct the equation before specializing its coefficient instances.
  let square (A : Type (u + 2)) [Category.{u + 1} A] [Abelian A]
      [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
      [SymmetricCategory A] [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
      [UpperStarPreservesFlat A]
      {X Y : Scheme.{u}} (f : X ⟶ Y) (c : Compactification f)
      (k : DerivedCategory (Sheaf (ProEt.topology X) A))
      (q N : DerivedCategory (Sheaf (ProEt.topology Y) A))
      (v : ((derivedTensor A Y).obj
          ((rightDerivedLowerShriekOfCompactification A c).obj k)).obj q ⟶
        (rightDerivedLowerShriekOfCompactification A c).obj
          (((derivedTensor A X).obj k).obj ((upperStar A f).leftDerivedFunctor.obj q))) :=
    let TX := derivedTensor A X
    let TY := derivedTensor A Y
    let F := rightDerivedLowerShriekOfCompactification A c
    let U := (upperStar A f).leftDerivedFunctor
    (TY.flip.obj N).map v ≫
        projectionTensorCoordinateComponent A c ((TX.obj k).obj (U.obj q)) N =
      (projectionActionAssociator A Y (F.obj k) q N).hom ≫
        projectionTensorCoordinateComponent A c k ((TY.obj q).obj N) ≫
        F.map ((TX.obj k).map (leftDerivedUpperStarTensorIso A f q N).hom) ≫
        F.map (projectionActionAssociator A X k (U.obj q) (U.obj N)).inv
  letI := Padic.finite_coefficientExtensionRing C.l E n hn
  let A := ULift.{u + 1} (Padic.coefficientExtensionRing C.l E n)
  let RX := CompactSupportFiniteProjection.realization
    (C := C) (E := E) (n := n) (hn := hn) X
  let RY := CompactSupportFiniteProjection.realization
    (C := C) (E := E) (n := n) (hn := hn) Y
  let k := RX.inverse.obj K.obj
  let q := RY.inverse.obj L.obj
  let N := DerivedCategory.Q.obj ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj
    ((constantSheaf (ProEt.topology Y.obj.left) (ModuleCat.{u + 1} A)).obj
      (ModuleCat.of A (A ⧸ J))))
  square (ModuleCat.{u + 1} A) f.hom.left c k q N
    (sixFunctorProjectionFiniteInFixedCoordinates S f c K L)

section
set_option Elab.async false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true


-- Retain the named functors when comparing their object and map fields.
attribute [local irreducible]
  Functor.mapDerivedCategory Functor.rightDerivedFunctor
  Functor.leftDerivedFunctor AlgebraicGeometry.ProEtale.derivedTensor
  AlgebraicGeometry.ProEtale.projectionMapOfCompactification
  AlgebraicGeometry.ProEtale.projectionActionAssociator
  AlgebraicGeometry.ProEtale.leftDerivedUpperStarTensorIso

-- Proof irrelevance identifies the proposition-valued instance arguments directly.
set_option linter.auxLemma false in
private theorem fixedComponent_eq
    [_hGroth : IsGrothendieckAbelian.{u + 1}
      (ModuleCat.{u + 1} (ULift.{u + 1} (Padic.coefficientExtensionRing C.l E n)))]
    [_hMonoidal : MonoidalPreadditive
      (ModuleCat.{u + 1} (ULift.{u + 1} (Padic.coefficientExtensionRing C.l E n)))]
    [_hResolution : Abelian.HasFunctorialFlatResolution
      (ModuleCat.{u + 1} (ULift.{u + 1} (Padic.coefficientExtensionRing C.l E n)))]
    [_hFlat : UpperStarPreservesFlat
      (ModuleCat.{u + 1} (ULift.{u + 1} (Padic.coefficientExtensionRing C.l E n)))]
    {X Y : SixFunctorSpace D} (f : X ⟶ Y)
    [IsSeparated f.hom.left] [LocallyOfFiniteType f.hom.left] [QuasiCompact f.hom.left]
    (c : Compactification f.hom.left)
    (k : DerivedCategory (Sheaf (ProEt.topology X.obj.left)
      (ModuleCat.{u + 1} (ULift.{u + 1} (Padic.coefficientExtensionRing C.l E n)))))
    (q : DerivedCategory (Sheaf (ProEt.topology Y.obj.left)
      (ModuleCat.{u + 1} (ULift.{u + 1} (Padic.coefficientExtensionRing C.l E n))))) :
    CompactSupportFiniteProjection.fixedComponent
      (C := C) (E := E) (n := n) (hn := hn) f c k q =
      projectionTensorCoordinateComponent
        (ModuleCat.{u + 1} (ULift.{u + 1}
          (Padic.coefficientExtensionRing C.l E n))) c k q := by
  rfl

private theorem equivalence_preimage_from_comparisons
    {A : Type*} {B : Type*} [Category* A] [Category* B]
    (R : A ≌ B) {a b : A} {a' b' : B}
    (e : a' ≅ R.functor.obj a) (e' : b' ≅ R.functor.obj b)
    (v : a' ⟶ b') (w : a ⟶ b)
    (h : v ≫ e'.hom = e.hom ≫ R.functor.map w) :
    (R.unitIso.app a).hom ≫ R.inverse.map (e.inv ≫ v ≫ e'.hom) ≫
      (R.unitIso.app b).inv = w := by
  have hc := congrArg (fun t ↦ e.inv ≫ t) h
  simp only [Iso.inv_hom_id_assoc] at hc
  rw [hc]
  exact R.fullyFaithfulFunctor.preimage_map w

/-- Finite reduction commutes with the datum's projection for every ideal, including
zero, the unit ideal, and nonperfect quotients. Source: current blueprint
prop-sf-pf-coherence, final clause; prop-sf-pf-reduction (1)
(blueprint: prop-sf-pf-coherence).
Proof: conjugate the actual component by its specified source and target comparisons.
The proper counit projection is associative with right tensoring; monoidality of
pullback identifies the target reassociation. The open tensor map has the same
associativity on pure tensors, so composing the proper and open equations gives
the displayed reduction square. The constant inverse-image comparison identifies
the pulled-back quotient with the quotient on X. No quotient flatness is used;
the ambient lower component retains cases outside the bounded finite-Tor domain. -/
theorem sixFunctorProjection_reduction_finite (S : SixFunctorDatum D C E n hn)
    {X Y : SixFunctorSpace D} (f : X ⟶ Y) [IsSeparated f.hom.left]
    (c : Compactification f.hom.left) (K : sixFunctorFiniteCategory D C E n hn X)
    (L : finiteTorConstructibleCategory C.l E n hn Y.obj.left)
    (J : Ideal (ULift.{u + 1} (Padic.coefficientExtensionRing C.l E n))) :
    sixFunctorProjectionFiniteReductionSquare S f c K L J := by
  have hgeometry := projectionGeometry (D := D) f c
  let : LocallyOfFiniteType f.hom.left := hgeometry.1
  let : QuasiCompact f.hom.left := hgeometry.2
  delta sixFunctorProjectionFiniteReductionSquare
  -- Elaboration may retain or eliminate the proof-valued finite-ring let instance.
  first
  | extract_lets square finite A RX RY k q N
    guard_hyp A : Type (u + 1)
  | extract_lets square A RX RY k q N
  dsimp only [square]
  let TX := derivedTensor (ModuleCat.{u + 1} A) X.obj.left
  let TY := derivedTensor (ModuleCat.{u + 1} A) Y.obj.left
  let F := rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c
  let U := CompactSupportFiniteProjection.fixedDerivedPull
    (C := C) (E := E) (n := n) f
  let := Padic.finite_coefficientExtensionRing C.l E n hn
  have hfixed : sixFunctorProjectionFiniteInFixedCoordinates S f c K L =
      CompactSupportFiniteProjection.fixedComponent
        (C := C) (E := E) (n := n) (hn := hn) f c k q := by
    dsimp only [sixFunctorProjectionFiniteInFixedCoordinates]
    exact equivalence_preimage_from_comparisons RY
      (CompactSupportFiniteProjection.sourceComparison
        S.toSixFunctorFiniteOperations f c K L)
      (CompactSupportFiniteProjection.targetComparison
        S.toSixFunctorFiniteOperations f c K L)
      ((intrinsicFiniteTorsionConstructible C.l E n hn Y.obj.left).ι.map
        (CompactSupportFiniteProjection.component
          S.toSixFunctorFiniteOperations f c K L))
      (CompactSupportFiniteProjection.fixedComponent
        (C := C) (E := E) (n := n) (hn := hn) f c k q)
      (sixFunctorProjection_realization S f c K L)
  have hcanonical : sixFunctorProjectionFiniteInFixedCoordinates S f c K L =
      projectionTensorCoordinateComponent (ModuleCat.{u + 1} A) c k q :=
    hfixed.trans (fixedComponent_eq (C := C) (E := E) (n := n) (hn := hn) f c k q)
  refine Eq.trans (congrArg (fun t ↦
    (TY.flip.obj N).map t ≫
      projectionTensorCoordinateComponent (ModuleCat.{u + 1} A) c
        ((TX.obj k).obj (U.obj q)) N) hcanonical) ?_
  exact projectionTensorCoordinateComponent_tensorAction (ModuleCat.{u + 1} A) f.hom.left c k q N

end

end

/-- Transport the prescribed tensor associator through the datum's tensor equality.
Source: current blueprint prop-sf-pf-coherence, reduction associativity comparison
(blueprint: prop-sf-pf-coherence). -/
def sixFunctorProjectionTensorAssociator {B : Type v} [Category.{w} B]
    (T T₀ : B ⥤ B ⥤ B) (h : T = T₀)
    (a : ∀ K L N : B, ((T₀.obj ((T₀.obj K).obj L)).obj N) ≅
      ((T₀.obj K).obj ((T₀.obj L).obj N))) (K L N : B) :
    ((T.obj ((T.obj K).obj L)).obj N) ≅ ((T.obj K).obj ((T.obj L).obj N)) :=
  eqToIso (congrArg (fun T ↦ (T.obj ((T.obj K).obj L)).obj N) h) ≪≫
    a K L N ≪≫
    (eqToIso (congrArg (fun T ↦ (T.obj K).obj ((T.obj L).obj N)) h)).symm

/-- The completed or field reduction square, expressed for right tensor with any
constructible coefficient object N. In particular this includes the constant
quotient by every ideal (and the zero and unit quotients). Pullback of N supplies
the coefficient object on X, with its canonical monoidal identification.
Source: current blueprint prop-sf-pf-coherence, finite reduction clause;
prop-sf-pf-reduction (1) (blueprint: prop-sf-pf-coherence). -/
def sixFunctorProjectionIntegralReductionSquare
    (S : SixFunctorDatum D C E n hn) {X Y : SixFunctorSpace D} (f : X ⟶ Y)
    (c : Compactification f.hom.left) (K : sfIntegralConstructibleCategory C.l E X.obj.left)
    (L N : sfIntegralConstructibleCategory C.l E Y.obj.left) : Prop :=
  letI : ∀ x : X.obj.left, Invertible (C.l : X.obj.left.residueField x) :=
    fun x ↦ (map_natCast (X.obj.hom.residueFieldAlgebraMap x) C.l) ▸
      ((PurCompactSupport.coefficientPrimeUnit C.l D C.different).map
        (X.obj.hom.residueFieldAlgebraMap x)).invertible
  letI : ∀ y : Y.obj.left, Invertible (C.l : Y.obj.left.residueField y) :=
    fun y ↦ (map_natCast (Y.obj.hom.residueFieldAlgebraMap y) C.l) ▸
      ((PurCompactSupport.coefficientPrimeUnit C.l D C.different).map
        (Y.obj.hom.residueFieldAlgebraMap y)).invertible
  let TX := S.higher.integralTensor X
  let TY := S.higher.integralTensor Y
  let F := S.higher.integral.support f c
  let U := S.higher.integral.pull f
  let aX := sixFunctorProjectionTensorAssociator TX _ (S.higher.integralTensorNormalization X)
    (pullbackTensorIntegralAssociator C.l E X.obj.left)
  let aY := sixFunctorProjectionTensorAssociator TY _ (S.higher.integralTensorNormalization Y)
    (pullbackTensorIntegralAssociator C.l E Y.obj.left)
  (TY.flip.obj N).map (compactSupportProjectionComponent S.higher.integralExchange f c K L) ≫
      compactSupportProjectionComponent S.higher.integralExchange f c
        ((TX.obj K).obj (U.obj L)) N =
    (aY (F.obj K) L N).hom ≫
      compactSupportProjectionComponent S.higher.integralExchange f c K ((TY.obj L).obj N) ≫
      F.map ((TX.obj K).map (sixFunctorProjectionIntegralMu S f L N).hom) ≫
      F.map (aX K (U.obj L) (U.obj N)).inv

/-- Finite-reduction compatibility for the datum's integral projection maps.
Right tensor by the constant quotient is reduction kept in the original coefficient
category, as in prop-sf-pf-reduction. The displayed identity is stated for all N,
so it also retains the identity and zero reductions.
Source: current blueprint prop-sf-pf-coherence, final clause
(blueprint: prop-sf-pf-coherence).
Proof: the proper counit projection satisfies tensor associativity by transposing
both composites. The open unit tensor comparison satisfies the same identity on
pure tensors. Paste them. At the integral stage retain this equation on coherent
systems and their completion units before applying Rlim. Localization and a common
finite coefficient field preserve it, with the specified tensor associators. -/
theorem sixFunctorProjection_reduction_integral (S : SixFunctorDatum D C E n hn)
    {X Y : SixFunctorSpace D} (f : X ⟶ Y) [IsSeparated f.hom.left]
    (c : Compactification f.hom.left) (K : sfIntegralConstructibleCategory C.l E X.obj.left)
    (L N : sfIntegralConstructibleCategory C.l E Y.obj.left) :
    sixFunctorProjectionIntegralReductionSquare S f c K L N := by
  sorry

/-- The completed or field reduction square, expressed for right tensor with any
constructible coefficient object N. In particular this includes the constant
quotient by every ideal (and the zero and unit quotients). Pullback of N supplies
the coefficient object on X, with its canonical monoidal identification.
Source: current blueprint prop-sf-pf-coherence, finite reduction clause;
prop-sf-pf-reduction (1) (blueprint: prop-sf-pf-coherence). -/
def sixFunctorProjectionRationalReductionSquare
    (S : SixFunctorDatum D C E n hn) {X Y : SixFunctorSpace D} (f : X ⟶ Y)
    (c : Compactification f.hom.left) (K : sfRationalConstructibleCategory C.l E X.obj.left)
    (L N : sfRationalConstructibleCategory C.l E Y.obj.left) : Prop :=
  letI : ∀ x : X.obj.left, Invertible (C.l : X.obj.left.residueField x) :=
    fun x ↦ (map_natCast (X.obj.hom.residueFieldAlgebraMap x) C.l) ▸
      ((PurCompactSupport.coefficientPrimeUnit C.l D C.different).map
        (X.obj.hom.residueFieldAlgebraMap x)).invertible
  letI : ∀ y : Y.obj.left, Invertible (C.l : Y.obj.left.residueField y) :=
    fun y ↦ (map_natCast (Y.obj.hom.residueFieldAlgebraMap y) C.l) ▸
      ((PurCompactSupport.coefficientPrimeUnit C.l D C.different).map
        (Y.obj.hom.residueFieldAlgebraMap y)).invertible
  let TX := S.higher.rationalTensor X
  let TY := S.higher.rationalTensor Y
  let F := S.higher.rational.support f c
  let U := S.higher.rational.pull f
  let aX := sixFunctorProjectionTensorAssociator TX _ (S.higher.rationalTensorNormalization X)
    (pullbackTensorRationalAssociator C.l E X.obj.left)
  let aY := sixFunctorProjectionTensorAssociator TY _ (S.higher.rationalTensorNormalization Y)
    (pullbackTensorRationalAssociator C.l E Y.obj.left)
  (TY.flip.obj N).map (compactSupportProjectionComponent S.higher.rationalExchange f c K L) ≫
      compactSupportProjectionComponent S.higher.rationalExchange f c
        ((TX.obj K).obj (U.obj L)) N =
    (aY (F.obj K) L N).hom ≫
      compactSupportProjectionComponent S.higher.rationalExchange f c K ((TY.obj L).obj N) ≫
      F.map ((TX.obj K).map (sixFunctorProjectionRationalMu S f L N).hom) ≫
      F.map (aX K (U.obj L) (U.obj N)).inv

/-- Finite-reduction compatibility for the datum's rational projection maps.
Right tensor by the constant quotient is reduction kept in the original coefficient
category, as in prop-sf-pf-reduction. The displayed identity is stated for all N,
so it also retains the identity and zero reductions.
Source: current blueprint prop-sf-pf-coherence, final clause
(blueprint: prop-sf-pf-coherence).
Proof: the proper counit projection satisfies tensor associativity by transposing
both composites. The open unit tensor comparison satisfies the same identity on
pure tensors. Paste them. At the integral stage retain this equation on coherent
systems and their completion units before applying Rlim. Localization and a common
finite coefficient field preserve it, with the specified tensor associators. -/
theorem sixFunctorProjection_reduction_rational (S : SixFunctorDatum D C E n hn)
    {X Y : SixFunctorSpace D} (f : X ⟶ Y) [IsSeparated f.hom.left]
    (c : Compactification f.hom.left) (K : sfRationalConstructibleCategory C.l E X.obj.left)
    (L N : sfRationalConstructibleCategory C.l E Y.obj.left) :
    sixFunctorProjectionRationalReductionSquare S f c K L N := by
  sorry

/-- The completed or field reduction square, expressed for right tensor with any
constructible coefficient object N. In particular this includes the constant
quotient by every ideal (and the zero and unit quotients). Pullback of N supplies
the coefficient object on X, with its canonical monoidal identification.
Source: current blueprint prop-sf-pf-coherence, finite reduction clause;
prop-sf-pf-reduction (1) (blueprint: prop-sf-pf-coherence). -/
def sixFunctorProjectionCommonReductionSquare
    (S : SixFunctorDatum D C E n hn) {X Y : SixFunctorSpace D} (f : X ⟶ Y)
    (c : Compactification f.hom.left)
    (K : generalAlgebraicallyClosedConstructibleCategory C.l C.Qbar X.obj.left)
    (L N : generalAlgebraicallyClosedConstructibleCategory C.l C.Qbar
      Y.obj.left) : Prop :=
  letI : ∀ x : X.obj.left, Invertible (C.l : X.obj.left.residueField x) :=
    fun x ↦ (map_natCast (X.obj.hom.residueFieldAlgebraMap x) C.l) ▸
      ((PurCompactSupport.coefficientPrimeUnit C.l D C.different).map
        (X.obj.hom.residueFieldAlgebraMap x)).invertible
  letI : ∀ y : Y.obj.left, Invertible (C.l : Y.obj.left.residueField y) :=
    fun y ↦ (map_natCast (Y.obj.hom.residueFieldAlgebraMap y) C.l) ▸
      ((PurCompactSupport.coefficientPrimeUnit C.l D C.different).map
        (Y.obj.hom.residueFieldAlgebraMap y)).invertible
  let TX := S.closure.commonStageTensor X
  let TY := S.closure.commonStageTensor Y
  let F := S.closure.commonStage.support f c
  let U := S.closure.commonStage.pull f
  let aX := sixFunctorProjectionTensorAssociator TX _ (S.closure.commonStageTensorNormalization X)
    (pullbackTensorCommonAssociator C.l C.Qbar X.obj.left)
  let aY := sixFunctorProjectionTensorAssociator TY _ (S.closure.commonStageTensorNormalization Y)
    (pullbackTensorCommonAssociator C.l C.Qbar Y.obj.left)
  (TY.flip.obj N).map (compactSupportProjectionComponent S.closure.commonStageExchange f c K L) ≫
      compactSupportProjectionComponent S.closure.commonStageExchange f c
        ((TX.obj K).obj (U.obj L)) N =
    (aY (F.obj K) L N).hom ≫
      compactSupportProjectionComponent S.closure.commonStageExchange f c K ((TY.obj L).obj N) ≫
      F.map ((TX.obj K).map (sixFunctorProjectionCommonMu S f L N).hom) ≫
      F.map (aX K (U.obj L) (U.obj N)).inv

/-- Finite-reduction compatibility for the datum's common projection maps.
Right tensor by the constant quotient is reduction kept in the original coefficient
category, as in prop-sf-pf-reduction. The displayed identity is stated for all N,
so it also retains the identity and zero reductions.
Source: current blueprint prop-sf-pf-coherence, final clause
(blueprint: prop-sf-pf-coherence).
Proof: the proper counit projection satisfies tensor associativity by transposing
both composites. The open unit tensor comparison satisfies the same identity on
pure tensors. Paste them. At the integral stage retain this equation on coherent
systems and their completion units before applying Rlim. Localization and a common
finite coefficient field preserve it, with the specified tensor associators. -/
theorem sixFunctorProjection_reduction_common (S : SixFunctorDatum D C E n hn)
    {X Y : SixFunctorSpace D} (f : X ⟶ Y) [IsSeparated f.hom.left]
    (c : Compactification f.hom.left)
    (K : generalAlgebraicallyClosedConstructibleCategory C.l C.Qbar X.obj.left)
    (L N : generalAlgebraicallyClosedConstructibleCategory C.l C.Qbar
      Y.obj.left) :
    sixFunctorProjectionCommonReductionSquare S f c K L N := by
  sorry

end WeilConjectures
