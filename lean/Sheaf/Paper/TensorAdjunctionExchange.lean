/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NO
-/
module

public import Sheaf.Paper.SixFunctorOperationDatum
public import Sheaf.Paper.ExceptionalAdjointAdmissibility
public import Sheaf.Paper.VerdierExchange
public import Sheaf.Algebra.Homology.RingedInternalHomShiftOfUniverses
public import Sheaf.Paper.DerivedAutomorphismHomEvaluation

/-! # Tensor-adjunction exchange

Source: blueprint main-20261015, sec-six-functors/sk-thm-sf-package,
fix-lem-tensor-adjunction (blueprint: fix-lem-tensor-adjunction).

The map is specified by evaluation, projection and the two adjunctions. The
realization records below reuse the existing ringed projection and signed-Hom
normalizations; no Verdier-exchange theorem or biduality assertion is used.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option genSizeOf false
set_option genCtorIdx false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
universe u a b v w
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open CategoryTheory.Pretriangulated.Opposite
open scoped CategoryTheory.Functor
namespace WeilConjectures
namespace TensorAdjunctionExchange
open ConstructibleExceptionalCoefficients

variable (l : ℕ) [Fact l.Prime]
  (Ω : Type u) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]

/-- The three adjunctions and the projection isomorphism on the actual finite-Tor
categories. These are conclusion data, with their canonical realization below.
Source: blueprint proof, five-arrow chain (blueprint: fix-lem-tensor-adjunction). -/
structure Model {X Y : Scheme.{u}} (s : Stage.{u} l) (F : Operation l Ω X Y s) where
  homX : (C l Ω X s)ᵒᵖ × C l Ω X s ⥤ C l Ω X s
  homY : (C l Ω Y s)ᵒᵖ × C l Ω Y s ⥤ C l Ω Y s
  closedX : CoefficientClosedStructure homX
  closedY : CoefficientClosedStructure homY
  pull : C l Ω Y s ⥤ C l Ω X s
  star : C l Ω X s ⥤ C l Ω Y s
  adjunction : pull ⊣ star
  projection (L : C l Ω Y s) (M : C l Ω X s) :
    F.F.obj (closedX.tensor.obj (pull.obj L, M)) ≅
      closedY.tensor.obj (L, F.F.obj M)

/-- The left side Rf_* RHom(M,f!N), as a bifunctor on the actual finite-Tor categories.
Source: displayed exchange (blueprint: fix-lem-tensor-adjunction). -/
def Model.left {X Y : Scheme.{u}} {s : Stage.{u} l} {F : Operation l Ω X Y s}
    (d : Model l Ω s F) : (C l Ω X s)ᵒᵖ ⥤ C l Ω Y s ⥤ C l Ω Y s :=
  Functor.curry.obj d.homX ⋙ (Functor.whiskeringLeft _ _ _).obj F.G ⋙
    (Functor.whiskeringRight _ _ _).obj d.star

/-- The right side RHom(Rf_!M,N), with both variances retained.
Source: displayed exchange (blueprint: fix-lem-tensor-adjunction). -/
def Model.right {X Y : Scheme.{u}} {s : Stage.{u} l} {F : Operation l Ω X Y s}
    (d : Model l Ω s F) : (C l Ω X s)ᵒᵖ ⥤ C l Ω Y s ⥤ C l Ω Y s :=
  F.F.op ⋙ Functor.curry.obj d.homY

/-- The inverse of the required exchange, explicitly transposed from evaluation.
This is the blueprint's h_B(1), so invertibility cannot select an unrelated map.
Source: proof steps 5--6 (blueprint: fix-lem-tensor-adjunction). -/
def Model.inverseComponent {X Y : Scheme.{u}} {s : Stage.{u} l}
    {F : Operation l Ω X Y s} (d : Model l Ω s F)
    (M : C l Ω X s) (N : C l Ω Y s) :
    ((d.right l Ω).obj (op M)).obj N ⟶ ((d.left l Ω).obj (op M)).obj N :=
  d.adjunction.homEquiv _ _
    (d.closedX.transpose _ M (F.G.obj N)
      (F.adjunction.homEquiv _ _
        ((d.projection (d.homY.obj (op (F.F.obj M), N)) M).hom ≫
          d.closedY.evaluation (F.F.obj M) N)))

/-- The natural isomorphism has the specified inverse components. Both shift
variables are retained: the opposite-category shift gives the negative shift of M.
Source: statement and proof step 8 (blueprint: fix-lem-tensor-adjunction). -/
structure Conclusion {X Y : Scheme.{u}} {s : Stage.{u} l} {F : Operation l Ω X Y s}
    (d : Model l Ω s F) where
  exchange : d.left l Ω ≅ d.right l Ω
  components (M : C l Ω X s) (N : C l Ω Y s) :
    (exchange.inv.app (op M)).app N = d.inverseComponent l Ω M N
  [homXFirst : ∀ N, ((Functor.curry.obj d.homX).flip.obj N).CommShift ℤ]
  [homYFirst : ∀ N, ((Functor.curry.obj d.homY).flip.obj N).CommShift ℤ]
  [homXSecond : ∀ M, ((Functor.curry.obj d.homX).obj M).CommShift ℤ]
  [homYSecond : ∀ M, ((Functor.curry.obj d.homY).obj M).CommShift ℤ]
  [starShift : d.star.CommShift ℤ]
  firstIso (N : C l Ω Y s) :
    (Functor.curry.obj d.homX).flip.obj (F.G.obj N) ⋙ d.star ≅
      F.F.op ⋙ (Functor.curry.obj d.homY).flip.obj N
  firstComponents (M : C l Ω X s) (N : C l Ω Y s) :
    (firstIso N).hom.app (op M) = (exchange.hom.app (op M)).app N
  first (N : C l Ω Y s) : (firstIso N).hom.CommShift ℤ
  second (M : (C l Ω X s)ᵒᵖ) :
    NatTrans.CommShift
      (F₁ := (F.G ⋙ (Functor.curry.obj d.homX).obj M) ⋙ d.star)
      (F₂ := (Functor.curry.obj d.homY).obj (F.F.op.obj M))
      (exchange.app M).hom ℤ

/-- Actual coefficient comparisons of the three adjunction ingredients; Hom maps
below are defined from these tensor comparisons and evaluation, rather than supplied.
Source: statement, coefficient clause (blueprint: fix-lem-tensor-adjunction). -/
structure Change {X Y : Scheme.{u}} {s t : Stage.{u} l}
    {F : Operation l Ω X Y s} {G : Operation l Ω X Y t}
    (d : Model l Ω s F) (e : Model l Ω t G)
    (TX : C l Ω X s ⥤ C l Ω X t) (TY : C l Ω Y s ⥤ C l Ω Y t) where
  exceptional : FieldComparison l Ω F G TX TY
  tensorX : d.closedX.tensor ⋙ TX ≅ (TX.prod TX) ⋙ e.closedX.tensor
  tensorY : d.closedY.tensor ⋙ TY ≅ (TY.prod TY) ⋙ e.closedY.tensor
  pull : d.pull ⋙ TX ≅ TY ⋙ e.pull
  projection (K : C l Ω Y s) (M : C l Ω X s) :
    TY.map (d.projection K M).hom ≫ tensorY.hom.app (K, F.F.obj M) ≫
        e.closedY.tensor.map (Prod.mkHom (𝟙 _) ((exceptional.q l Ω).hom.app M)) =
      (exceptional.q l Ω).hom.app (d.closedX.tensor.obj (d.pull.obj K, M)) ≫
        G.F.map (tensorX.hom.app (d.pull.obj K, M) ≫
          e.closedX.tensor.map (Prod.mkHom (pull.hom.app K) (𝟙 _))) ≫
        (e.projection (TY.obj K) (TX.obj M)).hom

/-- Hom coefficient map: transpose the extension of evaluation.
Source: proof step 7 (blueprint: fix-lem-tensor-adjunction). -/
def Change.homX {X Y : Scheme.{u}} {s t : Stage.{u} l}
    {F : Operation l Ω X Y s} {G : Operation l Ω X Y t}
    {d : Model l Ω s F} {e : Model l Ω t G}
    {TX : C l Ω X s ⥤ C l Ω X t} {TY : C l Ω Y s ⥤ C l Ω Y t}
    (a : Change l Ω d e TX TY) (M N : C l Ω X s) :
    TX.obj (d.homX.obj (op M, N)) ⟶ e.homX.obj (op (TX.obj M), TX.obj N) :=
  e.closedX.transpose _ _ _
    (a.tensorX.inv.app (d.homX.obj (op M, N), M) ≫ TX.map (d.closedX.evaluation M N))

/-- Hom coefficient map on Y, using its actual tensor and evaluation.
Source: proof step 7 (blueprint: fix-lem-tensor-adjunction). -/
def Change.homY {X Y : Scheme.{u}} {s t : Stage.{u} l}
    {F : Operation l Ω X Y s} {G : Operation l Ω X Y t}
    {d : Model l Ω s F} {e : Model l Ω t G}
    {TX : C l Ω X s ⥤ C l Ω X t} {TY : C l Ω Y s ⥤ C l Ω Y t}
    (a : Change l Ω d e TX TY) (M N : C l Ω Y s) :
    TY.obj (d.homY.obj (op M, N)) ⟶ e.homY.obj (op (TY.obj M), TY.obj N) :=
  e.closedY.transpose _ _ _
    (a.tensorY.inv.app (d.homY.obj (op M, N), M) ≫ TY.map (d.closedY.evaluation M N))

/-- Ordinary direct-image coefficient map, the counit-normalized pullback mate.
Source: proof step 7 (blueprint: fix-lem-tensor-adjunction). -/
def Change.star {X Y : Scheme.{u}} {s t : Stage.{u} l}
    {F : Operation l Ω X Y s} {G : Operation l Ω X Y t}
    {d : Model l Ω s F} {e : Model l Ω t G}
    {TX : C l Ω X s ⥤ C l Ω X t} {TY : C l Ω Y s ⥤ C l Ω Y t}
    (a : Change l Ω d e TX TY) (K : C l Ω X s) :
    TY.obj (d.star.obj K) ⟶ e.star.obj (TX.obj K) :=
  e.adjunction.homEquiv _ _ (a.pull.inv.app _ ≫ TX.map (d.adjunction.counit.app K))

/-- Equality of the two actual routes for the inverse exchange. Since exchange
is invertible this is equivalently its forward comparison square.
Source: proof step 7 (blueprint: fix-lem-tensor-adjunction). -/
def Compatible {X Y : Scheme.{u}} {s t : Stage.{u} l}
    {F : Operation l Ω X Y s} {G : Operation l Ω X Y t}
    {d : Model l Ω s F} {e : Model l Ω t G}
    {TX : C l Ω X s ⥤ C l Ω X t} {TY : C l Ω Y s ⥤ C l Ω Y t}
    (a : Change l Ω d e TX TY) : Prop :=
  ∀ (M : C l Ω X s) (N : C l Ω Y s),
    TY.map (d.inverseComponent l Ω M N) ≫
        a.star l Ω (d.homX.obj (op M, F.G.obj N)) ≫
        e.star.map (a.homX l Ω M (F.G.obj N)) ≫
        e.star.map (e.homX.map
          (Prod.mkHom (𝟙 _) ((a.exceptional.b l Ω).hom.app N))) =
      a.homY l Ω (F.F.obj M) N ≫
        e.homY.map (Prod.mkHom ((a.exceptional.q l Ω).inv.app M).op (𝟙 _)) ≫
        e.inverseComponent l Ω (TX.obj M) (TY.obj N)

/-- Realization of a restricted closed structure by the published partial closed
structure. In the integral case this uses completed tensor and its uniquely
completion-normalized evaluation, never an ordinary-to-completed isomorphism.
Source: proof steps 1--4 (blueprint: fix-lem-tensor-adjunction). -/
structure PartialRealization {A : Type a} {B : Type b}
    [Category.{v} A] [Category.{w} B] [Preadditive B]
    (H : Aᵒᵖ × A ⥤ A) (closed : CoefficientClosedStructure H)
    (I : A ⥤ B) (T : B × B ⥤ B) (J : ObjectProperty (Bᵒᵖ × B))
    (HB : J.FullSubcategory ⥤ B) (S : PodPartialClosed T J HB) where
  pair (P : Aᵒᵖ × A) : J ((I.op.prod I).obj P)
  hom : H ⋙ I ≅ J.lift (I.op.prod I) pair ⋙ HB
  tensor : closed.tensor ⋙ I ≅ (I.prod I) ⋙ T
  evaluation (M N : A) :
    I.map (closed.evaluation M N) =
      tensor.hom.app (H.obj (op M, N), M) ≫
        T.map (Prod.mkHom (hom.hom.app (op M, N)) (𝟙 _)) ≫
        S.evaluation ⟨(op (I.obj M), I.obj N), pair (op M, N)⟩

/-- Identification with the original ringed internal Hom, tensor, evaluation,
and ordinary pullback/direct-image adjunction, for arbitrary M and N.
Source: blueprint proof steps 1--4 (blueprint: fix-lem-tensor-adjunction). -/
structure RingModel {X Y : Scheme.{u}} (f : X ⟶ Y) (s : RingStage.{u} l)
    {F : Operation l Ω X Y (s.stage l)} (d : Model l Ω (s.stage l) F) where
  modelX : RingedSiteDualityModel.{u + 1, u, u}
    (ProEt.topology X) ((s.coefficients l).ring X)
  modelY : RingedSiteDualityModel.{u + 1, u, u}
    (ProEt.topology Y) ((s.coefficients l).ring Y)
  homX : d.homX ⋙ s.inclusion l Ω X ≅
    ((s.inclusion l Ω X).op.prod (s.inclusion l Ω X)) ⋙ VerdierExchange.ringHom l X s
  homY : d.homY ⋙ s.inclusion l Ω Y ≅
    ((s.inclusion l Ω Y).op.prod (s.inclusion l Ω Y)) ⋙ VerdierExchange.ringHom l Y s
  tensorX : d.closedX.tensor ⋙ s.inclusion l Ω X ≅
    ((s.inclusion l Ω X).prod (s.inclusion l Ω X)) ⋙ modelX.closed.tensor
  tensorY : d.closedY.tensor ⋙ s.inclusion l Ω Y ≅
    ((s.inclusion l Ω Y).prod (s.inclusion l Ω Y)) ⋙ modelY.closed.tensor
  evaluationX (M N : C l Ω X (s.stage l)) :
    (s.inclusion l Ω X).map (d.closedX.evaluation M N) =
      tensorX.hom.app (d.homX.obj (op M, N), M) ≫
        modelX.closed.tensor.map (Prod.mkHom (homX.hom.app (op M, N)) (𝟙 _)) ≫
        modelX.closed.evaluation ((s.inclusion l Ω X).obj M) ((s.inclusion l Ω X).obj N)
  evaluationY (M N : C l Ω Y (s.stage l)) :
    (s.inclusion l Ω Y).map (d.closedY.evaluation M N) =
      tensorY.hom.app (d.homY.obj (op M, N), M) ≫
        modelY.closed.tensor.map (Prod.mkHom (homY.hom.app (op M, N)) (𝟙 _)) ≫
        modelY.closed.evaluation ((s.inclusion l Ω Y).obj M) ((s.inclusion l Ω Y).obj N)
  pull : d.pull ⋙ s.inclusion l Ω X ≅
    s.inclusion l Ω Y ⋙ PurCompactSupport.pull (s.coefficients l) f
  star : d.star ⋙ s.inclusion l Ω Y ≅
    s.inclusion l Ω X ⋙ PurCompactSupport.push (s.coefficients l) f
  adjunction (K : C l Ω Y (s.stage l)) (M : C l Ω X (s.stage l))
      (a : d.pull.obj K ⟶ M) :
    (s.inclusion l Ω Y).map (d.adjunction.homEquiv K M a) ≫ star.hom.app M =
      (proEtaleRingDerivedAdjunction f ((s.coefficients l).ring Y)
        ((s.coefficients l).ring X) ((s.coefficients l).pull f)).homEquiv _ _
          (pull.inv.app K ≫ (s.inclusion l Ω X).map a)

/-- Normalization of the projection used in the five-arrow chain by the actual
proper-counit/open-projection map, with its signed K-flat tensor realizations.
Source: blueprint proof step 5 (blueprint: fix-lem-tensor-adjunction). -/
structure Projection {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f) (s : RingStage.{u} l)
    {F : Operation l Ω X Y (s.stage l)} {d : Model l Ω (s.stage l) F}
    (r : RingModel l Ω f s d) (left : LeftRealization l Ω c s F) where
  tensorX : VerdierExchange.ProjectionTensor l X s r.modelX
  tensorY : VerdierExchange.ProjectionTensor l Y s r.modelY
  tensorBar : ProEtaleTensorModel c.Z ((s.coefficients l).ring c.Z)
  pullComposition : (s.coefficients l).pull (c.i ≫ c.g) =
    proEtaleRingCompositeCoefficients c.i c.g
      ((s.coefficients l).ring Y) ((s.coefficients l).ring c.Z)
      ((s.coefficients l).ring X) ((s.coefficients l).pull c.g) ((s.coefficients l).pull c.i)
  projectionIso (M : C l Ω X (s.stage l)) (K : C l Ω Y (s.stage l)) :
    r.modelY.closed.tensor.obj
        ((PurCompactSupport.image (s.coefficients l) c).obj ((s.inclusion l Ω X).obj M),
          (s.inclusion l Ω Y).obj K) ≅
      (PurCompactSupport.image (s.coefficients l) c).obj
        (r.modelX.closed.tensor.obj ((s.inclusion l Ω X).obj M,
          (PurCompactSupport.pull (s.coefficients l) f).obj ((s.inclusion l Ω Y).obj K)))
  projectionMap (M : C l Ω X (s.stage l)) (K : C l Ω Y (s.stage l)) :
    (projectionIso M K).hom =
      ((PurCompactSupport.projectionMap (s.coefficients l) c
        tensorX.toModel tensorBar tensorY.toModel pullComposition).app
          ((s.inclusion l Ω X).obj M)).app ((s.inclusion l Ω Y).obj K)
  normalized (K : C l Ω Y (s.stage l)) (M : C l Ω X (s.stage l)) :
    (s.inclusion l Ω Y).map (d.projection K M).hom =
      left.hom.app (d.closedX.tensor.obj (d.pull.obj K, M)) ≫
        (PurCompactSupport.image (s.coefficients l) c).map
          (r.tensorX.hom.app (d.pull.obj K, M) ≫
            r.modelX.closed.tensor.map (Prod.mkHom (r.pull.hom.app K) (𝟙 _)) ≫
            (r.modelX.symmetric.braiding
              ((PurCompactSupport.pull (s.coefficients l) f).obj ((s.inclusion l Ω Y).obj K))
              ((s.inclusion l Ω X).obj M)).hom) ≫
        (projectionIso M K).inv ≫
        (r.modelY.symmetric.braiding
          ((PurCompactSupport.image (s.coefficients l) c).obj ((s.inclusion l Ω X).obj M))
          ((s.inclusion l Ω Y).obj K)).hom ≫
        r.modelY.closed.tensor.map (Prod.mkHom (𝟙 _) (left.inv.app M)) ≫
        r.tensorY.inv.app (K, F.F.obj M)


/-- Realize both Hom shift variables by the existing signed-source and unsigned-target
Hom comparisons. These are conclusions, not extra shift hypotheses.
Source: blueprint proof step 8 (blueprint: fix-lem-tensor-adjunction). -/
structure RingShifts {X Y : Scheme.{u}} {f : X ⟶ Y} {s : RingStage.{u} l}
    {F : Operation l Ω X Y (s.stage l)} {d : Model l Ω (s.stage l) F}
    (r : RingModel l Ω f s d) (c : Conclusion l Ω d) where
  modelX (Q : C l Ω X (s.stage l)) :
    VerdierExchange.DualShiftModel l X s ((s.inclusion l Ω X).obj Q)
  modelY (Q : C l Ω Y (s.stage l)) :
    VerdierExchange.DualShiftModel l Y s ((s.inclusion l Ω Y).obj Q)
  firstX (Q : C l Ω X (s.stage l)) :
    (Functor.curry.obj d.homX).flip.obj Q ⋙ s.inclusion l Ω X ≅
      (s.inclusion l Ω X).op ⋙
        VerdierExchange.rawDual l X s ((s.inclusion l Ω X).obj Q)
  firstY (Q : C l Ω Y (s.stage l)) :
    (Functor.curry.obj d.homY).flip.obj Q ⋙ s.inclusion l Ω Y ≅
      (s.inclusion l Ω Y).op ⋙
        VerdierExchange.rawDual l Y s ((s.inclusion l Ω Y).obj Q)
  firstComponentsX (M Q : C l Ω X (s.stage l)) :
    (firstX Q).hom.app (op M) = r.homX.hom.app (op M, Q)
  firstComponentsY (M Q : C l Ω Y (s.stage l)) :
    (firstY Q).hom.app (op M) = r.homY.hom.app (op M, Q)
  firstShiftX (Q : C l Ω X (s.stage l)) :
    letI := c.homXFirst Q
    letI := (modelX Q).ambientShift
    (firstX Q).hom.CommShift ℤ
  firstShiftY (Q : C l Ω Y (s.stage l)) :
    letI := c.homYFirst Q
    letI := (modelY Q).ambientShift
    (firstY Q).hom.CommShift ℤ
  secondX (M : C l Ω X (s.stage l)) :
    (Functor.curry.obj d.homX).obj (op M) ⋙ s.inclusion l Ω X ≅
      s.inclusion l Ω X ⋙ CategoryTheory.RingedHomUniverses.hom.{u + 1, u, u}
        (ProEt.topology X) ((s.coefficients l).ring X) ((s.inclusion l Ω X).obj M)
  secondY (M : C l Ω Y (s.stage l)) :
    (Functor.curry.obj d.homY).obj (op M) ⋙ s.inclusion l Ω Y ≅
      s.inclusion l Ω Y ⋙ CategoryTheory.RingedHomUniverses.hom.{u + 1, u, u}
        (ProEt.topology Y) ((s.coefficients l).ring Y) ((s.inclusion l Ω Y).obj M)
  secondComponentsX (M Q : C l Ω X (s.stage l)) :
    (secondX M).hom.app Q = r.homX.hom.app (op M, Q)
  secondComponentsY (M Q : C l Ω Y (s.stage l)) :
    (secondY M).hom.app Q = r.homY.hom.app (op M, Q)
  secondShiftX (M : C l Ω X (s.stage l)) :
    letI := c.homXSecond (op M)
    (secondX M).hom.CommShift ℤ
  secondShiftY (M : C l Ω Y (s.stage l)) :
    letI := c.homYSecond (op M)
    (secondY M).hom.CommShift ℤ
  starShift : letI := c.starShift
    r.star.hom.CommShift ℤ

/-- Shift-compatible coefficient transposes, in both Hom variables. The components
are the already defined maps, rather than unrelated natural transformations.
Source: blueprint proof steps 7--9 (blueprint: fix-lem-tensor-adjunction). -/
structure ChangeShifts {X Y : Scheme.{u}} {s t : Stage.{u} l}
    {F : Operation l Ω X Y s} {G : Operation l Ω X Y t}
    {d : Model l Ω s F} {e : Model l Ω t G}
    (cs : Conclusion l Ω d) (ct : Conclusion l Ω e)
    {TX : C l Ω X s ⥤ C l Ω X t} {TY : C l Ω Y s ⥤ C l Ω Y t}
    (a : Change l Ω d e TX TY) where
  firstX (N : C l Ω X s) :
    (Functor.curry.obj d.homX).flip.obj N ⋙ TX ⟶
      TX.op ⋙ (Functor.curry.obj e.homX).flip.obj (TX.obj N)
  firstY (N : C l Ω Y s) :
    (Functor.curry.obj d.homY).flip.obj N ⋙ TY ⟶
      TY.op ⋙ (Functor.curry.obj e.homY).flip.obj (TY.obj N)
  secondX (M : C l Ω X s) :
    (Functor.curry.obj d.homX).obj (op M) ⋙ TX ⟶
      TX ⋙ (Functor.curry.obj e.homX).obj (op (TX.obj M))
  secondY (M : C l Ω Y s) :
    (Functor.curry.obj d.homY).obj (op M) ⋙ TY ⟶
      TY ⋙ (Functor.curry.obj e.homY).obj (op (TY.obj M))
  star : d.star ⋙ TY ⟶ TX ⋙ e.star
  firstComponentsX (M N : C l Ω X s) : (firstX N).app (op M) = a.homX l Ω M N
  firstComponentsY (M N : C l Ω Y s) : (firstY N).app (op M) = a.homY l Ω M N
  secondComponentsX (M N : C l Ω X s) : (secondX M).app N = a.homX l Ω M N
  secondComponentsY (M N : C l Ω Y s) : (secondY M).app N = a.homY l Ω M N
  starComponents (M : C l Ω X s) : star.app M = a.star l Ω M
  firstShiftX (N : C l Ω X s) :
    letI := cs.homXFirst N
    letI := ct.homXFirst (TX.obj N)
    letI := a.exceptional.shiftX
    (firstX N).CommShift ℤ
  firstShiftY (N : C l Ω Y s) :
    letI := cs.homYFirst N
    letI := ct.homYFirst (TY.obj N)
    letI := a.exceptional.shiftY
    (firstY N).CommShift ℤ
  secondShiftX (M : C l Ω X s) :
    letI := cs.homXSecond (op M)
    letI := ct.homXSecond (op (TX.obj M))
    letI := a.exceptional.shiftX
    (secondX M).CommShift ℤ
  secondShiftY (M : C l Ω Y s) :
    letI := cs.homYSecond (op M)
    letI := ct.homYSecond (op (TY.obj M))
    letI := a.exceptional.shiftY
    (secondY M).CommShift ℤ
  starShift :
    letI := cs.starShift
    letI := ct.starShift
    letI := a.exceptional.shiftX
    letI := a.exceptional.shiftY
    star.CommShift ℤ

section Geometry
variable (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
  {X Y : Scheme.{u}} [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
  (f : X ⟶ Y) [f.IsOver (Spec (.of D.k))]
  [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
  (S : System l Ω D hl (f := f)) (c : Compactification f)

/-- Exactly the optional ambient admissibility at the chosen coefficient stage.
The base unit proof is packaged existentially because the dependency takes it as
an argument; no additional hypothesis about X or Y is introduced.
Source: statement and def-weil-exceptional-adjoint-admissibility
(blueprint: fix-lem-tensor-adjunction). -/
def Admissible (s : Stage.{u} l) : Prop :=
  ∃ hS : ∀ x : Spec (.of D.k), IsUnit (l : (Spec (.of D.k)).presheaf.stalk x),
    match s with
    | .finite E n => IsExceptionalAdjointAdmissibleAtFiniteStage l E.carrier n n.pos
        (Spec (.of D.k)) X Y hS f c
    | .integral E => IsExceptionalAdjointAdmissibleAtIntegral l E.carrier
        (Spec (.of D.k)) X Y hS f c
    | .rational E => IsExceptionalAdjointAdmissibleAtRational l E.carrier
        (Spec (.of D.k)) X Y hS f c
    | .closed => IsExceptionalAdjointAdmissibleAtAlgebraicallyClosed l Ω
        (Spec (.of D.k)) X Y hS f c

/-- The exchange on the prescribed coefficient stages. Every stage has its actual
operations, evaluation and projection realizations, and admissibility gives its
canonical natural isomorphism. Coefficient comparisons are those of the existing
System; in particular the exceptional right comparison is its counit-normalized mate.
Source: statement, coefficient clause and proof steps 1--9
(blueprint: fix-lem-tensor-adjunction). -/
structure CorePackage where
  stage (s : Stage.{u} l) : Model l Ω s (S.ring.operation c s)
  ring (s : RingStage.{u} l) : RingModel l Ω f s (stage (s.stage l))
  projection (s : RingStage.{u} l) :
    Projection l Ω c s (ring s) (S.ring.left c s)
  conclusion (s : Stage.{u} l) (_h : Admissible l Ω D f c s) : Conclusion l Ω (stage s)
  ringShifts (E : FieldStage.{u} l) (n : ℕ+)
      (h : Admissible l Ω D f c (.finite E n)) :
    RingShifts l Ω (ring (.finite E n)) (conclusion (.finite E n) h)
  integralX (E : FieldStage.{u} l)
      [∀ x : X, Invertible (l : X.residueField x)] :
    PartialRealization (stage (.integral E)).homX (stage (.integral E)).closedX
      (PurCompactSupport.finiteTorIntegralInclusion l E.carrier X)
      (constructibleIntegralTensor l E.carrier X)
      (constructibleIntegralHomPairs l E.carrier X)
      (constructibleIntegralHom l E.carrier X) (podIntegralClosed l E.carrier X)
  integralY (E : FieldStage.{u} l)
      [∀ y : Y, Invertible (l : Y.residueField y)] :
    PartialRealization (stage (.integral E)).homY (stage (.integral E)).closedY
      (PurCompactSupport.finiteTorIntegralInclusion l E.carrier Y)
      (constructibleIntegralTensor l E.carrier Y)
      (constructibleIntegralHomPairs l E.carrier Y)
      (constructibleIntegralHom l E.carrier Y) (podIntegralClosed l E.carrier Y)
  rationalX (E : FieldStage.{u} l)
      [∀ x : X, Invertible (l : X.residueField x)] :
    PartialRealization (stage (.rational E)).homX (stage (.rational E)).closedX (𝟭 _)
      (rationalDerivedTensor l E.carrier X) (constructibleRationalHomPairs l E.carrier X)
      (rationalDerivedInternalHom l E.carrier X) (podRationalClosed l E.carrier X)
  rationalY (E : FieldStage.{u} l)
      [∀ y : Y, Invertible (l : Y.residueField y)] :
    PartialRealization (stage (.rational E)).homY (stage (.rational E)).closedY (𝟭 _)
      (rationalDerivedTensor l E.carrier Y) (constructibleRationalHomPairs l E.carrier Y)
      (rationalDerivedInternalHom l E.carrier Y) (podRationalClosed l E.carrier Y)
  closedX [∀ x : X, Invertible (l : X.residueField x)] :
    PartialRealization (stage .closed).homX (stage .closed).closedX (𝟭 _)
      (commonStageDerivedTensor l Ω X) (commonStageHomPairs l Ω X)
      (commonStageDerivedInternalHom l Ω X) (podCommonClosed l Ω X)
  closedY [∀ y : Y, Invertible (l : Y.residueField y)] :
    PartialRealization (stage .closed).homY (stage .closed).closedY (𝟭 _)
      (commonStageDerivedTensor l Ω Y) (commonStageHomPairs l Ω Y)
      (commonStageDerivedInternalHom l Ω Y) (podCommonClosed l Ω Y)
  coefficientNaturality {s t : Stage.{u} l}
      {TX : C l Ω X s ⥤ C l Ω X t} {TY : C l Ω Y s ⥤ C l Ω Y t}
      (a : Change l Ω (stage s) (stage t) TX TY) : Compatible l Ω a
  ringScalar {s t : RingStage.{u} l}
      (a : PurCompactSupport.Change (s.coefficients l) (t.coefficients l)) (ha : Allowed l a) :
    ∃ b : Change l Ω (stage (s.stage l)) (stage (t.stage l))
        (S.ring.scalar a ha true).functor (S.ring.scalar a ha false).functor,
      b.exceptional = ⟨S.ring.comparison c a ha⟩
  rationalization (E : FieldStage.{u} l) :
    ∃ b : Change l Ω (stage (.integral E)) (stage (.rational E))
        (ConstructibleExceptionalCoefficients.rationalization l Ω E X)
        (ConstructibleExceptionalCoefficients.rationalization l Ω E Y),
      b.exceptional = S.fields.rationalizationComparison c E ∧
      (∀ M N : C l Ω X (.integral E), IsIso (b.homX l Ω M N)) ∧
      (∀ M N : C l Ω Y (.integral E), IsIso (b.homY l Ω M N)) ∧
      (∀ M : C l Ω X (.integral E), IsIso (b.star l Ω M))
  rationalScalar (E L : FieldStage.{u} l) (i : E.carrier →ₐ[Padic l] L.carrier) :
    ∃ b : Change l Ω (stage (.rational E)) (stage (.rational L))
        (ConstructibleExceptionalCoefficients.rationalScalar l Ω E L i X)
        (ConstructibleExceptionalCoefficients.rationalScalar l Ω E L i Y),
      b.exceptional = S.fields.rationalComparison c E L i ∧
      (∀ M N : C l Ω X (.rational E), IsIso (b.homX l Ω M N)) ∧
      (∀ M N : C l Ω Y (.rational E), IsIso (b.homY l Ω M N)) ∧
      (∀ M : C l Ω X (.rational E), IsIso (b.star l Ω M))
  common (i : AlgebraicallyClosedCoefficients.Index l Ω) :
    ∃ b : Change l Ω (stage (.rational (commonField l Ω i))) (stage .closed)
        (commonInclusion l Ω X i) (commonInclusion l Ω Y i),
      b.exceptional = S.common.commonComparison c i ∧
      (∀ M N : C l Ω X (.rational (commonField l Ω i)), IsIso (b.homX l Ω M N)) ∧
      (∀ M N : C l Ω Y (.rational (commonField l Ω i)), IsIso (b.homY l Ω M N)) ∧
      (∀ M : C l Ω X (.rational (commonField l Ω i)), IsIso (b.star l Ω M))
  coefficientShifts {s t : Stage.{u} l}
      (hs : Admissible l Ω D f c s) (ht : Admissible l Ω D f c t)
      {TX : C l Ω X s ⥤ C l Ω X t} {TY : C l Ω Y s ⥤ C l Ω Y t}
      (a : Change l Ω (stage s) (stage t) TX TY) :
    Nonempty (ChangeShifts l Ω (conclusion s hs) (conclusion t ht) a)

end Geometry

/-- Realization of the four functors and their adjunctions in the specified datum.
The two transpose equations fix the adjunctions as well as the objectwise functors.
Source: the six-functor datum in the statement
(blueprint: fix-lem-tensor-adjunction). -/
structure OperationRealization {X Y : Scheme.{u}} {s : Stage.{u} l}
    {F : Operation l Ω X Y s} (d : Model l Ω s F)
    {AX AY : Type a} [Category.{v} AX] [Category.{v} AY]
    (IX : C l Ω X s ⥤ AX) (IY : C l Ω Y s ⥤ AY)
    (P : AY ⥤ AX) (R U : AX ⥤ AY) (V : AY ⥤ AX)
    (adj : P ⊣ R) (exc : U ⊣ V) where
  pull : d.pull ⋙ IX ≅ IY ⋙ P
  star : d.star ⋙ IY ≅ IX ⋙ R
  support : F.F ⋙ IY ≅ IX ⋙ U
  exceptional : F.G ⋙ IX ≅ IY ⋙ V
  ordinary (K : C l Ω Y s) (M : C l Ω X s) (a : d.pull.obj K ⟶ M) :
    IY.map (d.adjunction.homEquiv K M a) ≫ star.hom.app M =
      adj.homEquiv _ _ (pull.inv.app K ≫ IX.map a)
  extraordinary (M : C l Ω X s) (N : C l Ω Y s) (a : F.F.obj M ⟶ N) :
    IX.map (F.adjunction.homEquiv M N a) ≫ exceptional.hom.app N =
      exc.homEquiv _ _ (support.inv.app M ≫ IY.map a)

/-- The full-subcategory inclusion of finite-Tor objects into bounded constructible
objects. It uses the first clause of the recorded finite-Tor predicate.
Source: finite-Tor convention of the datum (blueprint: fix-lem-tensor-adjunction). -/
def finiteInclusion (E : FieldStage.{u} l) (n : ℕ+) (X : Scheme.{u}) :
    C l Ω X (.finite E n) ⥤
      (intrinsicFiniteTorsionConstructible l E.carrier n n.pos X).FullSubcategory where
  obj M := ⟨M.obj, M.property.1⟩
  map a := ObjectProperty.homMk a.hom

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

/-- The compactifying scheme with its original map to the fixed base.
Source: the chosen compactification in proof step 5
(blueprint: fix-lem-tensor-adjunction). -/
def compactificationSpace {D : FiniteFieldDatum.{u}} {X Y : SixFunctorSpace D}
    {f : X ⟶ Y} (c : Compactification f.hom.left) : SixFunctorSpace D :=
  letI : LocallyOfFiniteType Y.obj.hom := Y.property.1
  letI : QuasiCompact Y.obj.hom := Y.property.2
  ⟨Over.mk (c.g ≫ Y.obj.hom),
    ⟨inferInstanceAs (LocallyOfFiniteType (c.g ≫ Y.obj.hom)),
      inferInstanceAs (QuasiCompact (c.g ≫ Y.obj.hom))⟩⟩

/-- The open factor as a morphism of the original base schemes.
Source: the chosen compactification in proof step 5
(blueprint: fix-lem-tensor-adjunction). -/
def compactificationOpen {D : FiniteFieldDatum.{u}} {X Y : SixFunctorSpace D}
    {f : X ⟶ Y} (c : Compactification f.hom.left) :
    X ⟶ compactificationSpace c :=
  ObjectProperty.homMk (Over.homMk c.i (by
    change c.i ≫ (c.g ≫ Y.obj.hom) = X.obj.hom
    rw [← Category.assoc, ← c.comm]
    exact Over.w f.hom))

/-- The proper factor retains the given base map.
Source: the chosen compactification in proof step 5
(blueprint: fix-lem-tensor-adjunction). -/
def compactificationProper {D : FiniteFieldDatum.{u}} {X Y : SixFunctorSpace D}
    {f : X ⟶ Y} (c : Compactification f.hom.left) :
    compactificationSpace c ⟶ Y :=
  ObjectProperty.homMk (Over.homMk c.g rfl)

/-- The identity base-change square, used only to read the projection component
of the supplied datum at the original compactification. All schemes and arrows
are explicit; no existence hypothesis on squares is imposed.
Source: def-exchange-projection and proof step 5
(blueprint: fix-lem-tensor-adjunction). -/
abbrev projectionSquare {D : FiniteFieldDatum.{u}} {X Y : SixFunctorSpace D}
    (f : X ⟶ Y) (c : Compactification f.hom.left) : SixFunctorCompactifiedSquare D where
  X := X
  Y := Y
  X' := X
  Y' := Y
  Z := compactificationSpace c
  Z' := compactificationSpace c
  f := f
  f' := f
  g := 𝟙 Y
  g' := 𝟙 X
  i := compactificationOpen c
  i' := compactificationOpen c
  p := compactificationProper c
  p' := compactificationProper c
  h := 𝟙 _
  open_i := c.isOpenImmersion
  open_i' := c.isOpenImmersion
  proper_p := c.isProper
  proper_p' := c.isProper
  factorization := ObjectProperty.hom_ext _ (Over.OverMorphism.ext c.comm)
  factorization' := ObjectProperty.hom_ext _ (Over.OverMorphism.ext c.comm)
  square := IsPullback.of_id_fst
  properSquare := IsPullback.of_id_fst
  openSquare := IsPullback.of_id_fst
  squareComm := (Category.id_comp f).trans (Category.comp_id f).symm
  properComm := (Category.id_comp _).trans (Category.comp_id _).symm
  openComm := (Category.id_comp _).trans (Category.comp_id _).symm

/-- A tensor realization expressed in the datum's curried coordinates.
The only extra factor is the equality with the published tensor, so a scalar
rescaling is not permitted.
Source: completed/localized tensor normalization, proof steps 2 and 9
(blueprint: fix-lem-tensor-adjunction). -/
def tensorComponent {B : Type a} {V : Type b} [Category.{v} B] [Category.{w} V]
    (I : B ⥤ V) (T : B × B ⥤ B) (R : V × V ⥤ V) (U : V ⥤ V ⥤ V)
    (h : U = Functor.curry.obj R) (e : T ⋙ I ≅ (I.prod I) ⋙ R) (M N : B) :
    I.obj (T.obj (M, N)) ≅ (U.obj (I.obj M)).obj (I.obj N) :=
  e.app (M, N) ≪≫
    eqToIso (congrArg (fun V' ↦ (V'.obj (I.obj M)).obj (I.obj N)) h.symm)

/-- The published signed braiding in the datum's tensor coordinates.
Source: lem-pur-derived-pullback-tensor-iso, higher coefficient braidings,
and proof step 5 (blueprint: fix-lem-tensor-adjunction). -/
def tensorBraiding {B : Type a} [Category.{v} B]
    (T : B × B ⥤ B) (U : B ⥤ B ⥤ B) (h : U = Functor.curry.obj T)
    (β : ∀ M N : B, T.obj (M, N) ≅ T.obj (N, M)) (M N : B) :
    (U.obj M).obj N ≅ (U.obj N).obj M :=
  eqToIso (congrArg (fun V' ↦ (V'.obj M).obj N) h) ≪≫ β M N ≪≫
    eqToIso (congrArg (fun V' ↦ (V'.obj N).obj M) h.symm)

/-- The inverse model projection is the datum's actual projection component,
conjugated only by the specified operation/tensor realizations and canonical
signed braidings. This pins the projection before transposing evaluation.
Source: def-exchange-projection, five-arrow chain in proof step 5
(blueprint: fix-lem-tensor-adjunction). -/
def ProjectionRealized {D : FiniteFieldDatum.{u}} {Q : SixFunctorCompactifiedSquare D}
    {B : SixFunctorSpace D → Type a} [∀ X, Category.{v} (B X)]
    {U : SixFunctorPushStage D B} {T : ∀ X, B X ⥤ B X ⥤ B X}
    {s : Stage.{u} l} {F : Operation l Ω Q.X.obj.left Q.Y.obj.left s}
    (d : Model l Ω s F) (IX : C l Ω Q.X.obj.left s ⥤ B Q.X)
    (IY : C l Ω Q.Y.obj.left s ⥤ B Q.Y)
    (c : Compactification Q.f.hom.left)
    (r : OperationRealization l Ω d IX IY (U.pull Q.f) (U.direct Q.f)
      (U.support Q.f c) (U.exceptional Q.f c)
      (U.pullDirectAdjunction Q.f) (U.exceptionalAdjunction Q.f c))
    (tx : ∀ M N, IX.obj (d.closedX.tensor.obj (M, N)) ≅
      ((T Q.X).obj (IX.obj M)).obj (IX.obj N))
    (ty : ∀ M N, IY.obj (d.closedY.tensor.obj (M, N)) ≅
      ((T Q.Y).obj (IY.obj M)).obj (IY.obj N))
    (bx : ∀ M N, ((T Q.X).obj M).obj N ≅ ((T Q.X).obj N).obj M)
    (by' : ∀ M N, ((T Q.Y).obj M).obj N ≅ ((T Q.Y).obj N).obj M)
    (ex : SixFunctorExchangeData U T Q) : Prop :=
  ∀ (K : C l Ω Q.Y.obj.left s) (M : C l Ω Q.X.obj.left s),
    IY.map (d.projection K M).inv ≫
        r.support.hom.app (d.closedX.tensor.obj (d.pull.obj K, M)) ≫
        (U.support Q.f c).map
          ((tx (d.pull.obj K) M).hom ≫
            ((T Q.X).map (r.pull.hom.app K)).app (IX.obj M) ≫
            (bx ((U.pull Q.f).obj (IY.obj K)) (IX.obj M)).hom) ≫
        (U.comparison Q.f c Q.compactification).hom.app
          (((T Q.X).obj (IX.obj M)).obj ((U.pull Q.f).obj (IY.obj K))) =
      (ty K (F.F.obj M)).hom ≫
        ((T Q.Y).obj (IY.obj K)).map (r.support.hom.app M) ≫
        (by' (IY.obj K) ((U.support Q.f c).obj (IX.obj M))).hom ≫
        ((T Q.Y).map ((U.comparison Q.f c Q.compactification).hom.app
          (IX.obj M))).app (IY.obj K) ≫
        ex.projectionComponent (IX.obj M) (IY.obj K)

/-- The exchange package is on the operations of the supplied six-functor datum.
At integral coefficients the inclusion forgets only the uniform Tor bound; at
field coefficients the comparison is on the recorded category itself.
Source: initial datum clause (blueprint: fix-lem-tensor-adjunction). -/
def Package (D : FiniteFieldDatum.{u}) (A : D.CoefficientDatum)
    (E : Type u) [Field E] [Algebra (Padic A.l) E]
    [FiniteDimensional (Padic A.l) E] (n : ℕ) (hn : 1 ≤ n)
    (six : SixFunctorOperationDatum D A E n hn)
    {X Y : SixFunctorSpace D} (f : X ⟶ Y)
    [IsSeparated f.hom.left] [LocallyOfFiniteType f.hom.left] [QuasiCompact f.hom.left]
    (S : System A.l A.Qbar D A.different (f := f.hom.left))
    (c : Compactification f.hom.left)
    : Prop :=
  ∃ core : (CorePackage A.l A.Qbar D A.different f.hom.left S c),
  ∃ coefficientOperations : (∀ (L : FieldStage.{u} A.l),
    SixFunctorHigherOperations D A L.carrier),
  ∃ _coefficientNormalization : (∀ (L : FieldStage.{u} A.l),
    SixFunctorIntegralNormalization D A L.carrier (coefficientOperations L)),
  ∃ _originalCoefficient : (coefficientOperations ⟨E⟩ = six.higher),
  ∃ _integralAt : (∀ (L : FieldStage.{u} A.l),
    OperationRealization A.l A.Qbar (core.stage (.integral L))
      (PurCompactSupport.finiteTorIntegralInclusion A.l L.carrier X.obj.left)
      (PurCompactSupport.finiteTorIntegralInclusion A.l L.carrier Y.obj.left)
      ((coefficientOperations L).integral.pull f) ((coefficientOperations L).integral.direct f)
      ((coefficientOperations L).integral.support f c)
      ((coefficientOperations L).integral.exceptional f c)
      ((coefficientOperations L).integral.pullDirectAdjunction f)
      ((coefficientOperations L).integral.exceptionalAdjunction f c)),
  ∃ rationalAt : (∀ (L : FieldStage.{u} A.l),
    OperationRealization A.l A.Qbar (core.stage (.rational L)) (𝟭 _) (𝟭 _)
      ((coefficientOperations L).rational.pull f) ((coefficientOperations L).rational.direct f)
      ((coefficientOperations L).rational.support f c)
      ((coefficientOperations L).rational.exceptional f c)
      ((coefficientOperations L).rational.pullDirectAdjunction f)
      ((coefficientOperations L).rational.exceptionalAdjunction f c)),
  ∃ _finiteDatum : (OperationRealization A.l A.Qbar (core.stage (.finite ⟨E⟩ ⟨n, hn⟩))
    (finiteInclusion A.l A.Qbar ⟨E⟩ ⟨n, hn⟩ X.obj.left)
    (finiteInclusion A.l A.Qbar ⟨E⟩ ⟨n, hn⟩ Y.obj.left)
    (six.finite.pull f) (six.finite.direct f) (six.finite.support f c)
    (six.finite.exceptional f c) (six.finite.pullDirectAdjunction f)
    (six.finite.exceptionalAdjunction f c)),
  ∃ closedDatum : (OperationRealization A.l A.Qbar (core.stage .closed) (𝟭 _) (𝟭 _)
    (six.closure.commonStage.pull f) (six.closure.commonStage.direct f)
    (six.closure.commonStage.support f c) (six.closure.commonStage.exceptional f c)
    (six.closure.commonStage.pullDirectAdjunction f)
    (six.closure.commonStage.exceptionalAdjunction f c)),
  ∃ _rationalProjection : (∀ (L : FieldStage.{u} A.l)
      [∀ x : X.obj.left, Invertible (A.l : X.obj.left.residueField x)]
      [∀ y : Y.obj.left, Invertible (A.l : Y.obj.left.residueField y)],
    ProjectionRealized A.l A.Qbar (Q := projectionSquare f c)
      (core.stage (.rational L)) (𝟭 _) (𝟭 _) c (rationalAt L)
      (tensorComponent (𝟭 _) _ _ _ ((coefficientOperations L).rationalTensorNormalization X)
        (core.rationalX L).tensor)
      (tensorComponent (𝟭 _) _ _ _ ((coefficientOperations L).rationalTensorNormalization Y)
        (core.rationalY L).tensor)
      (tensorBraiding (rationalDerivedTensor A.l L.carrier X.obj.left) _
        ((coefficientOperations L).rationalTensorNormalization X)
        (pullbackTensorRationalBraiding A.l L.carrier X.obj.left))
      (tensorBraiding (rationalDerivedTensor A.l L.carrier Y.obj.left) _
        ((coefficientOperations L).rationalTensorNormalization Y)
        (pullbackTensorRationalBraiding A.l L.carrier Y.obj.left))
      ((coefficientOperations L).rationalExchange (projectionSquare f c))),
  ∀ [∀ x : X.obj.left, Invertible (A.l : X.obj.left.residueField x)]
      [∀ y : Y.obj.left, Invertible (A.l : Y.obj.left.residueField y)],
    ProjectionRealized A.l A.Qbar (Q := projectionSquare f c)
      (core.stage .closed) (𝟭 _) (𝟭 _) c closedDatum
      (tensorComponent (𝟭 _) _ _ _ (six.closure.commonStageTensorNormalization X)
        core.closedX.tensor)
      (tensorComponent (𝟭 _) _ _ _ (six.closure.commonStageTensorNormalization Y)
        core.closedY.tensor)
      (tensorBraiding (commonStageDerivedTensor A.l A.Qbar X.obj.left) _
        (six.closure.commonStageTensorNormalization X)
        (pullbackTensorCommonBraiding A.l A.Qbar X.obj.left))
      (tensorBraiding (commonStageDerivedTensor A.l A.Qbar Y.obj.left) _
        (six.closure.commonStageTensorNormalization Y)
        (pullbackTensorCommonBraiding A.l A.Qbar Y.obj.left))
      (six.closure.commonStageExchange (projectionSquare f c))

/-- The tensor-adjunction exchange, natural in both variables, with finite reduction,
scalar extension and the signed first/second shift squares. The chosen normalized
System presents the operations of the six-functor datum on the actual finite-Tor
categories. Admissibility is retained at each stage, not silently discharged.

Source: blueprint main-20261015, sec-six-functors/sk-thm-sf-package,
fix-lem-tensor-adjunction (blueprint: fix-lem-tensor-adjunction).

Proof, following the nine DAG steps:
1. On each small ringed site apply lem-pur-rhom-global-sections and
   lem-weil-pbc-ringed-internal-hom-exact-restriction to get the tensor-Hom
   adjunction with evaluation as counit, naturally in all three inputs.
2. At integral coefficients use the actual completed tensor. Its quotient tower
   is the quotient tower of ordinary tensor by the K-flat balancing map
   (p tensor a) tensor (m tensor b) to (p tensor m) tensor ab. Use
   lem-weil-pbc-constant-completion-equivalence to identify its limit with Koszul
   completion and lem-weil-pbc-ringed-koszul-completion-reflector to map into the
   complete target. Compose this bijection with step 1.
3. Before Yoneda, check both representing objects at finite coefficients.
   fix-prop-adjunctions preserves the finite-Tor inputs. Choose finite dimension
   bounds by lem-kun-dimension-finite-type. Cover each scheme by finitely many
   affine opens, apply cor-weil-finite-constructible-hom on these separated charts,
   and glue finite constructible stratifications by disjoint refinement. The Tor
   interval is uniform on the cover. cor-sf-direct-image-ctf-proetale gives the
   finite-Tor direct image. Empty schemes give zero objects.
4. Use cor-coef-integral-internal-hom and the same finite bounds integrally.
   prop-weil-pbc-direct-image-limits preserves completeness and computes every
   reduction; the finite direct-image bounds are uniform. Then
   lem-coef-integral-residue-tor puts both objects in the integral finite-Tor category.
5. For every finite-Tor test object L form the five bijections: tensor-Hom,
   inverse projection, exceptional adjunction, tensor-Hom, ordinary adjunction.
   The intermediate pullback and tensor inputs lie in their proved domains by
   lem-sf-pullback-tor-amplitude, lem-sf-tensor-ctf and
   lem-pur-integral-operations-preserve-constructible. Use completed tensor in
   every integral occurrence. The projection realization is the actual proper
   counit/open projection paste, not a freely selected isomorphism.
6. Apply fully faithful Yoneda to the full finite-Tor category. The inverse
   component is h_B(1), explicitly inverseComponent above; the forward component
   is the inverse chain applied to 1_A. Naturality gives the two identity composites
   and naturality in the contravariant M and covariant N variables.
7. Transpose the two coefficient routes through the five bijections. Tensor and
   evaluation compatibility, the canonical q/b unit and counit equations, and
   projection compatibility identify the resulting maps. Use thm-coef-finite-hom
   and lem-coef-finite-direct-image for finite reductions, the arbitrary-first-input
   lem-coef-integral-hom-reduction for integral reduction, and
   lem-pur-integral-operations-scalar-extension for integral scalar extension.
   This proves Compatible for these actual morphisms, not just their endpoints.
8. Transpose the shift square by the same chain. Source shifting in Hom gives
   the negative shift and target shifting gives the positive shift, with the
   signed Hom-complex differential. The projection is a composite of tensor,
   open comparison, pullback composition and proper counit, so its shifted map
   is the same specified map. Completion is exact and its unit is natural;
   lem-weil-pbc-ringed-strict-tower-homotopy-limit gives the limit comparison.
   Uniqueness in step 6 proves both exchange shift squares.
9. Rationalization localizes the Hom groups and sends the inverse pair to an
   inverse pair. Over the algebraic closure choose a common finite coefficient
   field for the finitely many objects and morphisms; step 7 makes the result
   independent of a larger field. Composition, naturality and shift equations
   descend through the common-stage Hom colimit. These are the operations of
   def-weil-rationalization-karoubi and def-weil-algebraically-closed-coefficients.
No Verdier-exchange, biduality or downstream preservation theorem is used. -/
theorem tensor_adjunction
    (D : FiniteFieldDatum.{u}) (A : D.CoefficientDatum)
    (E : Type u) [Field E] [Algebra (Padic A.l) E]
    [FiniteDimensional (Padic A.l) E] (n : ℕ) (hn : 1 ≤ n)
    (six : SixFunctorOperationDatum D A E n hn)
    {X Y : SixFunctorSpace D} (f : X ⟶ Y)
    [IsSeparated f.hom.left] [LocallyOfFiniteType f.hom.left] [QuasiCompact f.hom.left]
    (S : System A.l A.Qbar D A.different (f := f.hom.left))
    (c : Compactification f.hom.left) :
    Package D A E n hn six f S c := by
  sorry

end TensorAdjunctionExchange
end WeilConjectures
