/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SixFunctorOperationDatum
public import WeilConjectures.AlgebraicGeometry.ExceptionalAdjointAdmissibility
public import WeilConjectures.SixFunctors.VerdierExchangeData
public import WeilConjectures.Algebra.Homology.RingedInternalHomShiftOfUniversesSupplement
public import WeilConjectures.AlgebraicGeometry.DerivedAutomorphismHomEvaluation

/-! # Tensor--Hom transposition data

Source: blueprint main-20261015, sec-six-functors/sk-thm-sf-package,
fix-lem-tensor-adjunction (blueprint: def-sf-tensor-hom-transposition-data).

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
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
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
structure Model {X Y : Scheme.{u}} (s : Stage.{u} l) (F : Operation.{u} l Ω X Y s) where
  homX : (C.{u} l Ω X s)ᵒᵖ × C.{u} l Ω X s ⥤ C.{u} l Ω X s
  homY : (C.{u} l Ω Y s)ᵒᵖ × C.{u} l Ω Y s ⥤ C.{u} l Ω Y s
  closedX : CoefficientClosedStructure homX
  closedY : CoefficientClosedStructure homY
  pull : C.{u} l Ω Y s ⥤ C.{u} l Ω X s
  star : C.{u} l Ω X s ⥤ C.{u} l Ω Y s
  adjunction : pull ⊣ star
  projection (L : C.{u} l Ω Y s) (M : C.{u} l Ω X s) :
    F.F.obj (closedX.tensor.obj (pull.obj L, M)) ≅
      closedY.tensor.obj (L, F.F.obj M)

/-- The left side Rf_* RHom(M,f!N), as a bifunctor on the actual finite-Tor categories.
Source: displayed exchange (blueprint: fix-lem-tensor-adjunction). -/
def Model.left {X Y : Scheme.{u}} {s : Stage.{u} l} {F : Operation.{u} l Ω X Y s}
    (d : Model l Ω s F) : (C.{u} l Ω X s)ᵒᵖ ⥤ C.{u} l Ω Y s ⥤ C.{u} l Ω Y s :=
  Functor.curry.obj d.homX ⋙ (Functor.whiskeringLeft _ _ _).obj F.G ⋙
    (Functor.whiskeringRight _ _ _).obj d.star

/-- The right side RHom(Rf_!M,N), with both variances retained.
Source: displayed exchange (blueprint: fix-lem-tensor-adjunction). -/
def Model.right {X Y : Scheme.{u}} {s : Stage.{u} l} {F : Operation.{u} l Ω X Y s}
    (d : Model l Ω s F) : (C.{u} l Ω X s)ᵒᵖ ⥤ C.{u} l Ω Y s ⥤ C.{u} l Ω Y s :=
  F.F.op ⋙ Functor.curry.obj d.homY

/-- The inverse of the required exchange, explicitly transposed from evaluation.
This is the blueprint's h_B(1), so invertibility cannot select an unrelated map.
Source: proof steps 5--6 (blueprint: fix-lem-tensor-adjunction). -/
def Model.inverseComponent {X Y : Scheme.{u}} {s : Stage.{u} l}
    {F : Operation.{u} l Ω X Y s} (d : Model l Ω s F)
    (M : C.{u} l Ω X s) (N : C.{u} l Ω Y s) :
    ((d.right l Ω).obj (op M)).obj N ⟶ ((d.left l Ω).obj (op M)).obj N :=
  d.adjunction.homEquiv _ _
    (d.closedX.transpose _ M (F.G.obj N)
      (F.adjunction.homEquiv _ _
        ((d.projection (d.homY.obj (op (F.F.obj M), N)) M).hom ≫
          d.closedY.evaluation (F.F.obj M) N)))

/-- The natural isomorphism has the specified inverse components. Both shift
variables are retained: the opposite-category shift gives the negative shift of M.
Source: statement and proof step 8 (blueprint: fix-lem-tensor-adjunction). -/
structure Conclusion {X Y : Scheme.{u}} {s : Stage.{u} l} {F : Operation.{u} l Ω X Y s}
    (d : Model l Ω s F) where
  exchange : d.left l Ω ≅ d.right l Ω
  components (M : C.{u} l Ω X s) (N : C.{u} l Ω Y s) :
    (exchange.inv.app (op M)).app N = d.inverseComponent l Ω M N
  [homXFirst : ∀ N, ((Functor.curry.obj d.homX).flip.obj N).CommShift ℤ]
  [homYFirst : ∀ N, ((Functor.curry.obj d.homY).flip.obj N).CommShift ℤ]
  [homXSecond : ∀ M, ((Functor.curry.obj d.homX).obj M).CommShift ℤ]
  [homYSecond : ∀ M, ((Functor.curry.obj d.homY).obj M).CommShift ℤ]
  [starShift : d.star.CommShift ℤ]
  firstIso (N : C.{u} l Ω Y s) :
    (Functor.curry.obj d.homX).flip.obj (F.G.obj N) ⋙ d.star ≅
      F.F.op ⋙ (Functor.curry.obj d.homY).flip.obj N
  firstComponents (M : C.{u} l Ω X s) (N : C.{u} l Ω Y s) :
    (firstIso N).hom.app (op M) = (exchange.hom.app (op M)).app N
  first (N : C.{u} l Ω Y s) : (firstIso N).hom.CommShift ℤ
  second (M : (C.{u} l Ω X s)ᵒᵖ) :
    NatTrans.CommShift
      (F₁ := (F.G ⋙ (Functor.curry.obj d.homX).obj M) ⋙ d.star)
      (F₂ := (Functor.curry.obj d.homY).obj (F.F.op.obj M))
      (exchange.app M).hom ℤ

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
    {F : Operation.{u} l Ω X Y (s.stage l)} (d : Model l Ω (s.stage l) F) where
  modelX : RingedSiteDualityModel.{u + 1, u, u}
    (ProEt.topology X) ((s.coefficients l).ring X)
  modelY : RingedSiteDualityModel.{u + 1, u, u}
    (ProEt.topology Y) ((s.coefficients l).ring Y)
  homX : d.homX ⋙ s.inclusion.{u} l Ω X ≅
    ((s.inclusion.{u} l Ω X).op.prod (s.inclusion.{u} l Ω X)) ⋙ VerdierExchange.ringHom l X s
  homY : d.homY ⋙ s.inclusion.{u} l Ω Y ≅
    ((s.inclusion.{u} l Ω Y).op.prod (s.inclusion.{u} l Ω Y)) ⋙ VerdierExchange.ringHom l Y s
  tensorX : d.closedX.tensor ⋙ s.inclusion.{u} l Ω X ≅
    ((s.inclusion.{u} l Ω X).prod (s.inclusion.{u} l Ω X)) ⋙ modelX.closed.tensor
  tensorY : d.closedY.tensor ⋙ s.inclusion.{u} l Ω Y ≅
    ((s.inclusion.{u} l Ω Y).prod (s.inclusion.{u} l Ω Y)) ⋙ modelY.closed.tensor
  evaluationX (M N : C.{u} l Ω X (s.stage l)) :
    (s.inclusion.{u} l Ω X).map (d.closedX.evaluation M N) =
      tensorX.hom.app (d.homX.obj (op M, N), M) ≫
        modelX.closed.tensor.map (Prod.mkHom (homX.hom.app (op M, N)) (𝟙 _)) ≫
        modelX.closed.evaluation ((s.inclusion.{u} l Ω X).obj M) ((s.inclusion.{u} l Ω X).obj N)
  evaluationY (M N : C.{u} l Ω Y (s.stage l)) :
    (s.inclusion.{u} l Ω Y).map (d.closedY.evaluation M N) =
      tensorY.hom.app (d.homY.obj (op M, N), M) ≫
        modelY.closed.tensor.map (Prod.mkHom (homY.hom.app (op M, N)) (𝟙 _)) ≫
        modelY.closed.evaluation ((s.inclusion.{u} l Ω Y).obj M) ((s.inclusion.{u} l Ω Y).obj N)
  pull : d.pull ⋙ s.inclusion.{u} l Ω X ≅
    s.inclusion.{u} l Ω Y ⋙ PurCompactSupport.pull (s.coefficients l) f
  star : d.star ⋙ s.inclusion.{u} l Ω Y ≅
    s.inclusion.{u} l Ω X ⋙ PurCompactSupport.push (s.coefficients l) f
  adjunction (K : C.{u} l Ω Y (s.stage l)) (M : C.{u} l Ω X (s.stage l))
      (a : d.pull.obj K ⟶ M) :
    (s.inclusion.{u} l Ω Y).map (d.adjunction.homEquiv K M a) ≫ star.hom.app M =
      (proEtaleRingDerivedAdjunction f ((s.coefficients l).ring Y)
        ((s.coefficients l).ring X) ((s.coefficients l).pull f)).homEquiv _ _
          (pull.inv.app K ≫ (s.inclusion.{u} l Ω X).map a)

/-- Normalization of the projection used in the five-arrow chain by the actual
proper-counit/open-projection map, with its signed K-flat tensor realizations.
Source: blueprint proof step 5 (blueprint: fix-lem-tensor-adjunction). -/
structure Projection {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f) (s : RingStage.{u} l)
    {F : Operation.{u} l Ω X Y (s.stage l)} {d : Model l Ω (s.stage l) F}
    (r : RingModel l Ω f s d) (left : LeftRealization l Ω c s F) where
  tensorX : VerdierExchange.ProjectionTensor l X s r.modelX
  tensorY : VerdierExchange.ProjectionTensor l Y s r.modelY
  tensorBar : ProEtaleTensorModel c.Z ((s.coefficients l).ring c.Z)
  pullComposition : (s.coefficients l).pull (c.i ≫ c.g) =
    proEtaleRingCompositeCoefficients c.i c.g
      ((s.coefficients l).ring Y) ((s.coefficients l).ring c.Z)
      ((s.coefficients l).ring X) ((s.coefficients l).pull c.g) ((s.coefficients l).pull c.i)
  projectionIso (M : C.{u} l Ω X (s.stage l)) (K : C.{u} l Ω Y (s.stage l)) :
    r.modelY.closed.tensor.obj
        ((PurCompactSupport.image (s.coefficients l) c).obj ((s.inclusion.{u} l Ω X).obj M),
          (s.inclusion.{u} l Ω Y).obj K) ≅
      (PurCompactSupport.image (s.coefficients l) c).obj
        (r.modelX.closed.tensor.obj ((s.inclusion.{u} l Ω X).obj M,
          (PurCompactSupport.pull (s.coefficients l) f).obj ((s.inclusion.{u} l Ω Y).obj K)))
  projectionMap (M : C.{u} l Ω X (s.stage l)) (K : C.{u} l Ω Y (s.stage l)) :
    (projectionIso M K).hom =
      ((PurCompactSupport.projectionMap (s.coefficients l) c
        tensorX.toModel tensorBar tensorY.toModel pullComposition).app
          ((s.inclusion.{u} l Ω X).obj M)).app ((s.inclusion.{u} l Ω Y).obj K)
  normalized (K : C.{u} l Ω Y (s.stage l)) (M : C.{u} l Ω X (s.stage l)) :
    (s.inclusion.{u} l Ω Y).map (d.projection K M).hom =
      left.hom.app (d.closedX.tensor.obj (d.pull.obj K, M)) ≫
        (PurCompactSupport.image (s.coefficients l) c).map
          (r.tensorX.hom.app (d.pull.obj K, M) ≫
            r.modelX.closed.tensor.map (Prod.mkHom (r.pull.hom.app K) (𝟙 _)) ≫
            (r.modelX.symmetric.braiding
              ((PurCompactSupport.pull (s.coefficients l) f).obj ((s.inclusion.{u} l Ω Y).obj K))
              ((s.inclusion.{u} l Ω X).obj M)).hom) ≫
        (projectionIso M K).inv ≫
        (r.modelY.symmetric.braiding
          ((PurCompactSupport.image (s.coefficients l) c).obj ((s.inclusion.{u} l Ω X).obj M))
          ((s.inclusion.{u} l Ω Y).obj K)).hom ≫
        r.modelY.closed.tensor.map (Prod.mkHom (𝟙 _) (left.inv.app M)) ≫
        r.tensorY.inv.app (K, F.F.obj M)


/-- Realize both Hom shift variables by the existing signed-source and unsigned-target
Hom comparisons. These are conclusions, not extra shift hypotheses.
Source: blueprint proof step 8 (blueprint: fix-lem-tensor-adjunction). -/
structure RingShifts {X Y : Scheme.{u}} {f : X ⟶ Y} {s : RingStage.{u} l}
    {F : Operation.{u} l Ω X Y (s.stage l)} {d : Model l Ω (s.stage l) F}
    (r : RingModel l Ω f s d) (c : Conclusion l Ω d) where
  modelX (Q : C.{u} l Ω X (s.stage l)) :
    VerdierExchange.DualShiftModel l X s ((s.inclusion.{u} l Ω X).obj Q)
  modelY (Q : C.{u} l Ω Y (s.stage l)) :
    VerdierExchange.DualShiftModel l Y s ((s.inclusion.{u} l Ω Y).obj Q)
  firstX (Q : C.{u} l Ω X (s.stage l)) :
    (Functor.curry.obj d.homX).flip.obj Q ⋙ s.inclusion.{u} l Ω X ≅
      (s.inclusion.{u} l Ω X).op ⋙
        VerdierExchange.rawDual l X s ((s.inclusion.{u} l Ω X).obj Q)
  firstY (Q : C.{u} l Ω Y (s.stage l)) :
    (Functor.curry.obj d.homY).flip.obj Q ⋙ s.inclusion.{u} l Ω Y ≅
      (s.inclusion.{u} l Ω Y).op ⋙
        VerdierExchange.rawDual l Y s ((s.inclusion.{u} l Ω Y).obj Q)
  firstComponentsX (M Q : C.{u} l Ω X (s.stage l)) :
    (firstX Q).hom.app (op M) = r.homX.hom.app (op M, Q)
  firstComponentsY (M Q : C.{u} l Ω Y (s.stage l)) :
    (firstY Q).hom.app (op M) = r.homY.hom.app (op M, Q)
  firstShiftX (Q : C.{u} l Ω X (s.stage l)) :
    letI := c.homXFirst Q
    letI := (modelX Q).ambientShift
    (firstX Q).hom.CommShift ℤ
  firstShiftY (Q : C.{u} l Ω Y (s.stage l)) :
    letI := c.homYFirst Q
    letI := (modelY Q).ambientShift
    (firstY Q).hom.CommShift ℤ
  secondX (M : C.{u} l Ω X (s.stage l)) :
    (Functor.curry.obj d.homX).obj (op M) ⋙ s.inclusion.{u} l Ω X ≅
      s.inclusion.{u} l Ω X ⋙ CategoryTheory.RingedHomUniverses.hom.{u + 1, u, u}
        (ProEt.topology X) ((s.coefficients l).ring X) ((s.inclusion.{u} l Ω X).obj M)
  secondY (M : C.{u} l Ω Y (s.stage l)) :
    (Functor.curry.obj d.homY).obj (op M) ⋙ s.inclusion.{u} l Ω Y ≅
      s.inclusion.{u} l Ω Y ⋙ CategoryTheory.RingedHomUniverses.hom.{u + 1, u, u}
        (ProEt.topology Y) ((s.coefficients l).ring Y) ((s.inclusion.{u} l Ω Y).obj M)
  secondComponentsX (M Q : C.{u} l Ω X (s.stage l)) :
    (secondX M).hom.app Q = r.homX.hom.app (op M, Q)
  secondComponentsY (M Q : C.{u} l Ω Y (s.stage l)) :
    (secondY M).hom.app Q = r.homY.hom.app (op M, Q)
  secondShiftX (M : C.{u} l Ω X (s.stage l)) :
    letI := c.homXSecond (op M)
    (secondX M).hom.CommShift ℤ
  secondShiftY (M : C.{u} l Ω Y (s.stage l)) :
    letI := c.homYSecond (op M)
    (secondY M).hom.CommShift ℤ
  starShift : letI := c.starShift
    r.star.hom.CommShift ℤ

section Geometry
variable (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
  {X Y : Scheme.{u}} [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
  (f : X ⟶ Y) [f.IsOver (Spec (.of D.k))]
  [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
  (S : System.{u} l Ω D hl (f := f)) (c : Compactification f)

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

end Geometry

end TensorAdjunctionExchange
end WeilConjectures
