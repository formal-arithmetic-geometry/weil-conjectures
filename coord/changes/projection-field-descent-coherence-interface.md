# TensorCoherence and the projection endpoint comparisons

## Reason

The component-level tensor predicate used raw rational functors, while the supplied
coefficient comparisons use the named stage categories and coefficient functor
aliases. Adapting its two equations to the existing scalar-cocycle structure made
Lean unfold the cached category and the scalar-localization composition; repeated
single-file compiles timed out at that conversion. The stage-2 node review already
suggested reusing `ExchangeProjectionScalarCocycle`.

Store the identity and tower equations in that existing Prop structure, for each
square and space. Its fields are exactly the former two equations: every object
of the source product is a pair, `NatIso.prod` has component `Prod.mkHom`, and
uncurried tensor evaluates at `(M, N)` to the displayed iterated tensor object.
The quantifiers are regrouped, without dropping any field, object, inclusion or
tower. The third, common-stage inclusion equation is retained. This is an
equivalent predicate on the same supplied data, with no new choice or datum.

The endpoint functor uses `sixFunctorCoefficientRational` and
`sixFunctorCoefficientTensor` instead of their defining projection expressions.
These aliases are definitionally equal to their defining expressions. Use a Bool
match in `endpoint` and `commonEndpoint` so endpoint reduction does not depend on
the decidable proposition used by `if b then`. On `true` the functor is the source;
on `false` it is the target, exactly as before. It keeps the cached category
interfaces aligned through the endpoint calculations. The target meanings do not change:
the tensor predicate has the same identity, tower and inclusion requirements,
and each Bool endpoint is the same functor.

The endpoint isomorphisms are represented as components of
`sixFunctorCompositeRealization` of the support, pullback and tensor natural
isomorphisms. The private proved lemmas `sourceIso_formula` and
`targetIso_formula` identify them with the original component formulas verbatim.
This keeps the supplied endpoint maps unchanged, while avoiding repeated
expansion of concrete coefficient categories when applying the generic coherence
calculations. The old and new `transported` and `transportedInverse` maps are
therefore equal by these two lemmas; their definitions themselves are unchanged.

`EndpointCocycles` similarly stores the source and target scalar cocycles instead
of expanding their identity and tower fields in a Bool-indexed conjunction. The
source comparison is the natural composite of support × identity with tensor;
the target comparison is the composite of identity × pullback, tensor, and
support. By `sourceIso_formula` and `targetIso_formula` these are exactly the
previous endpoint isomorphisms. Every pair object is `(K, N)`; expanding the
`identity` and `composition` fields gives the old predicate, with Bool `true`
selecting the source and `false` selecting the target. The quantifiers only
regroup: both identity equations and both tower equations are retained.
No extra coherence is assumed. The predicate's old expanded representation
compiled its tactic proof quickly but kernel conversion exceeded 60 seconds;
the equivalent structure representation compiles the full file in 24.7 seconds.

Parenthesize the target functor as `(identity × pullback ⋙ tensor) ⋙ support`,
matching its natural-composite factorization. Functor composition on objects and
maps is associative definitionally; functor proof fields agree by proof
irrelevance. The private component-formula lemmas and naturality proof compile
with this presentation. No operation or morphism is replaced.

## Old

```lean
def TensorCoherence {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
    (A : SixFunctorCommonStages D C) : Prop :=
  (∀ (Q : SixFunctorCompactifiedSquare D) (X : SixFunctorSpace D)
    (E : Padic.FiniteCoefficientFields C.l C.Qbar)
    (M N : Stage C.l C.Qbar X.obj.left E),
    ((A.coefficientExchangeComparison (le_rfl : E ≤ E) Q).tensor X).hom.app (M, N) ≫
        (Functor.uncurry.obj ((A.coefficientStages E).rationalTensor X)).map
          (Prod.mkHom ((sixFunctorStageUnitor D C X E).hom.app M)
            ((sixFunctorStageUnitor D C X E).hom.app N)) =
      (sixFunctorStageUnitor D C X E).hom.app
        (((A.coefficientStages E).rationalTensor X).obj M |>.obj N)) ∧
  (∀ (Q : SixFunctorCompactifiedSquare D) (X : SixFunctorSpace D)
    (E F G : Padic.FiniteCoefficientFields C.l C.Qbar) (h : E ≤ F) (h' : F ≤ G)
    (M N : Stage C.l C.Qbar X.obj.left E),
    ((stageSystem C.l C.Qbar X.obj.left).T h').map
        (((A.coefficientExchangeComparison h Q).tensor X).hom.app (M, N)) ≫
        ((A.coefficientExchangeComparison h' Q).tensor X).hom.app
          (((stageSystem C.l C.Qbar X.obj.left).T h).obj M,
            ((stageSystem C.l C.Qbar X.obj.left).T h).obj N) ≫
        (Functor.uncurry.obj ((A.coefficientStages G).rationalTensor X)).map
          (Prod.mkHom (((stageSystem C.l C.Qbar X.obj.left).assoc h h').hom.app M)
            (((stageSystem C.l C.Qbar X.obj.left).assoc h h').hom.app N)) =
      ((stageSystem C.l C.Qbar X.obj.left).assoc h h').hom.app
          (((A.coefficientStages E).rationalTensor X).obj M |>.obj N) ≫
        ((A.coefficientExchangeComparison (h.trans h') Q).tensor X).hom.app (M, N)) ∧
  (∀ (Q : SixFunctorCompactifiedSquare D) (X : SixFunctorSpace D)
    (E F : Padic.FiniteCoefficientFields C.l C.Qbar) (h : E ≤ F)
    (M N : Stage C.l C.Qbar X.obj.left E),
    (Functor.uncurry.obj (A.commonStageTensor X)).map
        (Prod.mkHom (((stageSystem C.l C.Qbar X.obj.left).transIso h).hom.app M)
          (((stageSystem C.l C.Qbar X.obj.left).transIso h).hom.app N)) ≫
        ((A.commonStageExchangeComparison E Q).tensor X).inv.app (M, N) =
      ((A.commonStageExchangeComparison F Q).tensor X).inv.app
          (((stageSystem C.l C.Qbar X.obj.left).T h).obj M,
            ((stageSystem C.l C.Qbar X.obj.left).T h).obj N) ≫
        (inclusion (l := C.l) (Ω := C.Qbar) (Y := X.obj.left) F).map
          (((A.coefficientExchangeComparison h Q).tensor X).inv.app (M, N)) ≫
        ((stageSystem C.l C.Qbar X.obj.left).transIso h).hom.app
          (((A.coefficientStages E).rationalTensor X).obj M |>.obj N))

def target (S : SixFunctorPushStage D B) (T : ∀ X, B X ⥤ B X ⥤ B X)
    (Q : SixFunctorCompactifiedSquare D) : B Q.X × B Q.Y ⥤ B Q.Y :=
  (𝟭 _).prod (S.pull Q.f) ⋙ Functor.uncurry.obj (T Q.X) ⋙ S.support Q.f Q.compactification

def sourceIso (e : SixFunctorExchangeComparison A A' L C) (K : B Q.X) (N : B Q.Y) :
    (L Q.Y).obj ((source S T Q).obj (K, N)) ≅
      (source S' T' Q).obj ((L Q.X).obj K, (L Q.Y).obj N) :=
  (e.tensor Q.Y).app ((S.support Q.f Q.compactification).obj K, N) ≪≫
    (Functor.uncurry.obj (T' Q.Y)).mapIso
      (Iso.prod ((C.supportAdjunction Q.f Q.compactification).left.app K) (Iso.refl _))

def targetIso (e : SixFunctorExchangeComparison A A' L C) (K : B Q.X) (N : B Q.Y) :
    (L Q.Y).obj ((target S T Q).obj (K, N)) ≅
      (target S' T' Q).obj ((L Q.X).obj K, (L Q.Y).obj N) :=
  (C.supportAdjunction Q.f Q.compactification).left.app
      (((T Q.X).obj K).obj ((S.pull Q.f).obj N)) ≪≫
    (S'.support Q.f Q.compactification).mapIso
      ((e.tensor Q.X).app (K, (S.pull Q.f).obj N) ≪≫
        (Functor.uncurry.obj (T' Q.X)).mapIso
          (Iso.prod (Iso.refl _) ((C.directAdjunction Q.f).left.app N)))

def endpoint {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
    (A : SixFunctorCommonStages D C) (Q : SixFunctorCompactifiedSquare D) (b : Bool)
    (E : Padic.FiniteCoefficientFields C.l C.Qbar) :=
  if b then source (A.coefficientStages E).rational (A.coefficientStages E).rationalTensor Q
  else target (A.coefficientStages E).rational (A.coefficientStages E).rationalTensor Q

def EndpointCocycles {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
    (A : SixFunctorCommonStages D C) (Q : SixFunctorCompactifiedSquare D) : Prop :=
  (∀ (b : Bool) (E : Padic.FiniteCoefficientFields C.l C.Qbar)
    (K : Stage C.l C.Qbar Q.X.obj.left E) (N : Stage C.l C.Qbar Q.Y.obj.left E),
    (endpointIso A Q b (le_rfl : E ≤ E) K N).hom ≫
        (endpoint A Q b E).map
          (Prod.mkHom ((sixFunctorStageUnitor D C Q.X E).hom.app K)
            ((sixFunctorStageUnitor D C Q.Y E).hom.app N)) =
      (sixFunctorStageUnitor D C Q.Y E).hom.app ((endpoint A Q b E).obj (K, N))) ∧
  (∀ (b : Bool) (E F G : Padic.FiniteCoefficientFields C.l C.Qbar)
    (h : E ≤ F) (h' : F ≤ G)
    (K : Stage C.l C.Qbar Q.X.obj.left E) (N : Stage C.l C.Qbar Q.Y.obj.left E),
    ((stageSystem C.l C.Qbar Q.Y.obj.left).T h').map (endpointIso A Q b h K N).hom ≫
        (endpointIso A Q b h'
          (((stageSystem C.l C.Qbar Q.X.obj.left).T h).obj K)
          (((stageSystem C.l C.Qbar Q.Y.obj.left).T h).obj N)).hom ≫
        (endpoint A Q b G).map
          (Prod.mkHom (((stageSystem C.l C.Qbar Q.X.obj.left).assoc h h').hom.app K)
            (((stageSystem C.l C.Qbar Q.Y.obj.left).assoc h h').hom.app N)) =
      ((stageSystem C.l C.Qbar Q.Y.obj.left).assoc h h').hom.app
          ((endpoint A Q b E).obj (K, N)) ≫
        (endpointIso A Q b (h.trans h') K N).hom)

def commonEndpoint {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
    (A : SixFunctorCommonStages D C) (Q : SixFunctorCompactifiedSquare D) (b : Bool) :=
  if b then source A.commonStage A.commonStageTensor Q
  else target A.commonStage A.commonStageTensor Q
```

## New

```lean
def TensorCoherence {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
    (A : SixFunctorCommonStages D C) : Prop :=
  (∀ (Q : SixFunctorCompactifiedSquare D) (X : SixFunctorSpace D),
    ExchangeProjectionScalarCocycle
      (fun E ↦ Stage C.l C.Qbar X.obj.left E × Stage C.l C.Qbar X.obj.left E)
      (fun E ↦ Stage C.l C.Qbar X.obj.left E)
      (fun E ↦ Functor.uncurry.obj
        (sixFunctorCoefficientTensor D C A.coefficientStages E X))
      (fun _ _ h ↦ ((stageSystem C.l C.Qbar X.obj.left).T h).prod
        ((stageSystem C.l C.Qbar X.obj.left).T h))
      (fun _ _ h ↦ (stageSystem C.l C.Qbar X.obj.left).T h)
      (fun E ↦ NatIso.prod (sixFunctorStageUnitor D C X E)
        (sixFunctorStageUnitor D C X E))
      (sixFunctorStageUnitor D C X)
      (fun _ _ _ h h' ↦ NatIso.prod ((stageSystem C.l C.Qbar X.obj.left).assoc h h')
        ((stageSystem C.l C.Qbar X.obj.left).assoc h h'))
      (fun _ _ _ h h' ↦ (stageSystem C.l C.Qbar X.obj.left).assoc h h')
      (fun _ _ h ↦ (A.coefficientExchangeComparison h Q).tensor X)) ∧
  (∀ (Q : SixFunctorCompactifiedSquare D) (X : SixFunctorSpace D)
    (E F : Padic.FiniteCoefficientFields C.l C.Qbar) (h : E ≤ F)
    (M N : Stage C.l C.Qbar X.obj.left E),
    (Functor.uncurry.obj (A.commonStageTensor X)).map
        (Prod.mkHom (((stageSystem C.l C.Qbar X.obj.left).transIso h).hom.app M)
          (((stageSystem C.l C.Qbar X.obj.left).transIso h).hom.app N)) ≫
        ((A.commonStageExchangeComparison E Q).tensor X).inv.app (M, N) =
      ((A.commonStageExchangeComparison F Q).tensor X).inv.app
          (((stageSystem C.l C.Qbar X.obj.left).T h).obj M,
            ((stageSystem C.l C.Qbar X.obj.left).T h).obj N) ≫
        (inclusion (l := C.l) (Ω := C.Qbar) (Y := X.obj.left) F).map
          (((A.coefficientExchangeComparison h Q).tensor X).inv.app (M, N)) ≫
        ((stageSystem C.l C.Qbar X.obj.left).transIso h).hom.app
          ((sixFunctorCoefficientTensor D C A.coefficientStages E X).obj M |>.obj N))

def target (S : SixFunctorPushStage D B) (T : ∀ X, B X ⥤ B X ⥤ B X)
    (Q : SixFunctorCompactifiedSquare D) : B Q.X × B Q.Y ⥤ B Q.Y :=
  ((𝟭 _).prod (S.pull Q.f) ⋙ Functor.uncurry.obj (T Q.X)) ⋙
    S.support Q.f Q.compactification

def sourceIso (e : SixFunctorExchangeComparison A A' L C) (K : B Q.X) (N : B Q.Y) :
    (L Q.Y).obj ((source S T Q).obj (K, N)) ≅
      (source S' T' Q).obj ((L Q.X).obj K, (L Q.Y).obj N) :=
  (sixFunctorCompositeRealization
    (F := (S.support Q.f Q.compactification).prod (𝟭 (B Q.Y)))
    (F' := (S'.support Q.f Q.compactification).prod (𝟭 (B' Q.Y)))
    (LA := (L Q.X).prod (L Q.Y)) (LB := (L Q.Y).prod (L Q.Y))
    (NatIso.prod (C.supportAdjunction Q.f Q.compactification).left (Iso.refl (L Q.Y)))
    (e.tensor Q.Y)).app (K, N)

def targetIso (e : SixFunctorExchangeComparison A A' L C) (K : B Q.X) (N : B Q.Y) :
    (L Q.Y).obj ((target S T Q).obj (K, N)) ≅
      (target S' T' Q).obj ((L Q.X).obj K, (L Q.Y).obj N) :=
  (sixFunctorCompositeRealization
    (sixFunctorCompositeRealization
      (F := (𝟭 (B Q.X)).prod (S.pull Q.f))
      (F' := (𝟭 (B' Q.X)).prod (S'.pull Q.f))
      (LA := (L Q.X).prod (L Q.Y)) (LB := (L Q.X).prod (L Q.X))
      (NatIso.prod (Iso.refl (L Q.X)) (C.directAdjunction Q.f).left) (e.tensor Q.X))
    (C.supportAdjunction Q.f Q.compactification).left).app (K, N)

def endpoint {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
    (A : SixFunctorCommonStages D C) (Q : SixFunctorCompactifiedSquare D) (b : Bool)
    (E : Padic.FiniteCoefficientFields C.l C.Qbar) :
    Stage C.l C.Qbar Q.X.obj.left E × Stage C.l C.Qbar Q.Y.obj.left E ⥤
      Stage C.l C.Qbar Q.Y.obj.left E :=
  match b with
  | true => source (sixFunctorCoefficientRational D C A.coefficientStages E)
      (sixFunctorCoefficientTensor D C A.coefficientStages E) Q
  | false => target (sixFunctorCoefficientRational D C A.coefficientStages E)
      (sixFunctorCoefficientTensor D C A.coefficientStages E) Q

def EndpointCocycles {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
    (A : SixFunctorCommonStages D C) (Q : SixFunctorCompactifiedSquare D) : Prop :=
  ExchangeProjectionScalarCocycle
      (fun E ↦ Stage C.l C.Qbar Q.X.obj.left E × Stage C.l C.Qbar Q.Y.obj.left E)
      (fun E ↦ Stage C.l C.Qbar Q.Y.obj.left E)
      (fun E ↦ source (sixFunctorCoefficientRational D C A.coefficientStages E)
        (sixFunctorCoefficientTensor D C A.coefficientStages E) Q)
      (fun _ _ h ↦ ((stageSystem C.l C.Qbar Q.X.obj.left).T h).prod
        ((stageSystem C.l C.Qbar Q.Y.obj.left).T h))
      (fun _ _ h ↦ (stageSystem C.l C.Qbar Q.Y.obj.left).T h)
      (fun E ↦ NatIso.prod (sixFunctorStageUnitor D C Q.X E)
        (sixFunctorStageUnitor D C Q.Y E))
      (sixFunctorStageUnitor D C Q.Y)
      (fun _ _ _ h h' ↦ NatIso.prod ((stageSystem C.l C.Qbar Q.X.obj.left).assoc h h')
        ((stageSystem C.l C.Qbar Q.Y.obj.left).assoc h h'))
      (fun _ _ _ h h' ↦ (stageSystem C.l C.Qbar Q.Y.obj.left).assoc h h')
      (fun _ _ h ↦ sixFunctorCompositeRealization
        (F := ((sixFunctorCoefficientRational D C A.coefficientStages _).support
          Q.f Q.compactification).prod (𝟭 _))
        (F' := ((sixFunctorCoefficientRational D C A.coefficientStages _).support
          Q.f Q.compactification).prod (𝟭 _))
        (LA := ((stageSystem C.l C.Qbar Q.X.obj.left).T h).prod
          ((stageSystem C.l C.Qbar Q.Y.obj.left).T h))
        (LB := ((stageSystem C.l C.Qbar Q.Y.obj.left).T h).prod
          ((stageSystem C.l C.Qbar Q.Y.obj.left).T h))
        (NatIso.prod ((A.coefficientTransition h).supportAdjunction
          Q.f Q.compactification).left
          (Iso.refl ((stageSystem C.l C.Qbar Q.Y.obj.left).T h)))
        ((A.coefficientExchangeComparison h Q).tensor Q.Y)) ∧
  ExchangeProjectionScalarCocycle
      (fun E ↦ Stage C.l C.Qbar Q.X.obj.left E × Stage C.l C.Qbar Q.Y.obj.left E)
      (fun E ↦ Stage C.l C.Qbar Q.Y.obj.left E)
      (fun E ↦ target (sixFunctorCoefficientRational D C A.coefficientStages E)
        (sixFunctorCoefficientTensor D C A.coefficientStages E) Q)
      (fun _ _ h ↦ ((stageSystem C.l C.Qbar Q.X.obj.left).T h).prod
        ((stageSystem C.l C.Qbar Q.Y.obj.left).T h))
      (fun _ _ h ↦ (stageSystem C.l C.Qbar Q.Y.obj.left).T h)
      (fun E ↦ NatIso.prod (sixFunctorStageUnitor D C Q.X E)
        (sixFunctorStageUnitor D C Q.Y E))
      (sixFunctorStageUnitor D C Q.Y)
      (fun _ _ _ h h' ↦ NatIso.prod ((stageSystem C.l C.Qbar Q.X.obj.left).assoc h h')
        ((stageSystem C.l C.Qbar Q.Y.obj.left).assoc h h'))
      (fun _ _ _ h h' ↦ (stageSystem C.l C.Qbar Q.Y.obj.left).assoc h h')
      (fun _ _ h ↦ sixFunctorCompositeRealization
        (sixFunctorCompositeRealization
          (F := (𝟭 _).prod
            ((sixFunctorCoefficientRational D C A.coefficientStages _).pull Q.f))
          (F' := (𝟭 _).prod
            ((sixFunctorCoefficientRational D C A.coefficientStages _).pull Q.f))
          (LA := ((stageSystem C.l C.Qbar Q.X.obj.left).T h).prod
            ((stageSystem C.l C.Qbar Q.Y.obj.left).T h))
          (LB := ((stageSystem C.l C.Qbar Q.X.obj.left).T h).prod
            ((stageSystem C.l C.Qbar Q.X.obj.left).T h))
          (NatIso.prod (Iso.refl ((stageSystem C.l C.Qbar Q.X.obj.left).T h))
            ((A.coefficientTransition h).directAdjunction Q.f).left)
          ((A.coefficientExchangeComparison h Q).tensor Q.X))
        ((A.coefficientTransition h).supportAdjunction Q.f Q.compactification).left)

def commonEndpoint {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
    (A : SixFunctorCommonStages D C) (Q : SixFunctorCompactifiedSquare D) (b : Bool) :=
  match b with
  | true => source A.commonStage A.commonStageTensor Q
  | false => target A.commonStage A.commonStageTensor Q
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| `Sheaf.Paper.ProjectionTensorCoefficientCocycles` | unclaimed | Equivalent representation of the predicate; its signature and imports stay unchanged. |
| `Sheaf.Paper.ConcreteProjectionFieldDescent` | A2 | Consume the scalar cocycle directly and use the inclusion conjunct at its new projection; normalize the endpoint aliases and represent endpoint comparisons by natural composites, proved equal to their old formulas. |

A repository search and `tools/downstream.py --uses TensorCoherence` find no
other consumer of this namespaced predicate. The endpoint, endpoint-cocycle and comparison declarations have no
external textual users; their public types retain the same categories, and each Bool branch is unchanged. No
module held by another group is adapted. All original theorem signatures remain
unchanged. `endpoint` has an explicit annotation of its already inferred functor type. Both changed modules are compiled together before delivery. The item then
compiled in 24.7 seconds against the sandbox predicate module; the clean
non-profiled sources are checked again by delivery preflight.

## Status

landed 20261025T163526-L-690519 2026-10-25 (merge of deliver/A2/Sheaf.Paper.ConcreteProjectionFieldDescent)
