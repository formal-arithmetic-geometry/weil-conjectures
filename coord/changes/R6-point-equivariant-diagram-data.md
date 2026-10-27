# Point-equivariant diagram data extraction

## Reason

The original-field construction and the two independent coefficient-extension lemmas
need the same diagram predicates. Extract their unchanged definitions to prevent an
import cycle between those new statement modules and the assembly theorem.
No statement, definition body, universe or visibility changes.

## Old

The following definitions were declared in `Sheaf.Paper.PointEquivariantDiagramLift`:

```lean
/-- H^0 of the recorded rational point fibre, on objects and arrows.
Source: paragraph 7 (blueprint: lem-zl-point-equivariant-diagram-lift). -/
def zlDiagramFiber : sfRationalConstructibleCategory l E (Spec (.of D.k)) ⥤ ModuleCat.{u} E :=
  pointRationalFibre D l hl E ⋙ DerivedCategory.coefficientFdCohomology E 0

/-- The actual geometric-Frobenius pullback, with inherited prime invertibility.
Source: paragraph 7 (blueprint: lem-zl-point-equivariant-diagram-lift). -/
def zlDiagramPullback : sfRationalConstructibleCategory l E (Spec (.of D.k)) ⥤
    sfRationalConstructibleCategory l E (Spec (.of D.k)) :=
  @rationalDerivedPullback l _ E _ _ _ _ _ (frobeniusPointIso D).hom
    (frobeniusPointPrimeInvertible D l hl) (frobeniusPointPrimeInvertible D l hl)

/-- H^0(iota), including the specified comparison to the actual pullback object.
Source: paragraph 7 (blueprint: lem-zl-point-equivariant-diagram-lift). -/
def zlDiagramTransport (K : sfRationalConstructibleCategory l E (Spec (.of D.k))) :
    (zlDiagramFiber D l hl E).obj K ⟶
      (zlDiagramFiber D l hl E).obj ((zlDiagramPullback D l hl E).obj K) :=
  (DerivedCategory.coefficientFdCohomology E 0).map (localPointTransport l E D hl K)

/-- The actual Weil fixed pair attached to one component of the lifted diagram.
This uses the recorded IsoAlgebra construction, rather than a second Weil-pair notion.
Source: paragraph 7 (blueprint: lem-zl-point-equivariant-diagram-lift). -/
def zlDiagramWeilObject (K : sfRationalConstructibleCategory l E (Spec (.of D.k)))
    (theta : (zlDiagramPullback D l hl E).obj K ≅ K) :
    CategoryTheory.Endofunctor.IsoAlgebra (zlDiagramPullback D l hl E) :=
  CategoryTheory.Endofunctor.IsoAlgebra.mk K theta

/-- A natural isomorphism T(G) to G gives the diagram in the recorded fixed-pair
category, retaining the underlying arrows exactly. Naturality supplies their Weil squares.
Source: paragraph 7 (blueprint: lem-zl-point-equivariant-diagram-lift). -/
def zlDiagramWeilFunctor {I : Type w} [Category.{vI} I]
    (G : I ⥤ sfRationalConstructibleCategory l E (Spec (.of D.k)))
    (theta : G ⋙ zlDiagramPullback D l hl E ≅ G) :
    I ⥤ CategoryTheory.Endofunctor.IsoAlgebra (zlDiagramPullback D l hl E) where
  obj i := zlDiagramWeilObject D l hl E (G.obj i) (theta.app i)
  map f := ObjectProperty.homMk
    { f := G.map f
      h := theta.hom.naturality f }
  map_id i := InducedCategory.hom_ext
    (CategoryTheory.Endofunctor.Algebra.ext (G.map_id i))
  map_comp f g := InducedCategory.hom_ext
    (CategoryTheory.Endofunctor.Algebra.ext (G.map_comp f g))

/-- The raw-heart lift of a diagram whose objects are in the heart; maps are unchanged.
Source: paragraph 7 (blueprint: lem-zl-point-equivariant-diagram-lift). -/
def zlDiagramHeart {I : Type w} [Category.{vI} I]
    (G : I ⥤ sfRationalConstructibleCategory l E (Spec (.of D.k)))
    (hG : ∀ i, sfRationalHeartProperty l E (Spec (.of D.k)) (G.obj i)) :
    I ⥤ sfRationalHeart l E (Spec (.of D.k)) :=
  (sfRationalHeartProperty l E (Spec (.of D.k))).lift G hG

/-- Preservation of every short exact sequence, mono and cokernel occurring in a diagram.
Quantifying over all short exact triples includes every finite designated collection.
All equations between parallel arrows are retained. The cokernel clause is its
universal property, not just a zero composite.
Source: paragraph 7 (blueprint: lem-zl-point-equivariant-diagram-lift). -/
def ZlDiagramExactRealization {I : Type w} [Category.{vI} I]
    {C : Type uC} [Category.{vC} C] [HasZeroMorphisms C]
    {F : Type u} [Field F] (G : I ⥤ C) (V : I ⥤ ModuleCat.{u} F) : Prop :=
  (∀ {i j : I} (f g : i ⟶ j), V.map f = V.map g → G.map f = G.map g) ∧
  (∀ {i j : I} (f : i ⟶ j), Mono (V.map f) → Mono (G.map f)) ∧
  (∀ {i j k : I} (f : i ⟶ j) (g : j ⟶ k) (hz : V.map f ≫ V.map g = 0),
    (ShortComplex.mk (V.map f) (V.map g) hz).ShortExact →
      ∃ h : G.map f ≫ G.map g = 0,
        (ShortComplex.mk (G.map f) (G.map g) h).ShortExact) ∧
  (∀ {i j k : I} (f : i ⟶ j) (g : j ⟶ k) (hz : V.map f ≫ V.map g = 0),
    Nonempty (IsColimit (CokernelCofork.ofπ (V.map g) hz)) →
      ∃ h : G.map f ≫ G.map g = 0,
        Nonempty (IsColimit (CokernelCofork.ofπ (G.map g) h)))

/-- The fibre formulas for a diagram of Weil pairs. Naturality of theta is precisely
f theta_i = theta_j T(f). The last equation identifies the degree-one local Frobenius.
Source: paragraph 7 (blueprint: lem-zl-point-equivariant-diagram-lift). -/
def ZlPointDiagramRealization {I : Type w} [Category.{vI} I]
    (V : I ⥤ ModuleCat.{u} E) (A : ∀ i, V.obj i ≅ V.obj i)
    (G : I ⥤ sfRationalConstructibleCategory l E (Spec (.of D.k)))
    (hG : ∀ i, sfRationalHeartProperty l E (Spec (.of D.k)) (G.obj i))
    (theta : G ⋙ zlDiagramPullback D l hl E ≅ G)
    (eta : G ⋙ zlDiagramFiber D l hl E ≅ V)
    (t : ∀ i, (zlDiagramFiber D l hl E).obj (G.obj i) ≅
      (zlDiagramFiber D l hl E).obj ((zlDiagramPullback D l hl E).obj (G.obj i))) : Prop :=
  ZlDiagramExactRealization (zlDiagramHeart D l E G hG) V ∧
  ∀ i,
    (t i).hom = zlDiagramTransport D l hl E (G.obj i) ∧
    (zlDiagramFiber D l hl E).map (theta.app i).hom =
      (t i).inv ≫ (eta.app i).hom ≫ (A i).hom ≫ (eta.app i).inv ∧
    (zlDiagramFiber D l hl E).map (theta.app i).inv =
      (eta.app i).hom ≫ (A i).inv ≫ (eta.app i).inv ≫ (t i).hom ∧
    (eta.app i).inv ≫ (t i).hom ≫
      (zlDiagramFiber D l hl E).map (theta.app i).hom ≫ (eta.app i).hom = (A i).hom

variable (L : Type u) [Field L] [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
  (ι : E →ₐ[Padic l] L)

/-- The specified H^0 scalar comparison: first the point-fibre comparison, then
cohomology of exact scalar extension. This fixes identity and tower normalizations.
Source: paragraph 7 (blueprint: lem-zl-point-equivariant-diagram-lift). -/
def zlDiagramScalarFiber (K : sfRationalConstructibleCategory l E (Spec (.of D.k))) :
    (zlDiagramFiber D l hl L).obj
        ((sfRationalScalarExtension l E (Spec (.of D.k)) 0
          (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι).obj K) ≅
      (ModuleCat.extendScalars ι.toRingHom).obj ((zlDiagramFiber D l hl E).obj K) :=
  (DerivedCategory.coefficientFdCohomology L 0).mapIso
      ((pointRationalFibreScalarIso D l hl E L ι).app K) ≪≫
    (DerivedCategory.fieldDerivedHomologyIso ι.toRingHom 0).app
      ((pointRationalFibre D l hl E).obj K).obj

/-- The specified pullback/scalar comparison with prime invertibility inherited from D.
Source: paragraph 7 (blueprint: lem-zl-point-equivariant-diagram-lift). -/
def zlDiagramScalarPullback :=
  @rationalPullbackScalarComparison l _ E _ _ _ L _ _ _ ι _ _ (frobeniusPointIso D).hom
    (frobeniusPointPrimeInvertible D l hl) (frobeniusPointPrimeInvertible D l hl)

variable (Ω : Type u) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]

/-- H^0 of the specified common-stage point fibre.
Source: paragraph 7 (blueprint: lem-zl-point-equivariant-diagram-lift). -/
def zlDiagramQbarFiber :
    generalAlgebraicallyClosedConstructibleCategory l Ω (Spec (.of D.k)) ⥤ ModuleCat.{u} Ω :=
  pointQbarFibre D l hl Ω ⋙ DerivedCategory.coefficientQbarCohomology l Ω 0

/-- Actual Frobenius pullback on literal common-stage pairs.
Source: paragraph 7 (blueprint: lem-zl-point-equivariant-diagram-lift). -/
def zlDiagramQbarPullback :=
  @commonStageDerivedPullback l _ Ω _ _ _ _ _ (frobeniusPointIso D).hom
    (frobeniusPointPrimeInvertible D l hl) (frobeniusPointPrimeInvertible D l hl)

/-- The specified H^0 point transport at common-stage coefficients.
Source: paragraph 7 (blueprint: lem-zl-point-equivariant-diagram-lift). -/
def zlDiagramQbarTransport
    (K : generalAlgebraicallyClosedConstructibleCategory l Ω (Spec (.of D.k))) :=
  (DerivedCategory.coefficientQbarCohomology l Ω 0).map
    (localQbarPointTransport l Ω D hl K)

/-- Pullback of a literal finite-stage object, with the published object comparison.
Source: paragraph 7 (blueprint: lem-zl-point-equivariant-diagram-lift). -/
def zlDiagramStagePullback (F : Padic.FiniteCoefficientFields l Ω)
    (K : GeneralAlgebraicallyClosedCoefficients.Stage l Ω (Spec (.of D.k)) F) :
    (zlDiagramQbarPullback D l hl Ω).obj
        ((GeneralAlgebraicallyClosedCoefficients.inclusion F).obj K) ≅
      (GeneralAlgebraicallyClosedCoefficients.inclusion F).obj
        ((zlDiagramPullback D l hl
          (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω F)).obj K) :=
  @localQbarPullbackStageIso l _ Ω _ _ _ _ _ (frobeniusPointIso D).hom
    (frobeniusPointPrimeInvertible D l hl) (frobeniusPointPrimeInvertible D l hl)
    ((GeneralAlgebraicallyClosedCoefficients.inclusion F).obj K)

/-- The canonical common-stage H^0 comparison, including Shrink and the tensor tower.
Source: paragraph 7 (blueprint: lem-zl-point-equivariant-diagram-lift). -/
def zlDiagramStageFiber (F : Padic.FiniteCoefficientFields l Ω)
    (K : GeneralAlgebraicallyClosedCoefficients.Stage l Ω (Spec (.of D.k)) F) :
    (zlDiagramQbarFiber D l hl Ω).obj
        ((GeneralAlgebraicallyClosedCoefficients.inclusion F).obj K) ≅
      (ModuleCat.extendScalars
        (F.val.subtype.comp (Shrink.algEquiv (Padic l) F.val).toRingHom)).obj
        ((zlDiagramFiber D l hl
          (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω F)).obj K) := by
  let C := (pointRationalFibre D l hl
    (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω F)).obj K
  let e := (Shrink.algEquiv (Padic l) F.val).toRingHom
  let a : (DerivedCategory.coefficientQbarCohomology l Ω 0).obj
      ((pointQbarFibre D l hl Ω).obj
        ((GeneralAlgebraicallyClosedCoefficients.inclusion F).obj K)) ≅
      (DerivedCategory.coefficientQbarCohomology l Ω 0).obj
        (pointQbarFibreObj D l hl Ω
          ((GeneralAlgebraicallyClosedCoefficients.inclusion F).obj K)) :=
    (DerivedCategory.coefficientQbarCohomology l Ω 0).mapIso
      (localQbarFibreObjIso l Ω D hl
        ((GeneralAlgebraicallyClosedCoefficients.inclusion F).obj K))
  let b := (DerivedCategory.fieldDerivedHomologyIso e 0).app C.obj
  let c := (ModuleCat.extendScalars F.val.subtype).mapIso b
  let d := ((ModuleCat.extendScalarsComp e F.val.subtype).app
    ((DerivedCategory.homologyFunctor (ModuleCat.{u}
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω F)) 0).obj C.obj)).symm
  exact a ≪≫ c ≪≫ d

/-- Extension of the entire lifted diagram to a finite coefficient field, using the
specified scalar/fibre and scalar/pullback comparisons. The transport square fixes
H^0(iota_L) as extension of H^0(iota_E), including the source pullback comparison.
Source: paragraph 7 (blueprint: lem-zl-point-equivariant-diagram-lift). -/
def ZlFiniteScalarDiagram {I : Type w} [Category.{vI} I]
    (V : I ⥤ ModuleCat.{u} E) (A : ∀ i, V.obj i ≅ V.obj i)
    (G : I ⥤ sfRationalConstructibleCategory l E (Spec (.of D.k)))
    (theta : G ⋙ zlDiagramPullback D l hl E ≅ G)
    (eta : G ⋙ zlDiagramFiber D l hl E ≅ V)
    (t : ∀ i, (zlDiagramFiber D l hl E).obj (G.obj i) ≅
      (zlDiagramFiber D l hl E).obj ((zlDiagramPullback D l hl E).obj (G.obj i))) : Prop :=
  ∃ (hL : ∀ i, sfRationalHeartProperty l L (Spec (.of D.k))
      ((sfRationalScalarExtension l E (Spec (.of D.k)) 0
        (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι).obj (G.obj i)))
    (thetaL : (G ⋙ sfRationalScalarExtension l E (Spec (.of D.k)) 0
      (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι) ⋙ zlDiagramPullback D l hl L ≅
        G ⋙ sfRationalScalarExtension l E (Spec (.of D.k)) 0
          (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι)
    (etaL : (G ⋙ sfRationalScalarExtension l E (Spec (.of D.k)) 0
      (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι) ⋙ zlDiagramFiber D l hl L ≅
        V ⋙ ModuleCat.extendScalars ι.toRingHom)
    (tL : ∀ i, (zlDiagramFiber D l hl L).obj
      ((sfRationalScalarExtension l E (Spec (.of D.k)) 0
        (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι).obj (G.obj i)) ≅
      (zlDiagramFiber D l hl L).obj ((zlDiagramPullback D l hl L).obj
        ((sfRationalScalarExtension l E (Spec (.of D.k)) 0
          (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι).obj (G.obj i)))),
    ZlPointDiagramRealization D l hl L (V ⋙ ModuleCat.extendScalars ι.toRingHom)
      (fun i ↦ (ModuleCat.extendScalars ι.toRingHom).mapIso (A i))
      (G ⋙ sfRationalScalarExtension l E (Spec (.of D.k)) 0
        (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι) hL thetaL etaL tL ∧
    ∀ i,
      thetaL.app i = (zlDiagramScalarPullback D l hl E L ι).symm.app (G.obj i) ≪≫
        (sfRationalScalarExtension l E (Spec (.of D.k)) 0
          (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι).mapIso (theta.app i) ∧
      etaL.app i = zlDiagramScalarFiber D l hl E L ι (G.obj i) ≪≫
        (ModuleCat.extendScalars ι.toRingHom).mapIso (eta.app i) ∧
      (tL i).hom ≫ (zlDiagramFiber D l hl L).map
          ((zlDiagramScalarPullback D l hl E L ι).inv.app (G.obj i)) ≫
          (zlDiagramScalarFiber D l hl E L ι
            ((zlDiagramPullback D l hl E).obj (G.obj i))).hom =
        (zlDiagramScalarFiber D l hl E L ι (G.obj i)).hom ≫
          (ModuleCat.extendScalars ι.toRingHom).map (t i).hom

/-- Literal common-stage images of the whole diagram, with canonical scalar comparisons,
exactness, inverse Weil maps, transport compatibility and the scalar-extended Frobenius.
The stage is the original F throughout; no coefficient enlargement is allowed here.
Source: paragraph 7 (blueprint: lem-zl-point-equivariant-diagram-lift). -/
def ZlCommonStageDiagram {I : Type w} [Category.{vI} I]
    (F : Padic.FiniteCoefficientFields l Ω)
    (V : I ⥤ ModuleCat.{u} (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω F))
    (A : ∀ i, V.obj i ≅ V.obj i)
    (G : I ⥤ GeneralAlgebraicallyClosedCoefficients.Stage l Ω (Spec (.of D.k)) F)
    (theta : G ⋙ zlDiagramPullback D l hl
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω F) ≅ G)
    (eta : G ⋙ zlDiagramFiber D l hl
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω F) ≅ V)
    (t : ∀ i, (zlDiagramFiber D l hl
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω F)).obj (G.obj i) ≅
      (zlDiagramFiber D l hl (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω F)).obj
        ((zlDiagramPullback D l hl
          (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω F)).obj (G.obj i))) : Prop :=
  ∃ (hΩ : ∀ i, sfCommonStageHeartProperty l (Spec (.of D.k)) Ω
      ((GeneralAlgebraicallyClosedCoefficients.inclusion F).obj (G.obj i)))
    (thetaΩ : (G ⋙ GeneralAlgebraicallyClosedCoefficients.inclusion F) ⋙
      zlDiagramQbarPullback D l hl Ω ≅ G ⋙ GeneralAlgebraicallyClosedCoefficients.inclusion F)
    (etaΩ : (G ⋙ GeneralAlgebraicallyClosedCoefficients.inclusion F) ⋙
      zlDiagramQbarFiber D l hl Ω ≅ V ⋙ ModuleCat.extendScalars
        (F.val.subtype.comp (Shrink.algEquiv (Padic l) F.val).toRingHom))
    (tΩ : ∀ i, (zlDiagramQbarFiber D l hl Ω).obj
      ((GeneralAlgebraicallyClosedCoefficients.inclusion F).obj (G.obj i)) ≅
      (zlDiagramQbarFiber D l hl Ω).obj ((zlDiagramQbarPullback D l hl Ω).obj
        ((GeneralAlgebraicallyClosedCoefficients.inclusion F).obj (G.obj i)))),
    ZlDiagramExactRealization
      ((sfCommonStageHeartProperty l (Spec (.of D.k)) Ω).lift
        (G ⋙ GeneralAlgebraicallyClosedCoefficients.inclusion F) hΩ)
      (V ⋙ ModuleCat.extendScalars
        (F.val.subtype.comp (Shrink.algEquiv (Padic l) F.val).toRingHom)) ∧
    ∀ i,
      thetaΩ.app i = zlDiagramStagePullback D l hl Ω F (G.obj i) ≪≫
        (GeneralAlgebraicallyClosedCoefficients.inclusion F).mapIso (theta.app i) ∧
      etaΩ.app i = zlDiagramStageFiber D l hl Ω F (G.obj i) ≪≫
        (ModuleCat.extendScalars
          (F.val.subtype.comp (Shrink.algEquiv (Padic l) F.val).toRingHom)).mapIso
          (eta.app i) ∧
      (tΩ i).hom = zlDiagramQbarTransport D l hl Ω
        ((GeneralAlgebraicallyClosedCoefficients.inclusion F).obj (G.obj i)) ∧
      (tΩ i).hom ≫ (zlDiagramQbarFiber D l hl Ω).map
          (zlDiagramStagePullback D l hl Ω F (G.obj i)).hom ≫
          (zlDiagramStageFiber D l hl Ω F
            ((zlDiagramPullback D l hl
              (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω F)).obj (G.obj i))).hom =
        (zlDiagramStageFiber D l hl Ω F (G.obj i)).hom ≫
          (ModuleCat.extendScalars
            (F.val.subtype.comp (Shrink.algEquiv (Padic l) F.val).toRingHom)).map
            (t i).hom ∧
      (etaΩ.app i).inv ≫ (tΩ i).hom ≫
          (zlDiagramQbarFiber D l hl Ω).map (thetaΩ.app i).hom ≫ (etaΩ.app i).hom =
        (ModuleCat.extendScalars
          (F.val.subtype.comp (Shrink.algEquiv (Padic l) F.val).toRingHom)).map (A i).hom ∧
      (zlDiagramQbarFiber D l hl Ω).map (thetaΩ.app i).inv =
        (etaΩ.app i).hom ≫
          (ModuleCat.extendScalars
            (F.val.subtype.comp (Shrink.algEquiv (Padic l) F.val).toRingHom)).map (A i).inv ≫
          (etaΩ.app i).inv ≫ (tΩ i).hom
```

## New

The exact same block is declared in `Sheaf.Paper.PointEquivariantDiagramData`.
The original module publicly imports that module. It keeps the original theorem,
whose full signature is unchanged, and privately imports the three proof-step modules.
All original public imports are reexported transitively by the data module.
The data module keeps the proof import of `Mathlib.Algebra.Category.ModuleCat.Descent`,
which its existing scalar comparison construction requires.

## Users

`python3 tools/downstream.py Sheaf.Paper.PointEquivariantDiagramLift --uses zlDiagramFiber`
reports zero downstream modules in the current library. Repository-wide textual search
for all diagram names also finds only the item module. The original public API remains
available at its original import path; target meanings are unchanged. No consumer
adaptation is necessary.

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.PointEquivariantDiagramLift | R6 | Publicly reexports the identical data; theorem type unchanged. |
| Sheaf.Paper.PointEquivariantOriginalDiagram | R6, new | States the original-field lift using the extracted data. |
| Sheaf.Paper.PointEquivariantFiniteScalar | R6, new | States finite coefficient extension for a supplied realized diagram. |
| Sheaf.Paper.PointEquivariantCommonStage | R6, new | States original-stage inclusion for a supplied realized diagram. |

## Status

landed 20261025T123650-L-1887771 2026-10-25 (merge of deliver/R6/Sheaf.Paper.PointEquivariantDiagramLift)
