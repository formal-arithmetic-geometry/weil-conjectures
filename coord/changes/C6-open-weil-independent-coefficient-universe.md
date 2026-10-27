# WeilConjectures.ZlOpenUnit common-stage coefficient universe

## Reason

The assigned item has independent scheme and coefficient universes. The existing
open-unit theorem's final section unnecessarily specialized the coefficient closure to
`Type u`. Generalize it to `Type v`, keeping finite coefficient models in `Type u`.
The former point-fibre cohomology clause uses a point-realization API whose closure
universe is restricted. Express that clause at the literal finite coefficient stage
instead. This still asserts vanishing in every degree. For the original same-universe
inputs it is equivalent: the point-fibre construction extends the finite point complex
along the canonical small-model field equivalence and then to the closure; cohomology
commutes with both extensions, and extension of fields is faithful. In particular the
preceding unchanged common-stage zero-object clause implies both versions of this
cohomological vanishing. No target definition or target statement is changed.

The three common-stage pullback normalizations previously used a same-universe helper.
`pullbackStageIso` is its exact `eqToIso` construction for an independent closure
universe, specialized to the inclusion of a literal finite stage. These maps are
unchanged in the old specialization. Local opacity annotations prevent unwanted
unfolding of the large realized functors during elaboration; they are not exported.
The scalar predicate uses the typed `rationalFrobeniusStageScalar` helper for its
two Frobenius arguments, retaining precisely the previous maps. The ScalarLaws calls
name their implicit functor parameters explicitly to avoid expensive unfolding during
inference; this has no effect on their elaborated propositions.

## Old

The model section additionally had `[IsSeparated X₀.hom]` and
`[IsSeparated U₀.hom]`; these hypotheses are removed. The final section binder was:

```lean
variable (Ω : Type u) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
```

The affected predicate definitions, verbatim:

```lean
def EmptyFibre (S : Action D l hl X₀ U₀ j₀ Ω)
    (R : ∀ (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E],
      RationalData D l hl X₀ U₀ j₀ E)
    (Q : CommonData D l hl X₀ U₀ j₀ Ω S) : Prop :=
  letI : ∀ x : (D.geometricFiber X₀).left,
      Invertible (l : (D.geometricFiber X₀).left.residueField x) :=
    sfWeilPrimeInvertible D l hl X₀
  letI : ∀ x : Spec (.of D.k), Invertible (l : (Spec (.of D.k)).residueField x) :=
    frobeniusPointPrimeInvertible D l hl
  ∀ (x : Spec (.of D.k) ⟶ (D.geometricFiber X₀).left),
    Disjoint (Set.range x) (Set.range (zlFiberMap D j₀)) →
      (∀ (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
        (K : sfIntegralConstructibleCategory l E (D.geometricFiber U₀).left),
        IsZero ((@constructibleIntegralPullback l _ E _ _ _ _ _ x
          (frobeniusPointPrimeInvertible D l hl) (sfWeilPrimeInvertible D l hl X₀)).obj
          ((integralJ D l hl X₀ U₀ j₀ E).obj K)).obj) ∧
      (∀ (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
        (K : sfRationalConstructibleCategory l E (D.geometricFiber U₀).left),
        IsZero ((@rationalDerivedPullback l _ E _ _ _ _ _ x
          (frobeniusPointPrimeInvertible D l hl) (sfWeilPrimeInvertible D l hl X₀)).obj
          ((rationalJ D l hl X₀ U₀ j₀ E).obj K))) ∧
      (∀ K : generalAlgebraicallyClosedConstructibleCategory l Ω (D.geometricFiber U₀).left,
        IsZero ((@commonStageDerivedPullback l _ Ω _ _ _ _ _ x
          (frobeniusPointPrimeInvertible D l hl) (sfWeilPrimeInvertible D l hl X₀)).obj
            (S.system.functor.obj K))) ∧
      (∀ (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
        (K : sfWeilComplex D l hl U₀ E) (a : ℤ),
        IsZero ((DerivedCategory.coefficientFdCohomology E a).obj
          (localPointComplex l E D hl X₀
            ((IsoAlgebra.mapOfNatIso (R E).beta).obj K) x))) ∧
      (∀ (K : sfCommonStageWeilComplex D l hl U₀ Ω) (a : ℤ),
        IsZero ((DerivedCategory.coefficientQbarCohomology l Ω a).obj
          (localQbarPointComplex l Ω D hl X₀
            ((IsoAlgebra.mapOfNatIso Q.beta).obj K) x)))

def FiniteScalarCompatibility (S : Action D l hl X₀ U₀ j₀ Ω)
    (I : ∀ (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E],
      IntegralData D l hl X₀ U₀ j₀ E)
    (R : ∀ (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E],
      RationalData D l hl X₀ U₀ j₀ E) : Prop :=
  letI : ∀ x : (D.geometricFiber U₀).left,
      Invertible (l : (D.geometricFiber U₀).left.residueField x) :=
    sfWeilPrimeInvertible D l hl U₀
  letI : ∀ x : (D.geometricFiber X₀).left,
      Invertible (l : (D.geometricFiber X₀).left.residueField x) :=
    sfWeilPrimeInvertible D l hl X₀
  ∀ (E L : AlgebraicallyClosedCoefficients.Index l Ω) (h : E ≤ L),
    ∃ (a : integralP D l hl X₀ U₀ j₀ (AlgebraicallyClosedCoefficients.Coefficient l Ω E) ⋙
          GeneralAlgebraicallyClosedCoefficients.integralTransition l Ω
            (D.geometricFiber U₀).left E L h ≅
        GeneralAlgebraicallyClosedCoefficients.integralTransition l Ω
            (D.geometricFiber X₀).left E L h ⋙
          integralP D l hl X₀ U₀ j₀ (AlgebraicallyClosedCoefficients.Coefficient l Ω L))
      (gU : integralG D l hl U₀ (AlgebraicallyClosedCoefficients.Coefficient l Ω E) ⋙
          GeneralAlgebraicallyClosedCoefficients.integralTransition l Ω
            (D.geometricFiber U₀).left E L h ≅
        GeneralAlgebraicallyClosedCoefficients.integralTransition l Ω
            (D.geometricFiber U₀).left E L h ⋙
          integralG D l hl U₀ (AlgebraicallyClosedCoefficients.Coefficient l Ω L))
      (gX : integralG D l hl X₀ (AlgebraicallyClosedCoefficients.Coefficient l Ω E) ⋙
          GeneralAlgebraicallyClosedCoefficients.integralTransition l Ω
            (D.geometricFiber X₀).left E L h ≅
        GeneralAlgebraicallyClosedCoefficients.integralTransition l Ω
            (D.geometricFiber X₀).left E L h ⋙
          integralG D l hl X₀ (AlgebraicallyClosedCoefficients.Coefficient l Ω L)),
      (∀ K, a.app K = @integralPullbackScalarComparison l _
        (AlgebraicallyClosedCoefficients.Coefficient l Ω E) _ _ _
        (AlgebraicallyClosedCoefficients.Coefficient l Ω L) _ _ _
        (AlgebraicallyClosedCoefficients.coefficientInclusion l Ω E L h) _ _ (zlFiberMap D j₀)
        (sfWeilPrimeInvertible D l hl U₀) (sfWeilPrimeInvertible D l hl X₀) K) ∧
      (∀ K, gU.app K = @integralPullbackScalarComparison l _
        (AlgebraicallyClosedCoefficients.Coefficient l Ω E) _ _ _
        (AlgebraicallyClosedCoefficients.Coefficient l Ω L) _ _ _
        (AlgebraicallyClosedCoefficients.coefficientInclusion l Ω E L h) _ _
        (D.geometricFrobenius U₀).hom
        (sfWeilPrimeInvertible D l hl U₀) (sfWeilPrimeInvertible D l hl U₀) K) ∧
      (∀ K, gX.app K = @integralPullbackScalarComparison l _
        (AlgebraicallyClosedCoefficients.Coefficient l Ω E) _ _ _
        (AlgebraicallyClosedCoefficients.Coefficient l Ω L) _ _ _
        (AlgebraicallyClosedCoefficients.coefficientInclusion l Ω E L h) _ _
        (D.geometricFrobenius X₀).hom
        (sfWeilPrimeInvertible D l hl X₀) (sfWeilPrimeInvertible D l hl X₀) K) ∧
      ScalarLaws (I (AlgebraicallyClosedCoefficients.Coefficient l Ω E))
        (I (AlgebraicallyClosedCoefficients.Coefficient l Ω L))
        (GeneralAlgebraicallyClosedCoefficients.integralTransition l Ω
          (D.geometricFiber U₀).left E L h)
        (GeneralAlgebraicallyClosedCoefficients.integralTransition l Ω
          (D.geometricFiber X₀).left E L h) (S.integralBeta h) a gU gX ∧
      ScalarLaws (R (AlgebraicallyClosedCoefficients.Coefficient l Ω E))
        (R (AlgebraicallyClosedCoefficients.Coefficient l Ω L))
        ((GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω (D.geometricFiber U₀).left).T h)
        ((GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω (D.geometricFiber X₀).left).T h)
        ((eqToIso (congrArg
          (fun F ↦ F ⋙ (GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω
            (D.geometricFiber X₀).left).T h) (S.finite_eq E))).symm ≪≫ S.system.β h ≪≫
          eqToIso (congrArg
            (fun F ↦ (GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω
              (D.geometricFiber U₀).left).T h ⋙ F) (S.finite_eq L)))
        (@rationalStageScalar l _ Ω _ _ _ _ _ (zlFiberMap D j₀)
          (sfWeilPrimeInvertible D l hl U₀) (sfWeilPrimeInvertible D l hl X₀) E L h)
        (@rationalStageScalar l _ Ω _ _ _ _ _ (D.geometricFrobenius U₀).hom
          (sfWeilPrimeInvertible D l hl U₀) (sfWeilPrimeInvertible D l hl U₀) E L h)
        (@rationalStageScalar l _ Ω _ _ _ _ _ (D.geometricFrobenius X₀).hom
          (sfWeilPrimeInvertible D l hl X₀) (sfWeilPrimeInvertible D l hl X₀) E L h)

def CommonStageCompatibility (S : Action D l hl X₀ U₀ j₀ Ω)
    (R : ∀ (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E],
      RationalData D l hl X₀ U₀ j₀ E)
    (Q : CommonData D l hl X₀ U₀ j₀ Ω S) : Prop :=
  letI : ∀ x : (D.geometricFiber U₀).left,
      Invertible (l : (D.geometricFiber U₀).left.residueField x) :=
    sfWeilPrimeInvertible D l hl U₀
  letI : ∀ x : (D.geometricFiber X₀).left,
      Invertible (l : (D.geometricFiber X₀).left.residueField x) :=
    sfWeilPrimeInvertible D l hl X₀
  ∀ E : AlgebraicallyClosedCoefficients.Index l Ω,
    ∃ (a : rationalP D l hl X₀ U₀ j₀ (AlgebraicallyClosedCoefficients.Coefficient l Ω E) ⋙
          GeneralAlgebraicallyClosedCoefficients.inclusion E ≅
        GeneralAlgebraicallyClosedCoefficients.inclusion E ⋙ zlPull D l hl Ω j₀)
      (gU : sfWeilFrobeniusPullback D l hl U₀
            (AlgebraicallyClosedCoefficients.Coefficient l Ω E) ⋙
          GeneralAlgebraicallyClosedCoefficients.inclusion E ≅
        GeneralAlgebraicallyClosedCoefficients.inclusion E ⋙
          sfCommonStageWeilFrobeniusPullback D l hl U₀ Ω)
      (gX : sfWeilFrobeniusPullback D l hl X₀
            (AlgebraicallyClosedCoefficients.Coefficient l Ω E) ⋙
          GeneralAlgebraicallyClosedCoefficients.inclusion E ≅
        GeneralAlgebraicallyClosedCoefficients.inclusion E ⋙
          sfCommonStageWeilFrobeniusPullback D l hl X₀ Ω),
      (∀ K, HEq (a.hom.app K)
        (@localQbarPullbackStageIso l _ Ω _ _ _ _ _ (zlFiberMap D j₀)
          (sfWeilPrimeInvertible D l hl U₀) (sfWeilPrimeInvertible D l hl X₀)
          ((GeneralAlgebraicallyClosedCoefficients.inclusion E).obj K)).inv) ∧
      (∀ K, HEq (gU.hom.app K)
        (@localQbarPullbackStageIso l _ Ω _ _ _ _ _ (D.geometricFrobenius U₀).hom
          (sfWeilPrimeInvertible D l hl U₀) (sfWeilPrimeInvertible D l hl U₀)
          ((GeneralAlgebraicallyClosedCoefficients.inclusion E).obj K)).inv) ∧
      (∀ K, HEq (gX.hom.app K)
        (@localQbarPullbackStageIso l _ Ω _ _ _ _ _ (D.geometricFrobenius X₀).hom
          (sfWeilPrimeInvertible D l hl X₀) (sfWeilPrimeInvertible D l hl X₀)
          ((GeneralAlgebraicallyClosedCoefficients.inclusion E).obj K)).inv) ∧
      ScalarLaws (R (AlgebraicallyClosedCoefficients.Coefficient l Ω E)) Q
        (GeneralAlgebraicallyClosedCoefficients.inclusion E)
        (GeneralAlgebraicallyClosedCoefficients.inclusion E)
        ((eqToIso (congrArg
          (fun F ↦ F ⋙ GeneralAlgebraicallyClosedCoefficients.inclusion E)
          (S.finite_eq E))).symm ≪≫ (S.system.ιCompFunctorIso E).symm) a gU gX
```

## New

The final section uses `Ω : Type v`. The finite compatibility predicate has the same witnesses and equations.
Its repeated transport expressions are factored through the transparent definitions
`transportScalarSquare`, `transportOperationSquare`, `transportInclusionSquare`,
and `rationalFrobeniusStageScalar`. These helpers construct exactly the original
whiskered composites; local opacity prevents repeated expansion during inference. The repaired predicates and finite-inclusion comparison are:

```lean
def EmptyFibre (S : Action D l hl X₀ U₀ j₀ Ω)
    (R : ∀ (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E],
      RationalData D l hl X₀ U₀ j₀ E)
    (_Q : CommonData D l hl X₀ U₀ j₀ Ω S) : Prop :=
  letI : ∀ x : (D.geometricFiber X₀).left,
      Invertible (l : (D.geometricFiber X₀).left.residueField x) :=
    sfWeilPrimeInvertible D l hl X₀
  letI : ∀ x : Spec (.of D.k), Invertible (l : (Spec (.of D.k)).residueField x) :=
    frobeniusPointPrimeInvertible D l hl
  ∀ (x : Spec (.of D.k) ⟶ (D.geometricFiber X₀).left),
    Disjoint (Set.range x) (Set.range (zlFiberMap D j₀)) →
      (∀ (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
        (K : sfIntegralConstructibleCategory l E (D.geometricFiber U₀).left),
        IsZero ((@constructibleIntegralPullback l _ E _ _ _ _ _ x
          (frobeniusPointPrimeInvertible D l hl) (sfWeilPrimeInvertible D l hl X₀)).obj
          ((integralJ D l hl X₀ U₀ j₀ E).obj K)).obj) ∧
      (∀ (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
        (K : sfRationalConstructibleCategory l E (D.geometricFiber U₀).left),
        IsZero ((@rationalDerivedPullback l _ E _ _ _ _ _ x
          (frobeniusPointPrimeInvertible D l hl) (sfWeilPrimeInvertible D l hl X₀)).obj
          ((rationalJ D l hl X₀ U₀ j₀ E).obj K))) ∧
      (∀ K : generalAlgebraicallyClosedConstructibleCategory l Ω (D.geometricFiber U₀).left,
        IsZero ((@commonStageDerivedPullback l _ Ω _ _ _ _ _ x
          (frobeniusPointPrimeInvertible D l hl) (sfWeilPrimeInvertible D l hl X₀)).obj
            (S.system.functor.obj K))) ∧
      (∀ (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
        (K : sfWeilComplex D l hl U₀ E) (a : ℤ),
        IsZero ((DerivedCategory.coefficientFdCohomology E a).obj
          (localPointComplex l E D hl X₀
            ((IsoAlgebra.mapOfNatIso (R E).beta).obj K) x))) ∧
      (∀ (K : sfCommonStageWeilComplex D l hl U₀ Ω) (a : ℤ),
        let N := (@commonStageDerivedPullback l _ Ω _ _ _ _ _ x
          (frobeniusPointPrimeInvertible D l hl)
          (sfWeilPrimeInvertible D l hl X₀)).obj (S.system.functor.obj K.carrier)
        IsZero ((DerivedCategory.coefficientFdCohomology
          (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω N.stage) a).obj
          ((pointRationalFibre D l hl
            (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω N.stage)).obj N.obj)))

/-- The object equation of the recorded common-stage pullback.
Source: coefficient descent (blueprint: lem-zl-open-weil-unit-and-empty-fibre). -/
def pullbackStageIso {X Y : Scheme.{u}} (f : X ⟶ Y)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (E : AlgebraicallyClosedCoefficients.Index l Ω)
    (K : sfRationalConstructibleCategory l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E) Y) :
    (commonStageDerivedPullback l Ω f).obj
        ((GeneralAlgebraicallyClosedCoefficients.inclusion E).obj K) ≅
      (GeneralAlgebraicallyClosedCoefficients.inclusion E).obj
        ((rationalDerivedPullback l
          (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E) f).obj K) :=
  eqToIso ((commonStageDerivedPullback_existsUnique l Ω f).exists.choose_spec.1
    ((GeneralAlgebraicallyClosedCoefficients.inclusion E).obj K))


/-- Inclusion of every literal finite stage preserves the actual unit and beta.
The pullback edges are the canonical object identifications of the recorded
common-stage construction; the support edge is the given coefficient action.
Source: Part 2, common-stage passage
(blueprint: lem-zl-open-weil-unit-and-empty-fibre). -/
def CommonStageCompatibility (S : Action D l hl X₀ U₀ j₀ Ω)
    (R : ∀ (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E],
      RationalData D l hl X₀ U₀ j₀ E)
    (Q : CommonData D l hl X₀ U₀ j₀ Ω S) : Prop :=
  letI : ∀ x : (D.geometricFiber U₀).left,
      Invertible (l : (D.geometricFiber U₀).left.residueField x) :=
    sfWeilPrimeInvertible D l hl U₀
  letI : ∀ x : (D.geometricFiber X₀).left,
      Invertible (l : (D.geometricFiber X₀).left.residueField x) :=
    sfWeilPrimeInvertible D l hl X₀
  ∀ E : AlgebraicallyClosedCoefficients.Index l Ω,
    ∃ (a : rationalP D l hl X₀ U₀ j₀ (AlgebraicallyClosedCoefficients.Coefficient l Ω E) ⋙
          GeneralAlgebraicallyClosedCoefficients.inclusion E ≅
        GeneralAlgebraicallyClosedCoefficients.inclusion E ⋙ zlPull D l hl Ω j₀)
      (gU : sfWeilFrobeniusPullback D l hl U₀
            (AlgebraicallyClosedCoefficients.Coefficient l Ω E) ⋙
          GeneralAlgebraicallyClosedCoefficients.inclusion E ≅
        GeneralAlgebraicallyClosedCoefficients.inclusion E ⋙
          sfCommonStageWeilFrobeniusPullback D l hl U₀ Ω)
      (gX : sfWeilFrobeniusPullback D l hl X₀
            (AlgebraicallyClosedCoefficients.Coefficient l Ω E) ⋙
          GeneralAlgebraicallyClosedCoefficients.inclusion E ≅
        GeneralAlgebraicallyClosedCoefficients.inclusion E ⋙
          sfCommonStageWeilFrobeniusPullback D l hl X₀ Ω),
      (∀ K, HEq (a.hom.app K)
        (@pullbackStageIso l _ Ω _ _ _ _ _ (zlFiberMap D j₀)
          (sfWeilPrimeInvertible D l hl U₀) (sfWeilPrimeInvertible D l hl X₀)
          E K).inv) ∧
      (∀ K, HEq (gU.hom.app K)
        (@pullbackStageIso l _ Ω _ _ _ _ _ (D.geometricFrobenius U₀).hom
          (sfWeilPrimeInvertible D l hl U₀) (sfWeilPrimeInvertible D l hl U₀)
          E K).inv) ∧
      (∀ K, HEq (gX.hom.app K)
        (@pullbackStageIso l _ Ω _ _ _ _ _ (D.geometricFrobenius X₀).hom
          (sfWeilPrimeInvertible D l hl X₀) (sfWeilPrimeInvertible D l hl X₀)
          E K).inv) ∧
      ScalarLaws (R (AlgebraicallyClosedCoefficients.Coefficient l Ω E)) Q
        (GeneralAlgebraicallyClosedCoefficients.inclusion E)
        (GeneralAlgebraicallyClosedCoefficients.inclusion E)
        ((eqToIso (congrArg
          (fun F ↦ F ⋙ GeneralAlgebraicallyClosedCoefficients.inclusion E)
          (S.finite_eq E))).symm ≪≫ (S.system.ιCompFunctorIso E).symm) a gU gX

attribute [local irreducible] FiniteScalarCompatibility CommonStageCompatibility
  EmptyFibre IntegralUnitNormalization Rationalization

```

## Users

`tools/downstream.py Sheaf.Paper.ZlOpenWeilUnitEmptyFibre --uses rationalStageScalar
CommonData EmptyFibre FiniteScalarCompatibility CommonStageCompatibility
openWeilUnitAndEmptyFibre` reports zero downstream modules and only self-use hits.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.ZlOpenWeilUnitEmptyFibre | unclaimed | Independent closure universe, literal finite-stage point cohomology and pullback comparison. |
| Sheaf.Paper.CommonStageWeilShriek | C6 | Uses the existing open adjunction at the item's original independent universes. |

The three DAG citers are `lem-zl-immersion-weil-local-behavior`,
`lem-zl-extension-by-zero-punctual`, and `lem-zl-clopen-prescribed-weil-filtration`.
They use the open unit, normalized Frobenius exchange, and outside stalk vanishing.
Those assertions are retained. The common-stage stalk is still asserted to be the
zero object; its realized cohomology is therefore zero as required by these citers.
The item introduces no separatedness hypothesis. The auxiliary package's old
separated structure-morphism hypotheses are removed: finite type and quasi-compactness
supply all needed Noetherian properties, while the open map itself is separated.
Stacks 09BN and 09BP apply to arbitrary schemes. The stronger auxiliary conclusion
specializes to every old input, so its three DAG consumers remain valid.

## Status

landed 20261025T122622-L-1790683 2026-10-25 (merge of deliver/C6/Sheaf.Paper.CommonStageWeilShriek)
