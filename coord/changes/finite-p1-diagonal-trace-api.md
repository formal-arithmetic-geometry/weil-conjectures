# ArbitraryBaseFiniteP1Splitting and the finite-P1 trace and diagonal APIs

## Reason

Repeated checking of the original expanded categorical objects and diagonal clause
exceeded the file limit. Share the actual ordered biproduct and direct-image objects
through `ordinaryFiniteP1SplittingSource` and `ordinaryFiniteP1SplittingTarget`, and
name the unchanged diagonal clause `finiteP1DiagonalProperty` in this same module.
These are ordinary transparent definitions of the original expressions. The diagonal composite before the trace is likewise shared as
`ordinaryFiniteP1DiagonalSupportedMap`: its body is exactly alpha followed by the
projected supported map. `ordinaryFiniteP1DiagonalTarget` is exactly its original
shifted-twist direct-image target. No object
is chosen from an existence theorem, and no data or predicate has an admitted body.
The theorem's hypotheses and conclusions are definitionally identical after unfolding;
this is a representation refactor, not a correction of its mathematical statement.
The assigned helper is not one of the fixed declarations of `Challenge.lean`.
No adopted-source module or fixed Challenge declaration is edited.

Replace repeated global-sections simplifications by the proved public theorem
`finiteP1_unitOnPullback`. Proof irrelevance identifies these invertibility witnesses.
Its module and the object definitions' module are publicly imported because public
interfaces name them. Keep the original public imports.

The base-change predicate shares its two functors and composite comparison with
local lets; delta reduction gives the original two equations. Explicit scheme,
object and category arguments give the previously inferred parameters. The trace's
projection likewise spells out its two summands. No global reducibility attribute
of an existing definition is changed. The diagonal trace now composes the existing explicit chart map with the
splitting trace. Delta reduction of that chart map gives the original four factors.
The structure's hom law similarly names the existing two-component map; its delta
reduction is the original biproduct desc. This avoids repeatedly checking the same
categorical constructions in record fields and proof transports. The private constructor and its proved hom equation provide a small API
for the actual splitting record.

## Old

```lean
structure ArbitraryBaseFiniteP1Splitting (A : Type (u + 1)) [CommRing A] (N : ℕ)
    (hA : (N : A) = 0) (t : OrdinaryFiniteTwistTransport A N hA)
    (S : Scheme.{u}) (hS : IsUnit (N : Γ(S, ⊤))) where
  chern : ordinaryFiniteUnit A (ProjectiveLine S) ⟶
    (ordinaryFiniteLine A N hA (ProjectiveLine S))⟦(2 : ℤ)⟧
  chern_spec : ordinaryFiniteP1ChernSpec A N hA S
    (by simpa using hS.map (ProjectiveLine S ↘ S).appTop.hom) chern
  decomposition :
    ((ordinaryFiniteLine A N hA S)⟦(2 : ℤ)⟧ ⊞ ordinaryFiniteUnit A S) ≅
      (ordinaryFinitePushforward A (ProjectiveLine S ↘ S)).obj
        ((ordinaryFiniteLine A N hA (ProjectiveLine S))⟦(2 : ℤ)⟧)
  decomposition_hom : decomposition.hom = biprod.desc
    (ordinaryFiniteP1Unit A N hA t S hS) (ordinaryFiniteP1ChernPushforward A N hA S chern)

/-- The trace is the second projection of the inverse of the normalized splitting.
Source: blueprint tower P1 adjunction, finite trace normalization
(blueprint: lem-sp-tower-p1-arbitrary-base-integrals). -/
def ArbitraryBaseFiniteP1Splitting.trace {A : Type (u + 1)} [CommRing A] {N : ℕ}
    {hA : (N : A) = 0} {t : OrdinaryFiniteTwistTransport A N hA}
    {S : Scheme.{u}} {hS : IsUnit (N : Γ(S, ⊤))}
    (d : ArbitraryBaseFiniteP1Splitting A N hA t S hS) :
    (ordinaryFinitePushforward A (ProjectiveLine S ↘ S)).obj
      ((ordinaryFiniteLine A N hA (ProjectiveLine S))⟦(2 : ℤ)⟧) ⟶
        ordinaryFiniteUnit A S :=
  d.decomposition.inv ≫ biprod.snd

/-- The two arbitrary-base exchange squares, for the splitting and its trace.
All comparisons are the canonical arrows of the recorded dependency nodes.
Source: blueprint tower P1 adjunction, finite levelwise check and base-change normalization
(blueprint: lem-sp-tower-p1-arbitrary-base-integrals). -/
def ArbitraryBaseFiniteP1BaseChange (A : Type (u + 1)) [CommRing A] (N : ℕ)
    (hA : (N : A) = 0) (t : OrdinaryFiniteTwistTransport A N hA)
    (d : ∀ (S : Scheme.{u}) (hS : IsUnit (N : Γ(S, ⊤))),
      ArbitraryBaseFiniteP1Splitting A N hA t S hS) : Prop :=
  ∀ {S' S : Scheme.{u}} (f : S' ⟶ S) (hS : IsUnit (N : Γ(S, ⊤)))
    (hS' : IsUnit (N : Γ(S', ⊤))),
    ((ordinaryFinitePullback A f).map (d S hS).decomposition.hom ≫
      ordinaryFiniteP1Exchange A f ((ordinaryFiniteLine A N hA (ProjectiveLine S))⟦(2 : ℤ)⟧) ≫
      (ordinaryFinitePushforward A (ProjectiveLine S' ↘ S')).map
        (ordinaryFiniteShiftedLinePullback A N hA t
          (ProjectiveSpace.map (ULift.{u} (Fin 2)) f)
          (by simpa using hS.map (ProjectiveLine S ↘ S).appTop.hom)).hom =
    ordinaryFiniteP1DecompositionSourceMap A N hA t f hS ≫
      (d S' hS').decomposition.hom) ∧
    ((ordinaryFinitePullback A f).map (d S hS).trace ≫
        (ordinaryFiniteUnitPullback A f).hom =
      ordinaryFiniteP1Exchange A f ((ordinaryFiniteLine A N hA (ProjectiveLine S))⟦(2 : ℤ)⟧) ≫
        (ordinaryFinitePushforward A (ProjectiveLine S' ↘ S')).map
          (ordinaryFiniteShiftedLinePullback A N hA t
            (ProjectiveSpace.map (ULift.{u} (Fin 2)) f)
            (by simpa using hS.map (ProjectiveLine S ↘ S).appTop.hom)).hom ≫
          (d S' hS').trace)

/-- Transport the specified trace on P1 over P along the canonical chart for either
projection of P times P. This uses the chart adjunction unit and derived composition,
followed by the normalized twist comparison and the given splitting's own trace.
Source: blueprint tower P1 adjunction, identification of the two projections with r_P
(blueprint: lem-sp-tower-p1-arbitrary-base-integrals). -/
def arbitraryBaseFiniteP1DiagonalTrace (A : Type (u + 1)) [CommRing A] (N : ℕ)
    (hA : (N : A) = 0) (t : OrdinaryFiniteTwistTransport A N hA)
    (d : ∀ (T : Scheme.{u}) (hT : IsUnit (N : Γ(T, ⊤))),
      ArbitraryBaseFiniteP1Splitting A N hA t T hT)
    (S : Scheme.{u}) (hS : IsUnit (N : Γ(S, ⊤))) (a : Bool) :
    (ordinaryFinitePushforward A (projectiveLineDiagonalProjection S a)).obj
      ((ordinaryFiniteLine A N hA
        (pullback (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S)))⟦(2 : ℤ)⟧) ⟶
      ordinaryFiniteUnit A (ProjectiveLine S) :=
  let e := (projectiveLineDiagonalChart S a).val
  let p := projectiveLineDiagonalProjection S a
  let r := ProjectiveLine (ProjectiveLine S) ↘ ProjectiveLine S
  let L := (ordinaryFiniteLine A N hA
    (pullback (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S)))⟦(2 : ℤ)⟧
  (ordinaryFinitePushforward A p).map
      ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) e.hom).unit.app L) ≫
    (rightDerivedLowerStarComp (ModuleCat.{u + 1} A) e.hom p).hom.app
      ((ordinaryFinitePullback A e.hom).obj L) ≫
    (rightDerivedLowerStarCongr (ModuleCat.{u + 1} A)
      (projectiveLineDiagonalChart S a).property).hom.app
        ((ordinaryFinitePullback A e.hom).obj L) ≫
    (ordinaryFinitePushforward A r).map
      (ordinaryFiniteShiftedLinePullback A N hA t e.hom (by
        simpa using hS.map
          ((pullback.fst (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S)) ≫
            (ProjectiveLine S ↘ S)).appTop.hom)).hom ≫
    (d (ProjectiveLine S)
      (by simpa using hS.map (ProjectiveLine S ↘ S).appTop.hom)).trace

/-- The finite Kummer splitting and both diagonal integrals over every N-invertible base.
The supported boundary fixes the sign through its canonical relative Kummer construction.
The maps alpha are the existing canonical composition identifications, explicitly isomorphisms.

Source: blueprint main-20261015, sec-smooth-purity/sk-prop-sp-tower-geometric/
sk-prop-sp-tower-geometric-p1.proof.md, levelwise finite diagonal check
(blueprint: lem-sp-tower-p1-arbitrary-base-integrals).

Proof plan:
1. Set U = Spec Z[1/N]. Every N-invertible scheme has its canonical map to U, by
localizing on affine opens and gluing. An ideal of Z[1/N] is generated by the generator
of its contraction to Z, so U is Noetherian. Apply lem-asd-ordinary-finite-p1-adjunction
to U, obtaining precisely the splitting with twisted-unit and Kummer components.
2. The projective-space standard charts and affine fibre-product calculation give
diagonal equations x-y and 1-xy. Coefficient comparison makes both nonzerodivisors
over any ring. They cut out the diagonal, hence its ideal is effective Cartier.
The hyperplane's ideal dual has the O(1) transitions. All equations survive base change.
3. Properness of projective space and lem-kun-proper-base-change-torsion-ring give
proper exchange for arbitrary base maps. The mate formula respects the twisted unit.
Express the hyperplane Chern class as its supported Kummer map after the divisor unit;
lem-asd-ordinary-supported-kummer and the Cartier calculation identify its pullback.
Taking adjuncts therefore gives the Kummer component on the new base. The two
component equations are exactly the decomposition square, before assuming invertibility.
4. Pull back the splitting from U. Exchange and twist comparisons are isomorphisms,
so it is an isomorphism over every base. Invert the square and project to its second
summand to obtain the displayed trace square, for every morphism of bases.
5. Apply lem-amb-p1-diagonal-integrals on U. Its trace is pr2 of this same inverse
splitting by def-amb-p1-trace; its supported class has the same Kummer sign.
6. Pull the diagonal square to any base. Supported Kummer pullback and naturality
of proper exchange identify the pushed supported classes. Derived direct-image
composition identifies alpha with the unit for p_i Delta = id. Clauses 2 and 4 of
lem-weil-pbc-mate-pasting identify its composite exchange with the identity exchange,
so the alpha comparisons also commute, without an extra base-change assumption.
7. Combine the class, alpha and trace squares to pull back each of the two identities
from U. Inverse image preserves identity maps. This proves both Boolean-indexed
integrals with no Noetherian or finite-type assumption on S. -/
theorem exists_arbitraryBaseFiniteP1Integrals (N : ℕ) (hN : 0 < N)
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0) :
    ∃ (t : OrdinaryFiniteTwistTransport A N hA)
      (d : ∀ (S : Scheme.{u}) (hS : IsUnit (N : Γ(S, ⊤))),
        ArbitraryBaseFiniteP1Splitting A N hA t S hS),
      ArbitraryBaseFiniteP1BaseChange A N hA t d ∧
      ∀ (S : Scheme.{u}) (hS : IsUnit (N : Γ(S, ⊤))),
        ∃ hI : (pullback.diagonal (ProjectiveLine S ↘ S)).ker.IsInvertible,
          ∃ κ : Ext
            ((lowerStar (ModuleCat.{u + 1} A) (pullback.diagonal (ProjectiveLine S ↘ S))).obj
              (ordinaryFiniteConstant A (ProjectiveLine S)))
            (Scheme.finiteEtaleTateLine
              (pullback (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S)) N A hA) 2,
            SupportedKummerBoundary A N hA (pullback.diagonal (ProjectiveLine S ↘ S)) hI
              (by
                simpa using hS.map
                  ((pullback.fst (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S)) ≫
                    (ProjectiveLine S ↘ S)).appTop.hom) κ ∧
            ∀ a : Bool,
              IsIso (projectiveLineDiagonalAlpha A S a) ∧
              projectiveLineDiagonalAlpha A S a ≫
                (ordinaryFinitePushforward A (projectiveLineDiagonalProjection S a)).map
                  (supportedExactDerivedMap
                    (lowerStar (ModuleCat.{u + 1} A)
                      (pullback.diagonal (ProjectiveLine S ↘ S)))
                    (ordinaryFiniteConstant A (ProjectiveLine S))
                    (Scheme.finiteEtaleTateLine
                      (pullback (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S)) N A hA) κ) ≫
                arbitraryBaseFiniteP1DiagonalTrace A N hA t d S hS a =
              𝟙 (ordinaryFiniteUnit A (ProjectiveLine S))
```

## New

The following two object definitions are in `FiniteP1KummerNaturality`:

```lean
/-- The ordered source of the finite P1 decomposition, constructed as a biproduct.
Source: blueprint thm-amb-p1-decomposition, after twisting by A(1)[2].
(blueprint: lem-sp-finite-p1-kummer-naturality). -/
@[implicit_reducible]
def ordinaryFiniteP1SplittingSource (A : Type (u + 1)) [CommRing A] (N : ℕ)
    (hA : (N : A) = 0) (S : Scheme.{u}) : DerivedCategoryModule A S :=
  (ordinaryFiniteLine A N hA S)⟦(2 : ℤ)⟧ ⊞ ordinaryFiniteUnit A S

/-- The target of the finite P1 decomposition, constructed by derived direct image.
Source: blueprint thm-amb-p1-decomposition, after twisting by A(1)[2].
(blueprint: lem-sp-finite-p1-kummer-naturality). -/
@[implicit_reducible]
def ordinaryFiniteP1SplittingTarget (A : Type (u + 1)) [CommRing A] (N : ℕ)
    (hA : (N : A) = 0) (S : Scheme.{u}) : DerivedCategoryModule A S :=
  (ordinaryFinitePushforward A (X := ProjectiveLine S) (Y := S)
    (ProjectiveLine S ↘ S)).obj
      ((ordinaryFiniteLine A N hA (ProjectiveLine S))⟦(2 : ℤ)⟧)
```

The following direct-image object and canonical supported and chart maps are in
`FiniteP1DiagonalKummerComponentFormula`:

```lean
/-- The shifted-twist direct image for one of the product projections.
Source: blueprint finite diagonal check, canonical projection direct image.
(blueprint: lem-sp-finite-p1-diagonal-kummer-component-formula). -/
@[implicit_reducible]
def ordinaryFiniteP1DiagonalTarget (A : Type (u + 1)) [CommRing A] (N : ℕ)
    (hA : (N : A) = 0) (S : Scheme.{u}) (a : Bool) :
    DerivedCategoryModule A (ProjectiveLine S) :=
  (ordinaryFinitePushforward A
    (X := pullback (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S)) (Y := ProjectiveLine S)
    (projectiveLineDiagonalProjection S a)).obj
      ((ordinaryFiniteLine A N hA
        (pullback (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S)))⟦(2 : ℤ)⟧)

/-- Apply the projected supported class to the canonical constant-object unit.
This is the canonical composite before the trace in the finite diagonal integral.
Source: blueprint finite diagonal check, supported class and composition unit.
(blueprint: lem-sp-finite-p1-diagonal-kummer-component-formula). -/
@[irreducible]
def ordinaryFiniteP1DiagonalSupportedMap (A : Type (u + 1)) [CommRing A] (N : ℕ)
    (hA : (N : A) = 0) (S : Scheme.{u}) (a : Bool)
    (κ : Ext
      (C := Sheaf
        (pullback (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S)).smallEtaleTopology
        (ModuleCat.{u + 1} A))
      ((lowerStar (ModuleCat.{u + 1} A) (Z := ProjectiveLine S)
        (Y := pullback (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S))
        (pullback.diagonal (ProjectiveLine S ↘ S))).obj
          (ordinaryFiniteConstant A (ProjectiveLine S)))
      (Scheme.finiteEtaleTateLine
        (pullback (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S)) N A hA) 2) :
    ordinaryFiniteUnit A (ProjectiveLine S) ⟶ ordinaryFiniteP1DiagonalTarget A N hA S a :=
  projectiveLineDiagonalAlpha A S a ≫
    (ordinaryFinitePushforward A
      (X := pullback (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S)) (Y := ProjectiveLine S)
      (projectiveLineDiagonalProjection S a)).map
        (X := (ordinaryFinitePushforward A (X := ProjectiveLine S)
          (Y := pullback (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S))
          (pullback.diagonal (ProjectiveLine S ↘ S))).obj
            (ordinaryFiniteUnit A (ProjectiveLine S)))
        (Y := (ordinaryFiniteLine A N hA
          (pullback (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S)))⟦(2 : ℤ)⟧)
        (supportedExactDerivedMap
          (lowerStar (ModuleCat.{u + 1} A) (Z := ProjectiveLine S)
            (Y := pullback (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S))
            (pullback.diagonal (ProjectiveLine S ↘ S)))
          (ordinaryFiniteConstant A (ProjectiveLine S))
          (Scheme.finiteEtaleTateLine
            (pullback (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S)) N A hA) κ)

/-- Direct-image transport from either product projection to the standard P1 projection.
This is the comparison preceding the trace in arbitraryBaseFiniteP1DiagonalTrace.
Source: blueprint lem-amb-p1-diagonal-integrals, identification of each projection.
(blueprint: lem-sp-finite-p1-diagonal-kummer-component-formula). -/
@[irreducible]
def ordinaryFiniteP1DiagonalChartMap (A : Type (u + 1)) [CommRing A] (N : ℕ)
    (hA : (N : A) = 0) (t : OrdinaryFiniteTwistTransport A N hA)
    (S : Scheme.{u}) (hS : IsUnit (N : Γ(S, ⊤))) (a : Bool) :
    ordinaryFiniteP1DiagonalTarget A N hA S a ⟶
      (ordinaryFinitePushforward A
        (ProjectiveLine (ProjectiveLine S) ↘ ProjectiveLine S)).obj
          ((ordinaryFiniteLine A N hA (ProjectiveLine (ProjectiveLine S)))⟦(2 : ℤ)⟧) :=
  let e := (projectiveLineDiagonalChart S a).val
  let p := projectiveLineDiagonalProjection S a
  let L := (ordinaryFiniteLine A N hA
    (pullback (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S)))⟦(2 : ℤ)⟧
  (ordinaryFinitePushforward A p).map
      ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) e.hom).unit.app L) ≫
    (rightDerivedLowerStarComp (ModuleCat.{u + 1} A) e.hom p).hom.app
      ((ordinaryFinitePullback A e.hom).obj L) ≫
    (rightDerivedLowerStarCongr (ModuleCat.{u + 1} A)
      (projectiveLineDiagonalChart S a).property).hom.app
        ((ordinaryFinitePullback A e.hom).obj L) ≫
    (ordinaryFinitePushforward A
      (ProjectiveLine (ProjectiveLine S) ↘ ProjectiveLine S)).map
      (ordinaryFiniteShiftedLinePullback A N hA t e.hom
        ((map_natCast
          ((pullback.fst (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S)) ≫
            (ProjectiveLine S ↘ S)).appTop.hom N) ▸
          hS.map ((pullback.fst (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S)) ≫
            (ProjectiveLine S ↘ S)).appTop.hom)).hom
```

The assigned module's public definitions and helper theorem signature are:

```lean
structure ArbitraryBaseFiniteP1Splitting (A : Type (u + 1)) [CommRing A] (N : ℕ)
    (hA : (N : A) = 0) (t : OrdinaryFiniteTwistTransport A N hA)
    (S : Scheme.{u}) (hS : IsUnit (N : Γ(S, ⊤))) where
  chern : ordinaryFiniteUnit A (ProjectiveLine S) ⟶
    (ordinaryFiniteLine A N hA (ProjectiveLine S))⟦(2 : ℤ)⟧
  chern_spec : ordinaryFiniteP1ChernSpec A N hA S
    (finiteP1_unitOnPullback N (X := ProjectiveLine S) (Y := S)
        (ProjectiveLine S ↘ S) hS) chern
  decomposition : ordinaryFiniteP1SplittingSource A N hA S ≅
    ordinaryFiniteP1SplittingTarget A N hA S
  decomposition_hom : decomposition.hom = ordinaryFiniteP1SplittingMap A N hA t S hS chern

/-- The trace is the second projection of the inverse of the normalized splitting.
Source: blueprint tower P1 adjunction, finite trace normalization
(blueprint: lem-sp-tower-p1-arbitrary-base-integrals). -/
def ArbitraryBaseFiniteP1Splitting.trace {A : Type (u + 1)} [CommRing A] {N : ℕ}
    {hA : (N : A) = 0} {t : OrdinaryFiniteTwistTransport A N hA}
    {S : Scheme.{u}} {hS : IsUnit (N : Γ(S, ⊤))}
    (d : ArbitraryBaseFiniteP1Splitting A N hA t S hS) :
    ordinaryFiniteP1SplittingTarget A N hA S ⟶ ordinaryFiniteUnit A S :=
  d.decomposition.inv ≫
    biprod.snd (X := (ordinaryFiniteLine A N hA S)⟦(2 : ℤ)⟧)
      (Y := ordinaryFiniteUnit A S)

/-- The two arbitrary-base exchange squares, for the splitting and its trace.
All comparisons are the canonical arrows of the recorded dependency nodes.
Source: blueprint tower P1 adjunction, finite levelwise check and base-change normalization
(blueprint: lem-sp-tower-p1-arbitrary-base-integrals). -/
def ArbitraryBaseFiniteP1BaseChange (A : Type (u + 1)) [CommRing A] (N : ℕ)
    (hA : (N : A) = 0) (t : OrdinaryFiniteTwistTransport A N hA)
    (d : ∀ (S : Scheme.{u}) (hS : IsUnit (N : Γ(S, ⊤))),
      ArbitraryBaseFiniteP1Splitting A N hA t S hS) : Prop :=
  ∀ {S' S : Scheme.{u}} (f : S' ⟶ S) (hS : IsUnit (N : Γ(S, ⊤)))
    (hS' : IsUnit (N : Γ(S', ⊤))),
    let F := ordinaryFinitePullback A (X := S') (Y := S) f
    let G := ordinaryFinitePushforward A (X := ProjectiveLine S') (Y := S')
        (ProjectiveLine S' ↘ S')
    let e := ordinaryFiniteP1Exchange A f
        ((ordinaryFiniteLine A N hA (ProjectiveLine S))⟦(2 : ℤ)⟧) ≫
      G.map (ordinaryFiniteShiftedLinePullback A N hA t
        (X := ProjectiveLine S') (Y := ProjectiveLine S)
        (ProjectiveSpace.map (ULift.{u} (Fin 2)) f)
        (finiteP1_unitOnPullback N (X := ProjectiveLine S) (Y := S)
        (ProjectiveLine S ↘ S) hS)).hom
    let s := ordinaryFiniteP1DecompositionSourceMap A N hA t f hS
    (F.map (d S hS).decomposition.hom ≫ e = s ≫ (d S' hS').decomposition.hom) ∧
      (F.map (d S hS).trace ≫ (ordinaryFiniteUnitPullback A (X := S') (Y := S) f).hom =
        e ≫ (d S' hS').trace)

/-- Transport the specified trace on P1 over P along the canonical chart for either
projection of P times P. This uses the chart adjunction unit and derived composition,
followed by the normalized twist comparison and the given splitting's own trace.
Source: blueprint tower P1 adjunction, identification of the two projections with r_P
(blueprint: lem-sp-tower-p1-arbitrary-base-integrals). -/
def arbitraryBaseFiniteP1DiagonalTrace (A : Type (u + 1)) [CommRing A] (N : ℕ)
    (hA : (N : A) = 0) (t : OrdinaryFiniteTwistTransport A N hA)
    (d : ∀ (T : Scheme.{u}) (hT : IsUnit (N : Γ(T, ⊤))),
      ArbitraryBaseFiniteP1Splitting A N hA t T hT)
    (S : Scheme.{u}) (hS : IsUnit (N : Γ(S, ⊤))) (a : Bool) :
    ordinaryFiniteP1DiagonalTarget A N hA S a ⟶
      ordinaryFiniteUnit A (ProjectiveLine S) :=
  ordinaryFiniteP1DiagonalChartMap A N hA t S hS a ≫
    (d (ProjectiveLine S)
      (finiteP1_unitOnPullback N (X := ProjectiveLine S) (Y := S)
        (ProjectiveLine S ↘ S) hS)).trace

/-- The supported diagonal classes and the two normalized integrals. This is the
diagonal clause of the arbitrary-base finite projective-line theorem.
Source: blueprint tower P1 adjunction, finite diagonal check
(blueprint: lem-sp-tower-p1-arbitrary-base-integrals). -/
def finiteP1DiagonalProperty (A : Type (u + 1)) [CommRing A] (N : ℕ)
    (hA : (N : A) = 0) (t : OrdinaryFiniteTwistTransport A N hA)
    (d : ∀ (S : Scheme.{u}) (hS : IsUnit (N : Γ(S, ⊤))),
      ArbitraryBaseFiniteP1Splitting A N hA t S hS)
    (S : Scheme.{u}) (hS : IsUnit (N : Γ(S, ⊤))) : Prop :=
  ∃ hI : (pullback.diagonal (ProjectiveLine S ↘ S)).ker.IsInvertible,
    ∃ κ : Ext
      (C := Sheaf
        (pullback (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S)).smallEtaleTopology
        (ModuleCat.{u + 1} A))
      ((lowerStar (ModuleCat.{u + 1} A)
        (Z := ProjectiveLine S)
        (Y := pullback (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S))
        (pullback.diagonal (ProjectiveLine S ↘ S))).obj
        (ordinaryFiniteConstant A (ProjectiveLine S)))
      (Scheme.finiteEtaleTateLine
        (pullback (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S)) N A hA) 2,
      SupportedKummerBoundary A N hA
        (D := ProjectiveLine S) (T := pullback (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S))
        (pullback.diagonal (ProjectiveLine S ↘ S)) hI
        (finiteP1_unitOnPullback N
  (X := pullback (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S)) (Y := S)
  ((pullback.fst (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S)) ≫
            (ProjectiveLine S ↘ S)) hS) κ ∧
      ∀ a : Bool,
        IsIso (C := DerivedCategoryModule A (ProjectiveLine S))
          (projectiveLineDiagonalAlpha A S a) ∧
        ordinaryFiniteP1DiagonalSupportedMap A N hA S a κ ≫
          arbitraryBaseFiniteP1DiagonalTrace A N hA t d S hS a =
        𝟙 (ordinaryFiniteUnit A (ProjectiveLine S))

theorem exists_arbitraryBaseFiniteP1Integrals (N : ℕ) (hN : 0 < N)
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0) :
    ∃ (t : OrdinaryFiniteTwistTransport A N hA)
      (d : ∀ (S : Scheme.{u}) (hS : IsUnit (N : Γ(S, ⊤))),
        ArbitraryBaseFiniteP1Splitting A N hA t S hS),
      ArbitraryBaseFiniteP1BaseChange A N hA t d ∧
      ∀ (S : Scheme.{u}) (hS : IsUnit (N : Γ(S, ⊤))),
        finiteP1DiagonalProperty A N hA t d S hS
```

## Users

`tools/downstream.py` reports zero downstream modules. Its `--uses` queries for
`ArbitraryBaseFiniteP1Splitting`, `ArbitraryBaseFiniteP1BaseChange`,
`arbitraryBaseFiniteP1DiagonalTrace`, and `exists_arbitraryBaseFiniteP1Integrals`
find only their defining module. There are no forced consumer adaptations.
The two citing nodes, `det-sp-tower-p1-adjunction` and
`lem-per-ordinary-smooth-orientation`, retain exactly the same mathematical input:
all-base splitting and trace naturality, and both supported diagonal integrals.
No parent dependency or unit route is removed. Future target statements using these
refactored definitions require the usual definition review; their mathematical
interpretation is unchanged by the displayed delta reductions.

| module | group holding it | effect |
| --- | --- | --- |
| `Sheaf.AlgebraicGeometry.FiniteP1ArbitraryBaseIntegrals` | G5 | Names the same objects and diagonal predicate; uses a proved unit witness and shares the same exchange expression. |

## Status

landed 20261020T230743-L-608710 2026-10-20 (merge of deliver/G5/Sheaf.AlgebraicGeometry.FiniteP1ArbitraryBaseIntegrals)
