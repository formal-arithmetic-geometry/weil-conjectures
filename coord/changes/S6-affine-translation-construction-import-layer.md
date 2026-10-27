# AlgebraicGeometry.Etale.ambientAffineTranslation

## Reason

The existing dependency theorem `purUniversalTranslationMultiplier` imports the item
for its concrete translation, exchange and Tate constructions. The item must now use
that dependency to implement its recorded proof. Separate the existing construction
node into `Sheaf.AlgebraicGeometry.AmbientAffineTranslationConstruction` and retain
`AmbientAffineTranslationTrace` as its public reexport plus the trace theorem.
Change the unclaimed `UniversalTranslationMultiplier` public import to the
construction module. This removes the import cycle without changing any definition,
public declaration signature, normalization or chosen object. The construction
module also contains the now-proved coordinate-square theorem. This is an import
architecture repair, not a split of mathematical work or a timeout workaround.

## Old

The following existing declarations are moved, with signatures and definition
bodies unchanged; only the coordinate-square proof is filled:

```lean
/-- Package the existing affine translation and its opposite as an isomorphism.
Source: Step 1 (blueprint: lem-trf-ambient-affine-translation-trace). -/
def ambientAffineTranslationIso (B : Scheme.{u}) (b : PUnit.{u + 1} → Γ(B, ⊤)) :
    AffineSpace PUnit.{u + 1} B ≅ AffineSpace PUnit.{u + 1} B where
  hom := AffineSpace.translation b
  inv := AffineSpace.translation (-b)
  hom_inv_id := (AffineSpace.translation_add b (-b)).symm.trans
    (congrArg AffineSpace.translation (add_neg_cancel b) |>.trans AffineSpace.translation_zero)
  inv_hom_id := (AffineSpace.translation_add (-b) b).symm.trans
    (congrArg AffineSpace.translation (neg_add_cancel b) |>.trans AffineSpace.translation_zero)

/-- The translation `z ↦ z-a` in the coordinate-tower model. Restrict the vector
at each step to its first coordinates, translate the last affine line, and apply
functoriality to the previous stages. This uses the upstream translation.
Source: Step 1 (blueprint: lem-trf-ambient-affine-translation-trace). -/
def ambientAffineTranslation (S : Scheme.{u}) :
    (d : ℕ) → (a : Fin d → Γ(S, ⊤)) → (affineTraceTower S d ≅ affineTraceTower S d)
  | 0, _ => Iso.refl S
  | d + 1, a =>
    ambientAffineTranslationIso (affineTraceTower S d)
      (fun _ ↦ -(affineTraceProjection S d).appTop (a (Fin.last d))) ≪≫
      (AffineSpace.functor.obj (Opposite.op PUnit.{u + 1})).mapIso
        (ambientAffineTranslation S d (fun i ↦ a i.castSucc))

/-- The cartesian square of a coordinate projection under translation. It is
cartesian because both horizontal morphisms are the explicit translation
isomorphisms. Its commutativity follows from `translation_over`, `map_over`,
and the recursive definition; these are equalities of the actual scheme maps.
Source: Step 1 (blueprint: lem-trf-ambient-affine-translation-trace).
Proof: the last-coordinate translation is over the preceding tower stage;
functoriality of affine space makes the other factor lie over the preceding
translation. Compose these equations and use the isomorphism-square criterion.
-/
theorem ambientAffineTranslation_lineSquare (S : Scheme.{u}) (d : ℕ)
    (a : Fin (d + 1) → Γ(S, ⊤)) :
    IsPullback (ambientAffineTranslation S (d + 1) a).hom
      (AffineSpace PUnit.{u + 1} (affineTraceTower S d) ↘ affineTraceTower S d)
      (AffineSpace PUnit.{u + 1} (affineTraceTower S d) ↘ affineTraceTower S d)
      (ambientAffineTranslation S d (fun i ↦ a i.castSucc)).hom := by
  sorry

/-- Expand the recorded affine-line right functor into its ordinary pulled-back
input and its shifted finite Tate line. This is tensor pullback followed by the
canonical inverse-image composition and the normalized finite-line comparison.
Source: Step 1 and sk-prop-an, Step 5(b)
(blueprint: lem-trf-ambient-affine-translation-trace). -/
def ambientAffineLineRightExpansion (A : Type (u + 1)) [CommRing A] (N : ℕ)
    (hA : (N : A) = 0) (t : OrdinaryFiniteTwistTransport A N hA)
    (B : Scheme.{u}) (hB : IsUnit (N : Γ(B, ⊤))) (K : DerivedCategoryModule A B) :
    (affineTraceLineRight A N hA B).obj K ≅
      (ordinaryFiniteTwistedPullback A (AffineSpace PUnit.{u + 1} B ↘ B)
        ((ordinaryFiniteLine A N hA (AffineSpace PUnit.{u + 1} B))⟦(2 : ℤ)⟧)).obj K :=
  ordinaryFiniteTensorPullback A (ProjectiveLine.affineChart B)
      ((ordinaryFinitePullback A (ProjectiveLine B ↘ B)).obj K)
      ((ordinaryFiniteLine A N hA (ProjectiveLine B))⟦(2 : ℤ)⟧) ≪≫
    ordinaryFiniteTensorRightMapIso A (AffineSpace PUnit.{u + 1} B)
      ((leftDerivedUpperStarComp (ModuleCat.{u + 1} A) (ProjectiveLine.affineChart B)
        (ProjectiveLine B ↘ B) (AffineSpace PUnit.{u + 1} B ↘ B)
        (ProjectiveLine.affineChart_over B).symm).symm.app K)
      (ordinaryFiniteShiftedLinePullback A N hA t (ProjectiveLine.affineChart B)
        (affineTraceProjectiveInvertible N B hB))

/-- The Tate identification for one coordinate square, constructed from tensor
pullback, the actual commutative square, and the normalized finite-line transport.
Source: Step 1 (blueprint: lem-trf-ambient-affine-translation-trace). -/
def ambientAffineLineRightSquare (A : Type (u + 1)) [CommRing A] (N : ℕ)
    (hA : (N : A) = 0) (t : OrdinaryFiniteTwistTransport A N hA)
    {B B' : Scheme.{u}} (f : B' ⟶ B)
    (g : AffineSpace PUnit.{u + 1} B' ⟶ AffineSpace PUnit.{u + 1} B)
    (w : g ≫ (AffineSpace PUnit.{u + 1} B ↘ B) =
      (AffineSpace PUnit.{u + 1} B' ↘ B') ≫ f)
    (hB : IsUnit (N : Γ(B, ⊤))) (hB' : IsUnit (N : Γ(B', ⊤)))
    (K : DerivedCategoryModule A B) :
    (ordinaryFinitePullback A g).obj ((affineTraceLineRight A N hA B).obj K) ≅
      (affineTraceLineRight A N hA B').obj ((ordinaryFinitePullback A f).obj K) :=
  (ordinaryFinitePullback A g).mapIso (ambientAffineLineRightExpansion A N hA t B hB K) ≪≫
    ordinaryFiniteTwistedPullbackComparison A
      (AffineSpace PUnit.{u + 1} B ↘ B) (AffineSpace PUnit.{u + 1} B' ↘ B') f g
      ((ordinaryFiniteLine A N hA (AffineSpace PUnit.{u + 1} B))⟦(2 : ℤ)⟧)
      ((ordinaryFiniteLine A N hA (AffineSpace PUnit.{u + 1} B'))⟦(2 : ℤ)⟧) K
      ((leftDerivedUpperStarComp (ModuleCat.{u + 1} A) g
        (AffineSpace PUnit.{u + 1} B ↘ B)).symm.app K ≪≫
        (leftDerivedUpperStarComp (ModuleCat.{u + 1} A)
          (AffineSpace PUnit.{u + 1} B' ↘ B') f _ w).app K)
      (ordinaryFiniteShiftedLinePullback A N hA t g (affineTraceInvertible N B hB 1)) ≪≫
    (ambientAffineLineRightExpansion A N hA t B' hB'
      ((ordinaryFinitePullback A f).obj K)).symm

/-- One explicit pasting step for the normalized Tate identification. The last
argument is the preceding coordinate identification, not independently chosen data.
Source: Step 1 (blueprint: lem-trf-ambient-affine-translation-trace). -/
def ambientAffineTranslationTateStep (A : Type (u + 1)) [CommRing A] (N : ℕ)
    (hA : (N : A) = 0) (t : OrdinaryFiniteTwistTransport A N hA)
    (S : Scheme.{u}) (hS : IsUnit (N : Γ(S, ⊤))) (d : ℕ)
    (a : Fin (d + 1) → Γ(S, ⊤))
    (e : (ordinaryFinitePullback A
      (ambientAffineTranslation S d (fun i ↦ a i.castSucc)).hom).obj
        ((affineTraceRight A N hA S d).obj (ordinaryFiniteUnit A S)) ≅
      (affineTraceRight A N hA S d).obj (ordinaryFiniteUnit A S)) :
    (ordinaryFinitePullback A (ambientAffineTranslation S (d + 1) a).hom).obj
        ((affineTraceLineRight A N hA (affineTraceTower S d)).obj
          ((affineTraceRight A N hA S d).obj (ordinaryFiniteUnit A S))) ≅
      (affineTraceLineRight A N hA (affineTraceTower S d)).obj
        ((affineTraceRight A N hA S d).obj (ordinaryFiniteUnit A S)) :=
  ambientAffineLineRightSquare A N hA t
      (ambientAffineTranslation S d (fun i ↦ a i.castSucc)).hom
      (ambientAffineTranslation S (d + 1) a).hom
      (ambientAffineTranslation_lineSquare S d a).w
      (affineTraceInvertible N S hS d) (affineTraceInvertible N S hS d)
      ((affineTraceRight A N hA S d).obj (ordinaryFiniteUnit A S)) ≪≫
    (affineTraceLineRight A N hA (affineTraceTower S d)).mapIso e

/-- The normalized Tate pullback identification on the coordinate-tower complex
`A(d)[2d]`, assembled one shifted Tate line at a time. The zero-dimensional
identification is the constant-sheaf identity comparison.
Source: Step 1 (blueprint: lem-trf-ambient-affine-translation-trace). -/
def ambientAffineTranslationTate (A : Type (u + 1)) [CommRing A] (N : ℕ)
    (hA : (N : A) = 0) (t : OrdinaryFiniteTwistTransport A N hA)
    (S : Scheme.{u}) (hS : IsUnit (N : Γ(S, ⊤))) :
    (d : ℕ) → (a : Fin d → Γ(S, ⊤)) →
    ((ordinaryFinitePullback A (ambientAffineTranslation S d a).hom).obj
        ((affineTraceRight A N hA S d).obj (ordinaryFiniteUnit A S)) ≅
      (affineTraceRight A N hA S d).obj (ordinaryFiniteUnit A S))
  := Nat.rec (motive := fun d ↦ (a : Fin d → Γ(S, ⊤)) →
      ((ordinaryFinitePullback A (ambientAffineTranslation S d a).hom).obj
          ((affineTraceRight A N hA S d).obj (ordinaryFiniteUnit A S)) ≅
        (affineTraceRight A N hA S d).obj (ordinaryFiniteUnit A S)))
    (fun _ ↦ ordinaryFiniteUnitPullback A (𝟙 S))
    (fun d r a ↦ ambientAffineTranslationTateStep A N hA t S hS d a
      (r (fun i ↦ a i.castSucc)))

/-- The canonical line exchange is the recorded proper/open exchange for the
translation square, followed by the recorded compactification comparison back
to the standard affine chart. No arbitrary endomorphism is supplied.
Source: Step 1 (blueprint: lem-trf-ambient-affine-translation-trace). -/
def ambientAffineTranslationLineExchange (A : Type (u + 1)) [CommRing A] [Finite A]
    (S : Scheme.{u}) (d : ℕ) (a : Fin (d + 1) → Γ(S, ⊤))
    (M : DerivedCategoryModule A (affineTraceTower S (d + 1))) :
    (ordinaryFinitePullback A
      (ambientAffineTranslation S d (fun i ↦ a i.castSucc)).hom).obj
        ((affineTraceLineLeft A (affineTraceTower S d)).obj M) ⟶
      (affineTraceLineLeft A (affineTraceTower S d)).obj
        ((ordinaryFinitePullback A (ambientAffineTranslation S (d + 1) a).hom).obj M) :=
  (rightDerivedLowerShriekOfCompactificationBaseChangeMap (ModuleCat.{u + 1} A)
      (ambientAffineTranslation_lineSquare S d a)
      (affineTraceLineCompactification (affineTraceTower S d))).app M ≫
    (rightDerivedLowerShriekOfCompactificationIso A
      ((affineTraceLineCompactification (affineTraceTower S d)).ofIsPullback
        (ambientAffineTranslation_lineSquare S d a))
      (affineTraceLineCompactification (affineTraceTower S d))).hom.app _

/-- The compact-support exchange for translation, pasted along the coordinate
compactifications. At rank zero insert only the canonical identity inverse-image
comparison. The unbounded comparison dependency identifies this pasting with
its compactification-independent exchange, on these bounded-below inputs.
Source: Step 1 (blueprint: lem-trf-ambient-affine-translation-trace). -/
def ambientAffineTranslationExchange (A : Type (u + 1)) [CommRing A] [Finite A]
    (S : Scheme.{u}) : (d : ℕ) → (a : Fin d → Γ(S, ⊤)) →
    (M : DerivedCategoryModule A (affineTraceTower S d)) →
    (affineTraceLeft A S d).obj M ⟶
      (affineTraceLeft A S d).obj
        ((ordinaryFinitePullback A (ambientAffineTranslation S d a).hom).obj M)
  | 0, _, M =>
    (unboundedEtaleUpperStarIdIso A S).inv.app M ≫
      (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) (𝟙 S)).inv.app M
  | d + 1, a, M =>
    ambientAffineTranslationExchange A S d (fun i ↦ a i.castSucc)
        ((affineTraceLineLeft A (affineTraceTower S d)).obj M) ≫
      (affineTraceLeft A S d).map (ambientAffineTranslationLineExchange A S d a M)

/-- The normalized twist transport supplied by the trace dependency. Its roots
inclusion and pure-tensor normalizations determine its maps uniquely; this is
not a choice of an unnormalized Tate trivialization.
Source: sk-prop-an and Step 1 (blueprint: lem-trf-ambient-affine-translation-trace). -/
def ambientAffineTraceTransport (N : ℕ) (hN : 0 < N)
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0) :
    OrdinaryFiniteTwistTransport A N hA :=
  Classical.choose (exists_affineSpaceTopTrace N hN A hA)

/-- The specified normalized projective-line data used in the coordinate counit.
The Kummer Chern map, decomposition components, and counit normalization determine
this data up to the equality of trace maps used here. No free trace is chosen.
Source: sk-prop-an and Step 1 (blueprint: lem-trf-ambient-affine-translation-trace). -/
def ambientAffineTraceDatum (N : ℕ) (hN : 0 < N)
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0) :
    ∀ (T : Scheme.{u}) [IsNoetherian T] (hT : IsUnit (N : Γ(T, ⊤))),
      OrdinaryFiniteP1Datum A N hA (ambientAffineTraceTransport N hN A hA) T hT :=
  Classical.choose (Classical.choose_spec (exists_affineSpaceTopTrace N hN A hA))

```

The old public import in UniversalTranslationMultiplier was:

```lean
public import Sheaf.AlgebraicGeometry.AmbientAffineTranslationTrace
```

## New

The quoted declarations now live in
`lean/Sheaf/AlgebraicGeometry/AmbientAffineTranslationConstruction.lean`.
Their names, signatures and non-theorem bodies are verbatim unchanged.
The coordinate-square proof uses `IsPullback.of_horiz_isIso`, `AffineSpace.map_over`
and `AffineSpace.translation_over`. The original module publicly imports the new
construction module, preserving access to every moved declaration and to every
previous public dependency, and contains the now-proved `ambientAffineTranslationTrace`.
UniversalTranslationMultiplier now uses:

```lean
public import Sheaf.AlgebraicGeometry.AmbientAffineTranslationConstruction
```

All its definitions, theorem statements and theorem proof bodies remain unchanged.
It has no consumers in the original snapshot; the item is its new proof-only consumer.
No target statement or definition meaning changes, so semantic target review does
not reopen. The existing definition node attachment is updated to the new module;
no duplicate definition or new node is introduced.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.AffineDiagonalIntegrationOrientation | W9 | Unchanged; original public module reexports identical constructions. |
| Sheaf.Paper.AffineTranslationTrace | Z8 | Unchanged; original public module reexports identical constructions. |
| Sheaf.Paper.AmbientDiagonalPurityBaseChange | unclaimed | Unchanged; original public module reexports identical constructions. |
| Sheaf.Paper.ChartDiagonalAssemblyData | unclaimed | Unchanged; original public module reexports identical constructions. |
| Sheaf.Paper.ChartDiagonalSourceMate | unclaimed | Unchanged; original public module reexports identical constructions. |
| Sheaf.Paper.ChartDncVectorFactors | S9 | Unchanged; original public module reexports identical constructions. |
| Sheaf.Paper.ChartExceptionalMateCoherence | W3 | Unchanged; original public module reexports identical constructions. |
| Sheaf.Paper.ChartTargetOpenDescent | unclaimed | Unchanged; original public module reexports identical constructions. |
| Sheaf.Paper.CompositionModelOrientationDescent | V3 | Unchanged; original public module reexports identical constructions. |
| Sheaf.Paper.DiagonalDncAssemblyGlobal | unclaimed | Unchanged; original public module reexports identical constructions. |
| Sheaf.Paper.DiagonalDncChartNormalization | T5 | Unchanged; original public module reexports identical constructions. |
| Sheaf.Paper.DiagonalOrientationCharts | unclaimed | Unchanged; original public module reexports identical constructions. |
| Sheaf.Paper.DiagonalOrientationChoiceIndependent | unclaimed | Unchanged; original public module reexports identical constructions. |
| Sheaf.Paper.EtaleOrientationLocality | unclaimed | Unchanged; original public module reexports identical constructions. |
| Sheaf.Paper.FiniteDiagonalOrientationReduction | U3 | Unchanged; original public module reexports identical constructions. |
| Sheaf.Paper.FiniteDiagonalReductionComparisons | unclaimed | Unchanged; original public module reexports identical constructions. |
| Sheaf.Paper.GeneralChartComparisons | G6 | Unchanged; original public module reexports identical constructions. |
| Sheaf.Paper.NormalModelSectionOrientation | unclaimed | Unchanged; original public module reexports identical constructions. |
| Sheaf.Paper.ProjectionPurityAgreement | N2 | Unchanged; original public module reexports identical constructions. |
| Sheaf.Paper.PurityCompositionCompatibleDncCharts | unclaimed | Unchanged; original public module reexports identical constructions. |
| Sheaf.Paper.RetaggingCoordinateOrientations | unclaimed | Unchanged; original public module reexports identical constructions. |
| Sheaf.Paper.SectionDncIntegrationSquare | unclaimed | Unchanged; original public module reexports identical constructions. |
| Sheaf.Paper.UniversalTranslationMultiplier | J9 | Import changed to construction module; all declarations unchanged. |
| Sheaf.Paper.VectorBundleFrameOrientationRestriction | unclaimed | Unchanged; original public module reexports identical constructions. |
| Sheaf.Paper.VectorIntegrationChartComparison | Z9 | Unchanged; original public module reexports identical constructions. |
| Sheaf.Paper.VectorModelChartDescent | T9 | Unchanged; original public module reexports identical constructions. |
| Sheaf.AlgebraicGeometry.AmbientAffineTranslationTrace | S6 | Definitions reexported; proof uses multiplier dependency. |
| Sheaf.AlgebraicGeometry.AmbientAffineTranslationConstruction | S6 (new module) | Existing definition node moved here, no data changes. |

## Status

landed 20261025T123757-L-1897710 2026-10-25 (merge of deliver/S6/Sheaf.AlgebraicGeometry.AmbientAffineTranslationTrace)
