# AlgebraicGeometry.ProEtale.FieldShriekSystem.ProjectionTensorComparisons

## Reason

The proper and open component lemmas must mention the existing tensor datum and
projection corner maps without importing the theorem that will use them. Move the
existing five data declarations verbatim to a shared module and publicly re-export
that module from the original module. Add the two explicit projection factors there.
No statement, definition body, name, visibility, universe or normalization changes.
This is a relocation to avoid an import cycle, not a split for a compile-time limit.

## Old

In lean/Sheaf/Paper/FieldProjectionSystemSquare.lean:

```lean
/-- The specified tensor comparisons used at all four corners. Symmetry is fixed by
its signed total-complex generators; the scalar tensorator uses the existing pure-tensor
and K-flat model, so neither map is an unspecified identification of object values.
Source: blueprint (2), canonical monoidal scalar and symmetry identifications
(blueprint: lem-sp-field-projection-system-square). -/
structure ProjectionTensorComparisons where
  symmetry : ∀ (E : Index P) (T : Scheme.{u}),
    SpTowerShriek.tensor P.coefficients.l E.val (D.base E) T ≅
      CategoryTheory.Prod.swap _ _ ⋙ SpTowerShriek.tensor P.coefficients.l E.val (D.base E) T
  symmetry_model : ∀ (E : Index P) (T : Scheme.{u})
    (A B : CochainComplex (SpTowerShriek.S P.coefficients.l E.val T) ℤ)
    (hA : CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1}
      (R := systemRing.{u + 1, u, u + 1} (Scheme.ProEt.topology T)
        (SpTowerShriek.B P.coefficients.l E.val T)
        (SpTowerShriek.tau P.coefficients.l E.val T)) A)
    (hB : CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1}
      (R := systemRing.{u + 1, u, u + 1} (Scheme.ProEt.topology T)
        (SpTowerShriek.B P.coefficients.l E.val T)
        (SpTowerShriek.tau P.coefficients.l E.val T)) B),
    ∃ s : (totalTensor.{u + 1, u, u + 1} (coefficientSequenceTopology (Scheme.ProEt.topology T))
        (systemRing.{u + 1, u, u + 1} (Scheme.ProEt.topology T)
        (SpTowerShriek.B P.coefficients.l E.val T)
          (SpTowerShriek.tau P.coefficients.l E.val T))).obj (A, B) ⟶
      (totalTensor.{u + 1, u, u + 1} (coefficientSequenceTopology (Scheme.ProEt.topology T))
        (systemRing.{u + 1, u, u + 1} (Scheme.ProEt.topology T)
        (SpTowerShriek.B P.coefficients.l E.val T)
          (SpTowerShriek.tau P.coefficients.l E.val T))).obj (B, A),
      (∀ (a b n : ℤ) (hab : a + b = n) (hba : b + a = n)
        (U : (ℕ × T.ProEt)ᵒᵖ) (x : (A.X a).val.obj U) (y : (B.X b).val.obj U),
        (s.f n).val.app U
            (coefficientTensorGenerator.{u + 1, u + 1, u}
              (coefficientSequenceTopology (Scheme.ProEt.topology T))
              (systemRing.{u + 1, u, u + 1} (Scheme.ProEt.topology T)
                (SpTowerShriek.B P.coefficients.l E.val T)
                (SpTowerShriek.tau P.coefficients.l E.val T)) A B a b n hab U x y) =
          (a * b).negOnePow •
            coefficientTensorGenerator.{u + 1, u + 1, u}
              (coefficientSequenceTopology (Scheme.ProEt.topology T))
              (systemRing.{u + 1, u, u + 1} (Scheme.ProEt.topology T)
                (SpTowerShriek.B P.coefficients.l E.val T)
                (SpTowerShriek.tau P.coefficients.l E.val T)) B A b a n hba U y x) ∧
      ((D.base E).calculus T).tensorModels.comparison.hom.app (⟨A, hA⟩, ⟨B, hB⟩) ≫
          (symmetry E T).hom.app (DerivedCategory.Q.obj A, DerivedCategory.Q.obj B) =
        DerivedCategory.Q.map s ≫
          ((D.base E).calculus T).tensorModels.comparison.hom.app (⟨B, hB⟩, ⟨A, hA⟩)
  scalar : ∀ (E F : Index P) (h : E ≤ F) (T : Scheme.{u}),
    SpTowerShriek.tensor P.coefficients.l E.val (D.base E) T ⋙ (D.scalars E F h T).T ≅
      ((D.scalars E F h T).T.prod (D.scalars E F h T).T) ⋙
        SpTowerShriek.tensor P.coefficients.l F.val (D.base F) T
  scalar_model : ∀ (E F : Index P) (h : E ≤ F) (T : Scheme.{u}),
    ScalarTensorComparisonModel.{u + 1, u, u + 1}
      (coefficientSequenceTopology (Scheme.ProEt.topology T))
      (systemRing.{u + 1, u, u + 1} (Scheme.ProEt.topology T)
        (SpTowerShriek.B P.coefficients.l E.val T)
        (SpTowerShriek.tau P.coefficients.l E.val T))
      (systemRing.{u + 1, u, u + 1} (Scheme.ProEt.topology T)
        (SpTowerShriek.B P.coefficients.l F.val T)
        (SpTowerShriek.tau P.coefficients.l F.val T))
      (coefficientMap P (D.coefficients E F h) T) (D.scalars E F h T)
      ((D.base E).calculus T).closed ((D.base F).calculus T).closed
      ((D.base E).calculus T).tensorModels ((D.base F).calculus T).tensorModels
      (scalar E F h T)

/-- The left-input compact-support projection, including both tensor symmetries.
Its middle arrow is exactly the published proper-counit/open projection.
Source: blueprint (2), pi_A and pi_B (blueprint: lem-sp-field-projection-system-square). -/
def leftProjection (t : ProjectionTensorComparisons P D) (E : Index P)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (K : SpTowerShriek.D P.coefficients.l E.val Y)
    (W : SpTowerShriek.D P.coefficients.l E.val X) :=
  (t.symmetry E Y).hom.app
      (K, (SpTowerShriek.F P.coefficients.l E.val (D.base E) (D.operations E) c).obj W) ≫
    SpTowerShriek.projection P.coefficients.l E.val (D.base E) (D.operations E) c W K ≫
    (SpTowerShriek.F P.coefficients.l E.val (D.base E) (D.operations E) c).map
      ((t.symmetry E X).hom.app
        (W, (SpTowerShriek.pull P.coefficients.l E.val (D.base E)
          ((D.operations E).geometry f)).obj K))

/-- The target comparison is scalar tensor followed by the inverse pullback compositor.
Source: blueprint (2), C_X f_A^* = f_B^* C_Y
(blueprint: lem-sp-field-projection-system-square). -/
def projectionTarget (t : ProjectionTensorComparisons P D) {E F : Index P} (h : E ≤ F)
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (K : SpTowerShriek.D P.coefficients.l E.val Y)
    (W : SpTowerShriek.D P.coefficients.l E.val X) :=
  (t.scalar E F h X).app
      ((SpTowerShriek.pull P.coefficients.l E.val (D.base E)
        ((D.operations E).geometry f)).obj K, W) ≪≫
    (SpTowerShriek.tensor P.coefficients.l F.val (D.base F) X).mapIso
      (Iso.prod ((D.pull E F h f).derived.symm.app K) (Iso.refl _))

/-- The two routes use the actual comparison b in the ordinary derived category.
Source: blueprint (2), displayed projection square
(blueprint: lem-sp-field-projection-system-square). -/
def ProjectionSystemSquare (t : ProjectionTensorComparisons P D) {E F : Index P}
    (h : E ≤ F) {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (K : SpTowerShriek.D P.coefficients.l E.val Y)
    (W : SpTowerShriek.D P.coefficients.l E.val X) : Prop :=
  (D.scalars E F h Y).T.map (leftProjection P D t E c K W) ≫
      (comparison P D h c).app
        ((SpTowerShriek.tensor P.coefficients.l E.val (D.base E) X).obj
          ((SpTowerShriek.pull P.coefficients.l E.val (D.base E)
            ((D.operations E).geometry f)).obj K, W)) ≫
      (SpTowerShriek.F P.coefficients.l F.val (D.base F) (D.operations F) c).map
        (projectionTarget P D t h f K W).hom =
    (t.scalar E F h Y).hom.app
        (K, (SpTowerShriek.F P.coefficients.l E.val (D.base E) (D.operations E) c).obj W) ≫
      (SpTowerShriek.tensor P.coefficients.l F.val (D.base F) Y).map
        (Prod.mkHom (𝟙 _) ((comparison P D h c).app W)) ≫
      leftProjection P D t F c ((D.scalars E F h Y).T.obj K)
        ((D.scalars E F h X).T.obj W)

/-- The same square after inverting the two projection maps on their finite-Tor
etale-origin domain. The invertibility witnesses come from tower_shriek_levels(2a).
Source: blueprint (2), inverted projection square
(blueprint: lem-sp-field-projection-system-square). -/
def InvertedProjectionSystemSquare (t : ProjectionTensorComparisons P D) {E F : Index P}
    (h : E ≤ F) {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (K : SpTowerShriek.D P.coefficients.l E.val Y)
    (W : SpTowerShriek.D P.coefficients.l E.val X)
    [IsIso (leftProjection P D t E c K W)]
    [IsIso (leftProjection P D t F c ((D.scalars E F h Y).T.obj K)
      ((D.scalars E F h X).T.obj W))] : Prop :=
  (comparison P D h c).app
        ((SpTowerShriek.tensor P.coefficients.l E.val (D.base E) X).obj
          ((SpTowerShriek.pull P.coefficients.l E.val (D.base E)
            ((D.operations E).geometry f)).obj K, W)) ≫
      (SpTowerShriek.F P.coefficients.l F.val (D.base F) (D.operations F) c).map
        (projectionTarget P D t h f K W).hom ≫
      inv (leftProjection P D t F c ((D.scalars E F h Y).T.obj K)
        ((D.scalars E F h X).T.obj W)) =
    (D.scalars E F h Y).T.map (inv (leftProjection P D t E c K W)) ≫
      (t.scalar E F h Y).hom.app
        (K, (SpTowerShriek.F P.coefficients.l E.val (D.base E) (D.operations E) c).obj W) ≫
      (SpTowerShriek.tensor P.coefficients.l F.val (D.base F) Y).map
        (Prod.mkHom (𝟙 _) ((comparison P D h c).app W))
```

## New

The same five declarations, verbatim, are in
lean/Sheaf/Paper/FieldProjectionSystemData.lean. The original module adds
`public import Sheaf.Paper.FieldProjectionSystemData`, retaining both of its
previous public imports. The new shared module also defines `leftProper` and
`leftOpen` as explicit composites. Their composition is proved equal to the
original `leftProjection` in the original module.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.FieldProjectionSystemSquare | S2 | Imports the relocated declarations; theorem signature unchanged. |

The downstream tool reported zero importing modules. A search for the five
qualified or unqualified declaration names found no consumer of these declarations
outside the assigned module. New component lemmas import the shared module.
The existing DAG attachment is retained for field_projection_system_square, and
the relocated data have the new definition-node attachment.

## Status

landed 20261025T203038-L-2779089 2026-10-25 (merge of deliver/S2/Sheaf.Paper.FieldProjectionSystemSquare)
