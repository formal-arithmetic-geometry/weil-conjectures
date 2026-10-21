# WeilConjectures.integralLineSingle and integral-line comparison constructors

## Reason

Move the ten existing definitions to a dependency module, so that the two strictly
smaller proof obligations can mention them without an import cycle. Their names,
signatures, bodies and public visibility are unchanged. The original module publicly
imports the definitions module, which re-exports all seven original public imports.
Only the blueprint docstring labels move to their new definitions node. No definition
or target changes meaning. The new modules contain the isomorphism and finite-model
sub-results. The original theorem proves naturality, normalized completion, and the
projection equations from those results and the existing completion-unit API.

## Old

In `lean/Sheaf/Paper/IntegralLineTensorComparison.lean`:

```lean
/-- The line is placed in degree zero, using the existing single-complex functor.
Source: Bhatt--Scholze, Definition 3.4.10
(blueprint: lem-sf-integral-line-tensor-comparison). -/
def integralLineSingle : Mod l E X none ⥤ Cx l E X none :=
  HomologicalComplex.single _ (ComplexShape.up ℤ) 0

/-- Ordinary derived tensor with a sheaf in degree zero. The tensor model is the
recorded total tensor on K-flat representatives. Source: Stacks 06YN, 06YY
(blueprint: lem-sf-integral-line-tensor-comparison). -/
def integralLineOrdinary : (D l E X none) × (Mod l E X none) ⥤ D l E X none :=
  ((𝟭 (D l E X none)).prod (integralLineSingle l E X ⋙ DerivedCategory.Q)) ⋙
    (duality l E X none).closed.tensor

/-- The recorded completed tensor with the same degree-zero line.
Source: Bhatt--Scholze, Definition 3.4.10
(blueprint: lem-sf-integral-line-tensor-comparison). -/
def integralLineCompleted : (D l E X none) × (Mod l E X none) ⥤ D l E X none :=
  ((𝟭 (D l E X none)).prod (integralLineSingle l E X ⋙ DerivedCategory.Q)) ⋙
    completedTensor l E X none

/-- The canonical comparison, with its existing (c,0) cone normalization.
Source: Bhatt--Scholze, Definition 3.5.2
(blueprint: lem-sf-integral-line-tensor-comparison). -/
def integralLineComparison : integralLineOrdinary l E X ⟶ integralLineCompleted l E X :=
  Functor.whiskerLeft (integralLineOrdinary l E X) (completionUnit l E X none)

/-- The ordinary total complex P tensor T[0], with the signed direct-sum differential.
Source: Stacks 06YN (blueprint: lem-sf-integral-line-tensor-comparison). -/
def integralLineComplex (P : Cx l E X none) (T : Mod l E X none) : Cx l E X none :=
  (coefficientTotalTensor.{u, t + 1, t} (topology X none) (ring l E X none)).obj
    (P, (integralLineSingle l E X).obj T)

/-- Canonical K-flat representative comparison, transported along QP isomorphic to C.
Source: Stacks 06YY (blueprint: lem-sf-integral-line-tensor-comparison). -/
def integralLineRepresentativeIso (P : (Good l E X none).FullSubcategory)
    (T : Mod l E X none)
    (hT : CochainComplex.IsKFlatIndependentCoefficients
      (J := topology X none) (R := ring l E X none) ((integralLineSingle l E X).obj T))
    (C : D l E X none) (e : DerivedCategory.Q.obj P.obj ≅ C) :
    DerivedCategory.Q.obj (integralLineComplex l E X P.obj T) ≅
      (integralLineOrdinary l E X).obj (C, T) :=
  ((duality l E X none).models.iso (topology X none) (ring l E X none)
      (duality l E X none).closed P.obj ((integralLineSingle l E X).obj T) P.property.1 hT) ≪≫
    (duality l E X none).closed.tensor.mapIso (Iso.prod e (Iso.refl _))

/-- The finite scalar-extension complex, before restoring the completed-ring action.
Source: Stacks 06YY (blueprint: lem-sf-integral-line-tensor-comparison). -/
def integralLineFiniteComplex (n : ℕ) :=
  (reduction l E X none n).mapHomologicalComplex (ComplexShape.up ℤ)

/-- Total tensor of the two ordinary finite reductions, over the finite ring.
Source: Stacks 06YY (blueprint: lem-sf-integral-line-tensor-comparison). -/
def integralLineFiniteTensor (P : Cx l E X none) (T : Mod l E X none) (n : ℕ) :=
  (coefficientTotalTensor.{u, t + 1, t} (topology X none) (finite l E X none n)).obj
    ((integralLineFiniteComplex l E X n).obj P,
      (integralLineFiniteComplex l E X n).obj ((integralLineSingle l E X).obj T))

/-- Restriction along the actual finite quotient projection, applied to complexes.
Source: Stacks 06YY (blueprint: lem-sf-integral-line-tensor-comparison). -/
def integralLineFiniteRestrict (n : ℕ) :=
  (SheafOfModules.restrictScalars
    ((sheafCompose _ (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).map
      (projection l E X none n))).mapHomologicalComplex (ComplexShape.up ℤ)

/-- The actual projection from the strict Roos complex to its nth quotient.
Source: Stacks 08TC (blueprint: lem-sf-integral-line-tensor-comparison). -/
def integralLineRoosProjection (S : Cx l E X none) (n : ℕ) :
    integralOperationsRoos ((tower l E X none).obj S) ⟶
      ((level l E X none n).obj S) :=
  CochainComplex.mappingCocone.fst
      (towerTransitionEndomorphism
        (K := fun m : ℕ ↦ ((tower l E X none).obj S).obj (op m))
        (integralOperationsTowerStep ((tower l E X none).obj S))) ≫
    Pi.π (fun m : ℕ ↦ ((tower l E X none).obj S).obj (op m)) n

```

## New

The identical ten definition bodies above are in
`lean/Sheaf/Paper/IntegralLineTensorComparisonDefinitions.lean`.
The original module has `public import Sheaf.Paper.IntegralLineTensorComparisonDefinitions`
and retains the original theorem signature verbatim. The new theorem modules privately
imported for its proof are `IntegralLineTensorComparisonIso` and
`IntegralLineTensorComparisonRepresentative`.

## Users

`tools/downstream.py Sheaf.Paper.IntegralLineTensorComparison --uses integralLineSingle`
reports only the original module as a user. A repository-wide search for all ten
constructor names likewise finds only that module. There are no external current
Lean consumers to adapt. Public re-export preserves the interface for unfinished DAG
parents and their future consumers.

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.IntegralLineTensorComparison | H2 | Same names, types and bodies through public re-export; theorem proof completed from two strictly smaller results. |
| Sheaf.Paper.IntegralLineTensorComparisonDefinitions | H2 (new) | Contains the unchanged constructors. |
| Sheaf.Paper.IntegralLineTensorComparisonIso | H2 (new) | States the invertibility sub-result. |
| Sheaf.Paper.IntegralLineTensorComparisonRepresentative | H2 (new) | States only K-flat models and finite balancing; assumes no completeness. |

## Status

landed 20261021T001119-L-1372542 2026-10-21 (merge of deliver/H2/Sheaf.Paper.IntegralLineTensorComparison)
