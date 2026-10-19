# AlgebraicGeometry.Etale.affineLinearTraceAction

## Reason

The new universal-action and family obligations need to mention the existing action
and coefficient constructions without importing the theorem that uses those obligations.
Move the nine definitions to `Sheaf.AlgebraicGeometry.AffineLinearTraceAction` and
publicly import that module from the original module. Names, signatures, visibility,
and definition bodies are preserved up to the explicit object argument described below. The new geometric API proves the Cartesian square certificate, the coordinate and
over-base equations, the identity formula, the tower base-change square and
compatibility of the linear map with base change. Its private coordinate lemmas
are proved as well.

## Old

The following signatures were declared in
`Sheaf.AlgebraicGeometry.AffineSpaceLinearTraceInvariance`:

```lean
def affineTraceLinearMap (S : Scheme.{u}) (d : ℕ) (g : Matrix.GeneralLinearGroup (Fin d) Γ(S, ⊤)) : affineTraceTower S d ⟶ affineTraceTower S d
```

```lean
def affineLinearPullbackId (A : Type (u + 1)) [CommRing A] (S : Scheme.{u}) : ordinaryFinitePullback A (𝟙 S) ≅ 𝟭 (DerivedCategoryModule A S)
```

```lean
def affineLinearBaseCoefficient (A : Type (u + 1)) [CommRing A] (N : ℕ) (hA : (N : A) = 0) (S : Scheme.{u}) : ℕ → DerivedCategoryModule A S
```

```lean
def affineLinearLineDescent (A : Type (u + 1)) [CommRing A] (N : ℕ) (hA : (N : A) = 0) (t : OrdinaryFiniteTwistTransport A N hA) (S : Scheme.{u}) (hS : IsUnit (N : Γ(S, ⊤))) (K : DerivedCategoryModule A S) : (affineTraceLineRight A N hA S).obj K ≅ (ordinaryFinitePullback A (AffineSpace PUnit.{u + 1} S ↘ S)).obj ((derivedTensorRight (ModuleCat.{u + 1} A) S ((ordinaryFiniteLine A N hA S)⟦(2 : ℤ)⟧)).obj K)
```

```lean
def affineLinearCoefficientDescentStep (A : Type (u + 1)) [CommRing A] (N : ℕ) (hA : (N : A) = 0) (t : OrdinaryFiniteTwistTransport A N hA) (S : Scheme.{u}) (hS : IsUnit (N : Γ(S, ⊤))) (d : ℕ) (e : (affineTraceRight A N hA S d).obj (ordinaryFiniteUnit A S) ≅ (ordinaryFinitePullback A (affineTraceProjection S d)).obj (affineLinearBaseCoefficient A N hA S d)) : (affineTraceLineRight A N hA (affineTraceTower S d)).obj ((affineTraceRight A N hA S d).obj (ordinaryFiniteUnit A S)) ≅ (ordinaryFinitePullback A ((AffineSpace PUnit.{u + 1} (affineTraceTower S d) ↘ affineTraceTower S d) ≫ affineTraceProjection S d)).obj ((derivedTensorRight (ModuleCat.{u + 1} A) S ((ordinaryFiniteLine A N hA S)⟦(2 : ℤ)⟧)).obj (affineLinearBaseCoefficient A N hA S d))
```

```lean
def affineLinearCoefficientDescent (A : Type (u + 1)) [CommRing A] (N : ℕ) (hA : (N : A) = 0) (t : OrdinaryFiniteTwistTransport A N hA) (S : Scheme.{u}) (hS : IsUnit (N : Γ(S, ⊤))) (d : ℕ) : (affineTraceRight A N hA S d).obj (ordinaryFiniteUnit A S) ≅ (ordinaryFinitePullback A (affineTraceProjection S d)).obj (affineLinearBaseCoefficient A N hA S d)
```

```lean
def affineLinearCoefficientPullback (A : Type (u + 1)) [CommRing A] (N : ℕ) (hA : (N : A) = 0) (t : OrdinaryFiniteTwistTransport A N hA) (S : Scheme.{u}) (hS : IsUnit (N : Γ(S, ⊤))) (d : ℕ) (a : affineTraceTower S d ⟶ affineTraceTower S d) (ha : a ≫ affineTraceProjection S d = affineTraceProjection S d) : (ordinaryFinitePullback A a).obj ((affineTraceRight A N hA S d).obj (ordinaryFiniteUnit A S)) ≅ (affineTraceRight A N hA S d).obj (ordinaryFiniteUnit A S)
```

```lean
def affineLinearCompactComparison (N : ℕ) (hN : 0 < N) (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0) (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤))) (d : ℕ) : (affineTraceLeft A S d).obj ((affineTraceRight A N hA S d).obj (ordinaryFiniteUnit A S)) ≅ (rightDerivedLowerShriek (ModuleCat.{u + 1} A) (affineTraceProjection S d)).obj ((affineTraceRight A N hA S d).obj (ordinaryFiniteUnit A S))
```

```lean
def affineLinearTraceAction (N : ℕ) (hN : 0 < N) (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0) (t : OrdinaryFiniteTwistTransport A N hA) (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤))) (d : ℕ) (a : affineTraceTower S d ⟶ affineTraceTower S d) (sq : IsPullback a (affineTraceProjection S d) (affineTraceProjection S d) (𝟙 S)) : (affineTraceLeft A S d).obj ((affineTraceRight A N hA S d).obj (ordinaryFiniteUnit A S)) ⟶ (affineTraceLeft A S d).obj ((affineTraceRight A N hA S d).obj (ordinaryFiniteUnit A S))
```

## New

The same definitions, with exactly the same signatures and definitionally equal bodies,
are declared in
`Sheaf.AlgebraicGeometry.AffineLinearTraceAction`. The old module exposes them by:

```lean
public import Sheaf.AlgebraicGeometry.AffineLinearTraceAction
```

In `affineLinearTraceAction`, the object argument of
`(affineLinearPullbackId A S).inv.app` is now written explicitly as
`(rightDerivedLowerShriek (ModuleCat A) (affineTraceProjection S d)).obj
  ((affineTraceRight A N hA S d).obj (ordinaryFiniteUnit A S))`.
This is the same inferred object, with the compact-support functor kept folded.
It prevents elaboration from expanding the chosen compactification inside identity
and action comparisons. No construction is changed.

The existing public imports are preserved through this public import. No coefficient,
exchange, counit or target changes meaning. Every target using these definitions
therefore has definitionally identical constructions; there is no semantic statement change.

## Users

`tools/downstream.py` found 761 transitive importers in the current source snapshot. A whole-library textual search
found the following users of the moved names; all keep the same public names and
definitionally identical bodies. No consumer adaptation is needed.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.AffineSpaceLinearTraceInvariance | G6 | Identical definitions via the existing import; no edit. |
| Sheaf.AlgebraicGeometry.VectorBundleIntegration | unclaimed | Identical definitions via the existing import; no edit. |
| Sheaf.Paper.FlagPullbackInjective | unclaimed | Identical definitions via the existing import; no edit. |
| Sheaf.Paper.AdicPurityRootComparisons | unclaimed | Identical definitions via the existing import; no edit. |
| Sheaf.Paper.FixedFinitePositiveCoefficientTwist | unclaimed | Identical definitions via the existing import; no edit. |
| Sheaf.Paper.PurityChernClasses | unclaimed | Identical definitions via the existing import; no edit. |
| Sheaf.Paper.FiniteReductionChartCalculus | unclaimed | Identical definitions via the existing import; no edit. |
| Sheaf.Paper.VectorPurityDirectSum | unclaimed | Identical definitions via the existing import; no edit. |
| Sheaf.Paper.FiniteSmoothPurityMaps | unclaimed | Identical definitions via the existing import; no edit. |
| Sheaf.Paper.VectorPurityFiniteReduction | unclaimed | Identical definitions via the existing import; no edit. |
| Sheaf.Paper.ProjectiveBundleFormula | unclaimed | Identical definitions via the existing import; no edit. |
| Sheaf.Paper.FiniteRingSectionDeformation | unclaimed | Identical definitions via the existing import; no edit. |
| Sheaf.Paper.PurityCompositionCoherence | unclaimed | Identical definitions via the existing import; no edit. |
| Sheaf.Paper.PurityDiagonalDualizingObject | unclaimed | Identical definitions via the existing import; no edit. |
| Sheaf.Paper.VectorPurityBaseChange | unclaimed | Identical definitions via the existing import; no edit. |
| Sheaf.Paper.AmbientDiagonalPurityBaseChange | unclaimed | Identical definitions via the existing import; no edit. |
| Sheaf.Paper.GeometricProjectiveSpaceHyperplaneCohomology | unclaimed | Identical definitions via the existing import; no edit. |
| Sheaf.Paper.LocalizedTopChern | unclaimed | Identical definitions via the existing import; no edit. |

The newly added universal-action module imports the new definition module directly.
They and the original theorem were compiled together in import order. The unchanged VectorBundleIntegration consumer was compiled successfully against the
sandbox overlay (5.3 seconds). Independent review must check the relocation and all five new proved modules.

## Status

landed 20261019T231203-L-558923 2026-10-19 (merge of deliver/G6/Sheaf.AlgebraicGeometry.AffineSpaceLinearTraceInvariance)
