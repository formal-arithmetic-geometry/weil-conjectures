# WeilConjectures.integralOperationRoosProjection

## Reason

The separate, unbounded Roos-effectivity lemma needs the actual projection and the two
finite-complex constructions. Move their existing definitions to its module so it can
state its theorem without importing the upper constructibility theorem. Re-export the
module publicly from the original module. This prevents an import cycle and keeps all
three declaration names, signatures, attributes and bodies unchanged.

## Old

In `Sheaf.Paper.IntegralOperationsPreserveConstructible`:

```lean
def integralOperationRoosProjection (W : AlgebraicGeometry.Scheme.{u})
    (T : ℕᵒᵖ ⥤ CochainComplex (integralTowerModules l E W) ℤ) (n : ℕ) :
    DerivedCategory.Q.obj (integralOperationsRoos T) ⟶ DerivedCategory.Q.obj (T.obj (op n)) :=
  DerivedCategory.Q.map
    (CochainComplex.mappingCocone.fst
      (towerTransitionEndomorphism (K := fun m ↦ T.obj (op m))
        (integralOperationsTowerStep T)) ≫ Pi.π (fun m ↦ T.obj (op m)) n)

/-- The finite pullback of the nth reduction of a good integral representative.
The coefficient pullback is the canonical pro-etale inverse image with its
constant-ring action; exactness makes this compute `f⁻¹(K tensor^L A_(n+1))`.
Source: Bhatt--Scholze, Lemma 6.5.9(5); Stacks Tag 099N(5)
(blueprint: lem-pur-integral-operations-preserve-constructible). -/
def integralPullbackFiniteComplex {X Y : AlgebraicGeometry.Scheme.{u}}
    (f : X ⟶ Y) (P : CochainComplex (integralTowerModules l E Y) ℤ) (n : ℕ) :=
  ((integralOperationsLevelPullback l E f n).mapHomologicalComplex (ComplexShape.up ℤ)).obj
    ((unrestrictedIntegralFiniteComplex l E Y n).obj P)

/-- The finite derived tensor on the two reduced K-flat representatives.
This is the recorded total tensor, before restricting its scalar action to the completion.
Source: Bhatt--Scholze, Lemma 6.5.5; Stacks Tag 09BQ
(blueprint: lem-pur-integral-operations-preserve-constructible). -/
def integralTensorFiniteComplex (W : AlgebraicGeometry.Scheme.{u})
    (P Q : CochainComplex (integralTowerModules l E W) ℤ) (n : ℕ) :=
  (Functor.uncurry.obj
    ((MonoidalCategory.curriedTensor
      (integralOperationsFiniteModules l E W n)).map₂CochainComplex)).obj
        (((unrestrictedIntegralFiniteComplex l E W n).obj P),
          ((unrestrictedIntegralFiniteComplex l E W n).obj Q))
```

## New

The same three definitions, verbatim, in
`Sheaf.Paper.IntegralOperationRoosEffectivity`, under the same
`@[expose] public noncomputable section`. The original module adds
`public import Sheaf.Paper.IntegralOperationRoosEffectivity`. The two canonical
comparison definitions and the upper theorem retain their original signatures and bodies
(except for the theorem proof). No mathematical definition or target meaning changes.
The original node's Lean attachment drops the moved declarations; the new node attaches them.

## Users

`tools/downstream.py Sheaf.Paper.IntegralOperationsPreserveConstructible --uses
integralOperationRoosProjection integralPullbackFiniteComplex integralTensorFiniteComplex`
found no downstream modules and only the defining module mentioning these names. This is
a relocation, not a withdrawal; unfinished parent proofs continue to see the same interface.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.IntegralOperationsPreserveConstructible | T5 | Publicly imports the new location; uses the same definitions. |
| Sheaf.Paper.IntegralOperationRoosEffectivity | new, T5 | Houses the unchanged definitions and the separate effectivity statement. |
| Sheaf.Paper.CompletedStalkFrobeniusReduction | unclaimed | Uses the relocated finite pullback definition; public name remains unchanged. |
| Sheaf.Paper.CompletedStalkReparametrizationCoherence | unclaimed | Uses the relocated finite pullback definition; public name remains unchanged. |

## Status

landed 20261020T221352-L-4178773 2026-10-20 (merge of deliver/T5/Sheaf.Paper.IntegralOperationsPreserveConstructible)
