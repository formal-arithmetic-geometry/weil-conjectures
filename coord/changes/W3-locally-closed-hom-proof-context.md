# Sheaf.Paper.LocallyClosedHomGenerator proof context

## Reason

Keep the large derived functors and specified comparison constructions behind their
published APIs while elaborating the normalization proof. Irreducibility follows the inverse construction and precedes the comparison predicate.
No declaration signature changes. The totalized inverse construction is replaced by the
unique inverse supplied by invertibility of the same specified arrow.
The proof uses four new intermediate statements, listed in report.md. No adopted
source-library module is edited.

## Old

The original declaration header was:

```lean
open CategoryTheory Limits Opposite
open scoped CategoryTheory.Functor
```

No local irreducibility attributes followed the definitions. The theorem body was `by sorry`.
The old inverse body was:

```lean
  open Classical in
  if h : IsIso (internalAdjunction A g j L M) then
    @inv _ _ _ _ (internalAdjunction A g j L M) h
  else 0
```

## New

The opens remain unchanged. The inverse body is now:

```lean
  @inv _ _ _ _ (internalAdjunction A g j L M)
    (locallyClosedInternalAdjunction_isIso A g j L M)
```

The theorem uniquely determines the inverse; no arbitrary existence witness is selected.
Since it proves the old `if` condition, this is equal to the old body. Its module is now
publicly imported, as a public construction uses that theorem. Before the normalization predicate:

```lean
attribute [local irreducible] derivedHom derivedTensor upperStar lowerStar
attribute [local irreducible] internalAdjunction evaluationComparison
  ordinaryComparison compactComparison etaleShriekLocallyClosedCoefficientMap
```

Other new proof imports are private. Original public imports remain. Private
unused dimension imports and the redundant direct-image import are removed.
All existing public signatures remain verbatim. IsNormalizedComparison now applies the generic `CategoryTheory.NormalizedComparisonWord`
predicate to precisely the same seven invertibility claims and six-factor equality. The
generic definition unfolds to the old conjunction verbatim; this changes representation
without adding or dropping a claim. Its proved constructor assembles the conjunction
with abstract category instances, avoiding repeated normalization of geometric data.
The new module is `Sheaf.Paper.NormalizedComparisonWord`, publicly imported by the item.
The other two abbreviations remain verbatim. No diagnostic options or instance-priority overrides remain in the final packet.

## Users

`tools/downstream.py Sheaf.Paper.LocallyClosedHomGenerator` reports zero Lean downstream
modules. DAG parents still need the item; none is withdrawn. Local attributes do not
propagate to importers, so no consumer adaptation is required.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.LocallyClosedHomGenerator | W3 | Proof reduction and local proof context. |

## Status

landed 20261025T203559-L-2830098 2026-10-25 (merge of deliver/W3/Sheaf.Paper.LocallyClosedHomGenerator)

## Old definitions verbatim

```lean
def inverseInternalAdjunction (g : Z ⟶ X) [IsClosedImmersion g]
    (j : S ⟶ Z) [IsOpenImmersion j]
    (L : DerivedCategoryModule A S) (M : DerivedCategoryModule A X) :
    ((derivedHom (ModuleCat A) X).obj (op ((shriek A g j).obj L))).obj M ⟶
      (star A g j).obj (innerHom g j L M) :=
  open Classical in
  if h : IsIso (internalAdjunction A g j L M) then
    @inv _ _ _ _ (internalAdjunction A g j L M) h
  else 0

/-- The displayed factors, their invertibility, and the equality to the evaluation transpose.
Here b is the published exceptional comparison, q the open-then-closed scalar map,
c the ordinary counit-defined map, and u the coefficient change of evaluation.
Source: thm-coef-finite-hom, paragraphs 3--4
(blueprint: lem-coef-locally-closed-hom-generator). -/
def IsNormalizedComparison (φ : A →+* B) (g : Z ⟶ X) [IsClosedImmersion g]
    (j : S ⟶ Z) [IsOpenImmersion j]
    (L : DerivedCategoryModule A S) (M : DerivedCategoryModule A X) : Prop :=
  IsIso (internalAdjunction A g j L M) ∧
  IsIso ((scalarExtension φ X).map (inverseInternalAdjunction g j L M)) ∧
  IsIso (ordinaryComparison φ g j (innerHom g j L M)) ∧
  IsIso ((star B g j).map (evaluationComparison φ S L (exceptionalObject g j M))) ∧
  IsIso ((star B g j).map
    (((derivedHom (ModuleCat B) S).obj (op ((scalarExtension φ S).obj L))).map
      (etaleShriekLocallyClosedCoefficientMap φ g j M))) ∧
  IsIso (internalAdjunction B g j ((scalarExtension φ S).obj L)
    ((scalarExtension φ X).obj M)) ∧
  IsIso (((derivedHom (ModuleCat B) X).map (compactComparison φ g j L).op).app
    ((scalarExtension φ X).obj M)) ∧
  ((scalarExtension φ X).map (inverseInternalAdjunction g j L M) ≫
      ordinaryComparison φ g j (innerHom g j L M) ≫
      (star B g j).map (evaluationComparison φ S L (exceptionalObject g j M)) ≫
      (star B g j).map
        (((derivedHom (ModuleCat B) S).obj (op ((scalarExtension φ S).obj L))).map
          (etaleShriekLocallyClosedCoefficientMap φ g j M)) ≫
      internalAdjunction B g j ((scalarExtension φ S).obj L)
        ((scalarExtension φ X).obj M) ≫
      ((derivedHom (ModuleCat B) X).map (compactComparison φ g j L).op).app
        ((scalarExtension φ X).obj M)) =
    evaluationComparison φ X ((shriek A g j).obj L) M

```

## New definitions verbatim

```lean
def inverseInternalAdjunction (g : Z ⟶ X) [IsClosedImmersion g]
    (j : S ⟶ Z) [IsOpenImmersion j]
    (L : DerivedCategoryModule A S) (M : DerivedCategoryModule A X) :
    ((derivedHom (ModuleCat A) X).obj (op ((shriek A g j).obj L))).obj M ⟶
      (star A g j).obj (innerHom g j L M) :=
  @inv _ _ _ _ (internalAdjunction A g j L M)
    (locallyClosedInternalAdjunction_isIso A g j L M)

attribute [local irreducible] derivedHom derivedTensor upperStar lowerStar
attribute [local irreducible] internalAdjunction evaluationComparison
  ordinaryComparison compactComparison etaleShriekLocallyClosedCoefficientMap

/-- The displayed factors, their invertibility, and the equality to the evaluation transpose.
Here b is the published exceptional comparison, q the open-then-closed scalar map,
c the ordinary counit-defined map, and u the coefficient change of evaluation.
Source: thm-coef-finite-hom, paragraphs 3--4
(blueprint: lem-coef-locally-closed-hom-generator). -/
def IsNormalizedComparison (φ : A →+* B) (g : Z ⟶ X) [IsClosedImmersion g]
    (j : S ⟶ Z) [IsOpenImmersion j]
    (L : DerivedCategoryModule A S) (M : DerivedCategoryModule A X) : Prop :=
  letI := locallyClosedInternalAdjunction_isIso A g j L M
  MappedComparisonWord (scalarExtension φ X) (star B g j)
    (derivedHom (ModuleCat B) X) (internalAdjunction A g j L M)
    (ordinaryComparison φ g j (innerHom g j L M))
    (evaluationComparison φ S L (exceptionalObject g j M))
    (((derivedHom (ModuleCat B) S).obj (op ((scalarExtension φ S).obj L))).map
      (etaleShriekLocallyClosedCoefficientMap φ g j M))
    (compactComparison φ g j L) ((scalarExtension φ X).obj M)
    (internalAdjunction B g j ((scalarExtension φ S).obj L) ((scalarExtension φ X).obj M))
    (evaluationComparison φ X ((shriek A g j).obj L) M)
```

The mapped representation expands first to NormalizedComparisonWord, then to the old conjunction. It uses the same unique inverse, with the supplied isomorphism proof irrelevant. No target meaning changes; the definition representation is submitted for independent review.
