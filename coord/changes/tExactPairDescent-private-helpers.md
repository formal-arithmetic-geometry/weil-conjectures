# CategoryTheory.CommonStage.tExactPairDescent private proof helpers

## Reason

The proof uses a closed section to share its lengthy categorical hypotheses among
private lemmas. The static interface check detects these `variable`, `include`, and
section commands. They affect only private proof helpers: the original public
signatures, definitions, attributes and imports are unchanged. This record supplies
the requested review of those commands. The additive identity comparison is a private
theorem, installed as a local instance only inside `descent_exists`.

## Old

No `DescentProperties` section or private helper commands existed. The theorem body
was `by sorry`; all existing public declarations are preserved verbatim.

## New

The added section's variable command is:

```lean
variable (A B : ExactPairDiagram.{w, u, v} I)
  (RA : PairStructure A.toDiagram) (RB : PairStructure B.toDiagram)
  [HasShift RA.Obj ℤ] [HasZeroObject RA.Obj]
  [∀ n : ℤ, (shiftFunctor RA.Obj n).Additive]
  [Pretriangulated RA.Obj] [IsTriangulated RA.Obj]
  [HasShift RB.Obj ℤ] [HasZeroObject RB.Obj]
  [∀ n : ℤ, (shiftFunctor RB.Obj n).Additive]
  [Pretriangulated RB.Obj] [IsTriangulated RB.Obj]
  (P : ExactPairPresentation A RA) (Q : ExactPairPresentation B RB)
  (Φ : Family A.toDiagram B.toDiagram) (hb : Φ.Coherent)
  (F : RA.Obj ⥤ RB.Obj) (hF : IsDescent RA RB Φ F)

```

The section ends before the original theorem. `include hb hF in` and
`include P hb hF in` apply only to individual private helper theorems. The two scoped
`set_option backward.isDefEq.respectTransparency false in` commands also apply only
to private helper proofs. No global instance is introduced. All helpers are proved.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.CategoryTheory.Triangulated.TExactPairDescent | G8 | Fills its only hole; public interface unchanged. |

`tools/downstream.py Sheaf.CategoryTheory.Triangulated.TExactPairDescent --uses
CategoryTheory.CommonStage.tExactPairDescent` reports zero downstream modules and
only the declaration's own module as a textual user. No consumer adaptations are needed;
parents with unfinished proofs retain the same theorem and node.

## Status

landed 20261023T102803-L-2973306 2026-10-23 (merge of deliver/G8/Sheaf.CategoryTheory.Triangulated.TExactPairDescent)
