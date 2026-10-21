# AlgebraicGeometry.ProEtale.VaryingRing.gamma_evaluation

## Reason

The final coefficient-normalization proof needs private categorical helpers for
`AdjunctionEvaluation`, with a generic category universe. The static command scan
requires a record for the added private section and its local open command. All
existing public signatures, attributes, public imports and data definitions are
unchanged. No target statement or target definition changes.

## Old

The module used `universe u` and had no private `Evaluation` section. Its final
public declaration had this signature and a `sorry` body:

```lean
theorem gamma_evaluation {V W S T : Scheme.{u}} (k : V ⟶ W) (r : V ⟶ S)
    (p : W ⟶ T) (i : S ⟶ T) [IsOpenImmersion k] [IsOpenImmersion i]
    [QuasiCompact k] [QuasiCompact i] [IsProper r] [IsProper p]
    (h : k ≫ p = r ≫ i) (M : Derived R φ V) (n : ℕ) :
    (ev R φ T n).map ((gamma R φ k r p i h).app M) ≫
        (evalP R φ p n).hom.app ((J R φ k).obj M) ≫
        (StrictTower.moduleDirectImage (R n) p).rightDerivedFunctor.map
          ((evalJ R φ k n).hom.app M) =
      (evalJ R φ i n).hom.app ((P R φ r).obj M) ≫
        (StrictTower.moduleJ (R n) i).mapDerivedCategory.map
          ((evalP R φ r n).hom.app M) ≫
        constantGamma (R n) k r p i h ((ev R φ V n).obj M) := by
  sorry
```

## New

The same declaration has a complete proof from the two separately recorded
geometric coefficient comparisons, of which the cartesian-open comparison is
now fully proved and the existing `evaluation_mate` theorem.
The new outer commands are:

```lean
universe u k

section Evaluation
open WeilConjectures.SemilinearSections
```

The section ends after `gamma_evaluation`. Its three added helpers
`evaluationOfMate`, `properEvaluation` and `strictEvaluation` are private and have
complete bodies. The extra universe is used only by `evaluationOfMate`; it does
not add a parameter to any existing public declaration. The private proof import
is `Sheaf.AlgebraicGeometry.VaryingRingClopenArrowEvaluation`.

Four new modules construct the two actual factors, state their geometric
coefficient comparisons, and prove the assembly equation. Their interfaces are
recorded by their new nodes. No existing definition or statement is repaired,
weakened, strengthened, or renamed.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.VaryingRingProperOpenPasting | A5 | New private proof section; final theorem signature identical. |
| Sheaf.SixFunctors.SemilinearProperOpenMatePasting | U4 | Existing consumer of gamma_evaluation; identical signature and visibility, no source adaptation. |
| Sheaf.AlgebraicGeometry.VaryingRingClopenArrowFactors | A5, new | Actual factor constructions and proved factorizations; no existing consumer to adapt. |
| Sheaf.AlgebraicGeometry.VaryingRingOpenBaseChangeEvaluation | A5, new | Proved arbitrary-ring cartesian-open comparison. |
| Sheaf.AlgebraicGeometry.VaryingRingClopenSectionEvaluation | A5, new | Separate clopen-section geometric comparison. |
| Sheaf.AlgebraicGeometry.VaryingRingClopenArrowEvaluation | A5, new | Proved assembly of the two comparisons. |

`tools/downstream.py Sheaf.AlgebraicGeometry.VaryingRingProperOpenPasting --uses
gamma_evaluation` reports precisely the item and the one existing external
consumer above as declaration users (38 modules import the item transitively).
Because its signature and all data definitions stay identical, none needs an
adaptation. No module held by another group is edited.

## Status

landed 20261021T060929-L-1669963 2026-10-21 (merge of deliver/A5/Sheaf.AlgebraicGeometry.VaryingRingProperOpenPasting)
