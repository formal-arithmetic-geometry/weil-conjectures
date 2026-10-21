# AlgebraicGeometry.ProEtale.FiniteDiscreteOrdinary.FiniteCoefficientModelComparison

## Reason

STATEMENT-DISPUTED: the original interval field parses as `(a ≤ b → V) ↔ W`,
because implication binds more tightly than the equivalence. If `b < a`, its left
side is true for every complex, but its right side requires vanishing in every
degree. For example, a nonzero constant module in degree zero over a geometric
point disproves it. The source and DAG require the equivalence only for `a ≤ b`.
Parenthesize the equivalence so that the inequality guards both sides.

## Old

```lean
  intervals : ∀ (K : DerivedCategory (Internal A X)) (a b : ℤ), a ≤ b →
    (∀ q : ℤ, q < a ∨ b < q →
      IsZero ((DerivedCategory.homologyFunctor (Internal A X) q).obj K)) ↔
    (∀ q : ℤ, q < a ∨ b < q →
      IsZero ((DerivedCategory.homologyFunctor (Ordinary A X) q).obj
        (e.ordinaryDerived.functor.obj K)))
```

## New

```lean
  intervals : ∀ (K : DerivedCategory (Internal A X)) (a b : ℤ), a ≤ b →
    ((∀ q : ℤ, q < a ∨ b < q →
      IsZero ((DerivedCategory.homologyFunctor (Internal A X) q).obj K)) ↔
    (∀ q : ℤ, q < a ∨ b < q →
      IsZero ((DerivedCategory.homologyFunctor (Ordinary A X) q).obj
        (e.ordinaryDerived.functor.obj K))))
```

The outer theorem signature, coefficient definitions, and all other fields are
unchanged. No declaration in `lean/Challenge.lean` changes. The target statements
and their meaning must be reviewed again if they use this comparison structure.
The repaired clause agrees with the unchanged mathematical node statement.

## Users

`python3 tools/downstream.py Sheaf.Paper.FiniteCoefficientModelComparison --uses
FiniteCoefficientModelComparison` reports two downstream modules. The only textual
users are this item and `IntegralResidueCriterion`, whose private proof import names
this module. Its theorem statement is independent of the comparison structure and
its proof is still `sorry`; it does not project the interval field. The indirect
consumer `IntegralOpenDirectImage` uses that theorem's unchanged statement. Neither
consumer needs adaptation, and neither changes meaning.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.FiniteCoefficientModelComparison | J5 | Correct the interval field and prove it using preservation and reflection of homology vanishing. |
| Sheaf.SixFunctors.ProEtale.IntegralResidueCriterion | unclaimed | Proof import only; statement independent of the structure; no adaptation. |
| Sheaf.SixFunctors.ProEtale.IntegralOpenDirectImage | unclaimed | Indirect proof consumer through the unchanged residue criterion; no adaptation. |

## Status

landed 20261021T214807-L-1856662 2026-10-21 (merge of deliver/J5/Sheaf.Paper.FiniteCoefficientModelComparison)
