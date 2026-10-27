# realization_adjoint_comparisons proof context

## Reason

The proof uses private categorical localization helpers with independent category
universes. Preflight records their section, universe and variable commands and the
scoped unfolding command as a module-command interface change. All existing public
signatures, definition bodies and public imports remain verbatim. This record
covers proof elaboration commands only; no mathematical interface is changed.

## Old

The original module had no `RationalSquare` helper section or local unfolding
wrapper. Its option block contained:

```lean
set_option backward.isDefEq.respectTransparency false
```

The theorem body was `by sorry`.

## New

The option block additionally contains:

```lean
set_option backward.isDefEq.respectTransparency.types false
```

The proved private tensor-adjunction helpers are enclosed in this context:

```lean
section RationalSquare
universe r
variable (R : Type r) [CommRing R] (t : R)
  {C : Type uC} [Category.{vC} C] [Preadditive C] [Linear R C]
  {D : Type uD} [Category.{vD} D] [Preadditive D] [Linear R D]
  (WC : MorphismProperty C) (WD : MorphismProperty D)
  [(ScalarLocalization.localization R C t).IsLocalization WC]
  [(ScalarLocalization.localization R D t).IsLocalization WD]
  (P : C ⥤ D) (Q : D ⥤ C) [P.Additive] [P.Linear R] [Q.Additive] [Q.Linear R]
end RationalSquare
```

The unchanged public theorem is elaborated under:

```lean
unseal realizationPullScalarMap in
```

This makes the existing irreducible scalar-map abbreviation available to the proof
only, without changing its definition or exported reducibility. Every new helper
is private and proved. The private `import all
Sheaf.Paper.RealizationPullRationalDescent` reuses that module's proved raw
localization helpers, without adding a public import or new construction.

The complete module compiles cleanly through `lcompile.py` in 20.1 seconds.

## Users

`tools/downstream.py Sheaf.Paper.RealizationAdjointComparisons --names` returned
no current Lean importers. This is not a withdrawal: DAG parents with unfinished
proofs continue to use the unchanged theorem and its unchanged unit route.
No consumer requires adaptation because the mathematical public interface is
identical.

| module | group holding it | effect |
|---|---|---|
| `Sheaf.Paper.RealizationAdjointComparisons` | D6 | Proof context and theorem proof only; unchanged public API. |

## Status

landed 20261023T230637-L-3454910 2026-10-23 (merge of deliver/D6/Sheaf.Paper.RealizationAdjointComparisons)
