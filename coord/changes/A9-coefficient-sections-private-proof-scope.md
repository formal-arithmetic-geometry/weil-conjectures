# AlgebraicGeometry.ProEtale.set_sections_filtered_colimit

## Reason

Restore the quarantined module and close its final proof hole. The static interface detector flags
the new `section SetComparison`, `variable`, and `omit` commands. These only parameterize proved
private helper theorems inside a section that ends before any existing public theorem. No public
signature, definition, instance, attribute, notation, public import, or universe binder changes.

## Old

There was no helper section between `namespace AlgebraicGeometry.ProEtale` and the first public
theorem. The public comparison theorem had proof `by sorry`. The quarantine archive is preserved.

## New

```lean
section SetComparison

variable {X : Scheme.{u}} {I : Type v} [SmallCategory I] [IsFiltered I]
  {F : I ⥤ Sheaf (Scheme.ProEt.topology X) (Type (max (u + 1) v))}
  {c : Cocone F}
```

This block scopes the proved private helpers `presheaf_colimit`, `local_representatives`,
`local_equality`, `eventual_equality`, `stage_injective`, and `section_representative`.
`omit [IsFiltered I] in` immediately precedes the first two helper declarations because their
statements and proofs need no filteredness. The section ends with:

```lean
end SetComparison
```

The existing public comparison theorem now has a complete proof. All three existing public
signatures and all existing public imports match the archived source verbatim. The two existing
public downstream proofs are unchanged. Every new helper has a complete proof.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.CoefficientFiniteDescentSections | A9 | Restored and proved; public interface unchanged. |

`tools/downstream.py Sheaf.Paper.CoefficientFiniteDescentSections` reports "unknown module(s)"
because the item is quarantined and absent from `lean/` at the current base. An explicit search
of every `.lean` file in both `lean/` and `quarantine/` finds no import of this module and no
external occurrence of its public declaration names. Thus there are no Lean consumers to adapt.
DAG parents remain attached to the existing node, whose statement and Lean attachment are unchanged.
The helper-section commands end before the public statements, so they change no consumer's
elaboration context. The clean single-file compile checks the unchanged public proofs against the
new private helper proofs. No target statement or target-used definition changes.

## Status

landed 20261021T023253-L-2943136 2026-10-21 (merge of deliver/A9/Sheaf.Paper.CoefficientFiniteDescentSections)
