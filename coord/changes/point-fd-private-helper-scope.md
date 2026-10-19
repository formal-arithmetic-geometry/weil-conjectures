# DerivedCategory.pointFdQbar_homInj

## Reason

The interface detector reports the scoped `omit` preceding a new private theorem
as a command change. It removes an unused algebraic-closure instance from that
private theorem only. No existing declaration, definition, instance, public import,
or target statement changes; this record documents the detected command addition.

## Old

The private helper and its scoped command were absent. The surrounding parameters
are unchanged:

```lean
variable (l : ℕ) [Fact l.Prime] (Ω : Type u) [Field Ω] [Algebra (Padic l) Ω]
  [IsAlgClosure (Padic l) Ω]
```

## New

The surrounding parameters above are retained verbatim. The new helper begins:

```lean
omit [IsAlgClosure (Padic l) Ω] in
private theorem pointFdQbar_homInj : (pointFdQbarCocone l Ω).HomInj := by
```

Its proof is complete. The `in` restricts the `omit` to that theorem and has no
scope over subsequent declarations. The private faithful-scalar-extension helper
also has a theorem-scoped transparency option for its proof elaboration.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.PointFdQbarCategory | J8 | Uses the proved private helper in the colimit proof. |

The helper is private, absent from the original library, and has no downstream
users. Existing importers see precisely the same public declarations and imports;
no consumer needs adaptation or a changed signature. No target definition changes,
so the target-statement semantic review is not reopened.

## Status

landed 20261019T005307-L-2749482 2026-10-19 (merge of deliver/J8/Sheaf.Paper.PointFdQbarCategory)
