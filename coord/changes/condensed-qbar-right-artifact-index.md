# constructibleToQbar_exchange_right_adjunct

## Reason

The returned right-adjunct module checked ordinarily but timed out while exporting
artifacts. Diagnostics isolated Lean's symbol-frequency and Sine Qua Non premise
indices. Both traverse the concrete theorem type, repeatedly scanning large inferred
derived-category instance terms. A scratch traversal measured the final identity's
scan at about 19 seconds per pass; kernel checking and axiom collection succeeded.
Opacity-only experiments did not remove these structural dependency scans.

## Old

The returned right module ends immediately after its namespace. Every public theorem
is eligible for Lean's two global premise-index export passes, including the concrete
`constructibleToQbar_exchange_right_adjunct` identity. Its full artifact compilation
timed out at 60 seconds.

## New


Append a command using Lean's documented
`LibrarySuggestions.nameDenyListExt.addEntry` API, with the exact name component
`constructibleToQbar_exchange_right_adjunct`. The appended code is:

```lean
run_cmd do
  Lean.modifyEnv fun env =>
    Lean.LibrarySuggestions.nameDenyListExt.addEntry env
      "constructibleToQbar_exchange_right_adjunct"
```

No existing declaration text changes.
The theorem's statement, proof, visibility, and direct applications remain identical.
The generic mate and finite-to-Qbar counit identities remain available to premise
suggestions. Only automatic premise suggestions omit the concrete final identity.
No compiler limit or kernel check changes; no files or proofs are split.

## Users

`Sheaf.Paper.CondensedQbarExchangeEquality` applies the theorem explicitly and compiles
against the exported artifact. The six delivered modules are unchanged apart from
this command and retain their existing signatures. No additional consumer adaptation
is required. The prior MorphismDefs exposure adjustment and its forced
BoundedExchangeAmbient import remain documented separately in
`condensed-pullback-square-interface.md`.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.CondensedQbarExchangeRightAdjunct | unclaimed | Exclude the named theorem from premise indices; all theorem signatures and proofs preserved. |
| Sheaf.Paper.CondensedQbarExchangeLeftAdjunct | unclaimed | Importing the index filter changes suggestions only; explicit helper applications compile. |
| Sheaf.Paper.CondensedQbarExchangeEquality | A3 | Explicit use of the right adjunct compiles; no statement or proof change from the returned revision. |

## Status

landed 20261016T091300-L-1890425 2026-10-16 (merge of deliver/A3/Sheaf.Paper.CondensedQbarExchangeEquality)

The right-adjunct artifact exported in 28.5 seconds with an explicit 60-second timeout.
All six delivered modules exported without warnings under the same 60-second
per-file limit. The repair awaits the independent reader; no delivery was pushed.
