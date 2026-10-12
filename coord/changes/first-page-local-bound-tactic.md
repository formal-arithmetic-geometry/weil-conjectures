# AlgebraicGeometry.Etale.etale_complex_first_page_continuity

## Reason

Return 2 from reviewer X-1ed64 requires the original public signature. It is now
restored verbatim, including omitted page-bound arguments. Default `lia` tactics
in those arguments inspect the large context: local compilation took 58.2 s and
then timed out at 60 s. A local macro resolves reflexive bounds immediately and
falls back to `omega`. It is a local elaboration command, not an exported tactic
or a change to the signature. The static checker flags added commands, so this
record documents the command and its checked downstream effect.

## Old

No local tactic macro before the theorem. The theorem signature is the original
repository signature, with omitted page-bound arguments; this repair preserves it
verbatim.

## New

```lean
-- Resolve reflexive page bounds before inspecting the large dependent context.
local macro_rules
  | `(tactic| lia) => `(tactic| first | exact le_refl _ | omega)
```

The command is before the theorem. All existing declaration signatures,
visibility and public imports are unchanged. Explicit `le_refl 1` witnesses
occur only inside the theorem proof.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.EtaleComplexFiltrationDeepening | E1 | Original unchanged importer compiled against the repaired sandbox overlay in 17.8 s; no adaptation. |

The returned explicit-bound signature failed in this importer at lines 88 and
234. That signature change has been removed; the original signature and node's
Lean record agree verbatim. This table describes the repaired version only.
No forced adaptation is delivered. The local macro is not exported.

## Status

landed 20261012T144137-L-2104543 2026-10-12 (merge of deliver/Q1/Sheaf.AlgebraicGeometry.EtaleComplexFirstPageContinuity)
