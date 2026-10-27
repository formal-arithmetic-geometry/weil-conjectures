# RingTheory.isRegularRing_transverseLocalRootFamily

## Reason

The stage-3 interface comparison records the added `section Proof`, its two
elaboration options and its closing `end Proof` as changed commands. They scope
proof elaboration only. Every existing public declaration signature, definition
body, attribute and public import is unchanged. All added declarations are private
and proved. There are no global instances or exported registrations.

## Old

The original module had no proof-local section or corresponding options, and
`RingTheory.isRegularRing_transverseLocalRootFamily` had proof `by sorry`.
The surrounding commands were:

```lean
@[expose] public section

set_option autoImplicit false

universe u v

namespace RingTheory
```

The module ended with `end RingTheory`.

## New

The original commands above remain verbatim. Immediately after the four existing
presentation definitions, the proof helpers and the original theorem are enclosed by:

```lean
section Proof

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
```

After the theorem proof, `end Proof` closes this scope, followed by the unchanged
`end RingTheory`. The theorem has a complete proof and zero holes. These options
only guide elaboration of the local proof and do not alter its elaborated statement.

## Users

`python3 tools/downstream.py Sheaf.RingTheory.TransverseLocalRootFamilyRegular
--uses RingTheory.isRegularRing_transverseLocalRootFamily` reports zero downstream
modules; its only textual declaration use is its own declaration.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.RingTheory.TransverseLocalRootFamilyRegular | D3 | Proof only; existing public API unchanged. |

No consumer adaptation or target statement review is needed: all existing
statement and definition text and public imports have been compared verbatim.
The DAG parent remains needed and is preserved; no withdrawal is proposed.

## Status

landed 20261023T123429-L-1187152 2026-10-23 (merge of deliver/D3/Sheaf.RingTheory.TransverseLocalRootFamilyRegular)
