# AlgebraicGeometry.Etale.finite_range_exchange_comparison: abutment elaboration

## Reason

Repair of H10, reviewer X-18231, returned head 182318d4b. The retained
local irreducibility setting alone did not keep this module below the
60-second compilation limit. The unchanged returned version again timed out
locally, both in the sandbox build and standalone.

Timing probes located the expensive tactic at the single long dependent
`obtain` extracting the abutment data in `hcoh`. The preceding main-proof
steps elaborated in about five seconds. Naming the remaining abutment
proposition after each group of witnesses avoids elaborating that entire
nested pattern in one tactic invocation. This repairs the elaboration of
existing data; no definition, signature, theorem, module boundary, or proof
argument is replaced or split off.

## Old

```lean
    obtain ⟨_, _, _, _, LN, MN, AN, BN, hAN, hBN, _, _, _, _, hfinA, hfinB,
      _, _, i, j, _, _, U, V, hU, hV, _, _, _, t, _, _,
      lift, hlift, grN, hgrN, zN, tiN, hzN, htiN, eN, eN', _, _, _, _, hcomp⟩ := habut n
```

## New

```lean
    -- Keep the dependent abutment data in short elimination steps. A single long
    -- pattern makes elaboration repeatedly process the full remaining telescope.
    obtain ⟨_, _, _, _, LN, MN, AN, BN, hAN, hBN, hrest⟩ := habut n
    obtain ⟨_, _, _, _, hfinA, hfinB, _, _, i, j, _, _, U, V, hU, hV, hrest⟩ := hrest
    obtain ⟨_, _, _, t, _, _, lift, hlift, grN, hgrN, zN, tiN, hzN, htiN,
      eN, eN', _, _, _, _, hcomp⟩ := hrest
```

The same witnesses and properties feed the same remaining proof. All other
Lean lines are identical to the returned sandbox. In particular, the local
irreducibility setting is retained and no extra reducibility setting is added.
The theorem signature is byte-for-byte unchanged from the returned version.

## Users

The current shared repository's `tools/downstream.py` reports zero downstream
modules of `Sheaf.AlgebraicGeometry.FiniteRangeComparison`; the sole occurrence
of the theorem name is its own declaration. The retained source comparison
also confirms the proof still closes the original shared-repository hole.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.FiniteRangeComparison | C3 | Existing proof elaborates in 14 seconds; its statement and mathematical argument are unchanged. |

No consumer adaptation is needed. The retained changes in
`DerivedCoupleFunctoriality` and their users are documented in the earlier
change records; this repair does not modify that module. No target statement
or public definition changes and no target statement review is reopened.

Validation: `lcompile.py --all` compiled `DerivedCoupleFunctoriality` in 4.9 s
and `FiniteRangeComparison` in 14.2 s. Standalone compilation of the latter
took 14.0 s. The compiled-module `#print axioms` audit reports only
`propext`, `Classical.choice`, and `Quot.sound` for the target and the exposed
helpers (only `propext` for the reused transport lemma). Both modules contain
zero `sorry` tokens, no forbidden declarations, and no Lean line over 100
characters. Profiling commands have been removed.

## Status

landed 20261016T075723-L-1295295 2026-10-16 (merge of deliver/C3/Sheaf.AlgebraicGeometry.FiniteRangeComparison)
