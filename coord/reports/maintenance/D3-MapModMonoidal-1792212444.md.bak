# D3 maintenance: MapModMonoidal

The repeated stage-3 failures were caused by `tools/stage3_gate.py` rejecting
proof-field replacements inside the existing `mapModCoreMonoidal` and
`comapCoreMonoidal` definitions. The ten fields are proposition-valued
coherence obligations; their retained proofs compile, while the comparison
isomorphism data and all public signatures remain unchanged. The gate only
checks the enclosing declaration keyword and therefore rejects these valid
proof completions as non-theorem body changes.

The completed source repair is in commit `4fbd4b85e5acc96c4ff97f421fb9baa73f11d6ac`.
The pre-edit source backup is
`lean/WeilConjectures/CategoryTheory/ModuleObjects/MapModMonoidal.lean.bak-maint-20261017125019`.
The repaired module compiles with `tools/lean_file.sh` in 6.9 seconds; its
unchanged `UnitCoherence` consumer compiles in 6.3 seconds.

The protected gate owner should accept replacement of an existing `sorry` only
when the replaced field elaborates to a proposition, while continuing to
reject data-field changes, signature/import/attribute changes, and newly added
`sorry`s. No launcher-owned tool was edited by this maintenance.
