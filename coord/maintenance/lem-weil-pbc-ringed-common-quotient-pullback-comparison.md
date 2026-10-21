# NF common-quotient maintenance, 2026-10-21

The returned item needs a definition-only module for F1, but relocating its definitions
also modifies a proved dependency module. The stage-2 proof-shape checker rejects that
module's preserved proofs. The failure-count note says thirteen; current direct inspection
finds twenty-two theorem declarations rejected by the same rule. No provider fault is involved.

This maintenance commit extracts the seven public definitions into
Sheaf.Algebra.Homology.SuccessiveDerivedQuotientData, adds their owning definition node,
and makes the normalization theorem publicly import it. Definition code is identical
after the blueprint-citation replacement; the entire 43,651-byte proof suffix is identical.
The theorem node now owns only its theorem and cites the definition node.

Private tools/lean_file.sh checks passed, one file at a time, with the existing 60 s limit:
data 17.7 s; normalization 35.7 s; existing importer RingedCoefficientProjectionData 23.4 s.
The new definition module also passes check_lean_text.
The change is registered as a normal interface landing through landing.new_record.
Every installed path has a .maint-NF-1792572867.bak (new-file backups contain the installed text).

The next worker should use the landed definition node, keep it in the item's stmt_deps,
and omit both normalization/data modules and their node copies from the stage-2 packet.
Import the data module directly. Preserve RingedTopoiDerivedPullbackIndependent and its
dependency-node repair. Repair F2's actual identity and composable-geometry coherence
equations, compile and run deliver2.py --no-push, then deliver normally. F2 is not repaired
by this maintenance commit. No checker, dispatcher, landing tool or concurrency setting changes.
