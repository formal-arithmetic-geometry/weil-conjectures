Maintenance: Sheaf.SixFunctorsBasics.BrownHypothesesArbitraryFieldCompactness

Cause: a false split was repeatedly assigned as a proof item. The ordinary
no-new-hole gate then refused the correct rollback of its dependent Brown
assembly. See coord/changes/maintenance-K4-brown-false-split-rollback.md.

The maintenance commit applies the retained K4 Lean repair, updates five DAG
plans, and records the retirement of both false statements with statement_change.
The item has zero direct holes and remains useful to the supported finite-field
and conditional integral proofs. The original Brown theorem remains disputed
and unresolved with exactly its previous signature. Net proof progress is zero.

All changed existing files have adjacent .maint-K4-brown-1793068709.bak backups.
The commit transaction validates changed nodes and compiles the two changed
modules and both direct importers sequentially with tools/lean_file.sh.
Validation output is retained under local/maintenance/K4-brown-1793068709/.

Next worker: refresh from sheaf-dag and preserve this correction. Do not recreate
the retired obligation/witness, or retry the pre-repair false-split packet. No
gate exception is needed now: the restored Brown hole is on the baseline.
Read the original Brown dispute before attempting that parent item; changing a
unit or target statement still needs the human's decision. Launcher state,
failure counts, admission, concurrency, and landing tools were not modified.
