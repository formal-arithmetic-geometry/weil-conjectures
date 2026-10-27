# Maintenance extraction for N7 product-subseries H2 return

The independent return of immutable head 0e5b17a239f5 requires a definition owner
for ProjectiveSpace.fieldSections and removal of the unrelated regularity theorem
from the consumer statement dependencies. The worker implemented that extraction,
but stage2_delivery.py excludes the former owner from the consumer prerequisite
closure and then rejects its edited module as unowned (preflight (c)). Repeating
the same packet cannot repair that ownership deadlock.

This maintenance commit performs the shared-library extraction first. The full
fieldSections name, type and body are unchanged; MRegularConsequences publicly
imports the new module, and its node now cites the definition and removes only
fieldSections from its own declaration inventory. Its theorem is unchanged.
No pipeline gate, review service, landing tool or launcher-owned file is edited.

Validation: scompile.py compiled FieldGlobalSections, MRegularConsequences and
the retained ProductSubseriesEventualFullness consumer one at a time through
tools/lean_file.sh with the default 60 s limit; all clean, actual module compile
times 6.1 s, 2.9 s and 3.5 s respectively. A byte comparison checked that the old
module differs only by removing the definition block and adding its public import.

Worker handoff: cite the landed def-sfb-field-global-sections; keep the consumer
public import of FieldGlobalSections. Remove the already-landed definition and
old-owner node/module copies from the delivery packet, retaining their .bak files.
Run deliver2.py N7 lem-sfb-product-subseries-eventual-fullness --no-push and then
its normal delivery command. Preserve the reviewed theorem statement and proof
plan; no artificial theorem edge or statement_change is required.

Every edited existing file has a sibling .maint-N7-product-subseries-20261024.bak
preimage. New files have a .bak copy of their initial content (they had no preimage).
