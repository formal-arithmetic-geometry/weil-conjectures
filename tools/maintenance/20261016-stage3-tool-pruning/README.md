# Stage-3 tool approval pruning

The C3 FiniteRangeComparison return at d8f916d90d required removing the obsolete
top-level tool_uses entry lem-sp-page-induction. deliver3.py silently retained it,
preflight forbade changing the field, and batch_land.py did not copy its changes.

stage3_delivery.py now checks deletion-only changes; the packager and batch lander
apply only those removals. Independent approvals added on the current tip survive.
The standing stage-3 brief documents this exception. New approvals still require
the maintainer, and changed node files still require CODEX review.

deliver3.py here is the deployed launcher snapshot. Its live path is
/home/ubuntu/weil-launcher/deliver3.py on the dispatcher machine. Tests select the
snapshot by default; WEIL_DELIVER3_SOURCE can select another copy.

Run from the project root:

    SHEAF_LEAD=L-only python3 -m unittest discover -s tools -p test_stage3_tool_pruning.py -v
    SHEAF_LEAD=L-only python3 -m unittest discover -s tools -p test_red_recovery.py

The regression runs the actual packager against a temporary git repository,
checks the packaged node with check_nodes, and runs the actual land_one function
with fake landing/claim processes. It also covers null/absent/empty field removal,
rejection of additions/replacements/reordering, and preservation of current audits
and independently added approvals. No Lean or live service is run by these tests.

The existing autoland3 process imports the lander once at startup. No process was
stopped: the new lander code takes effect on its next normal start. The obsolete
entry was also deleted directly from the live item node under coord/.merge.lock,
so the current process can land this item's next delivery without restoring it.
Keep the C3 return and claim until the independent reader delivers normally.
