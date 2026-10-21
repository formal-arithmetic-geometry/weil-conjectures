# Q05 integral completion presentation: dependency repair

The stage-2 return at immutable head 2a6d22f27666 explicitly requires
lem-sf-finite-discrete-normalized-encoding to be a proof dependency, while a
new existing:true definition node owns the Encoding data used in the statement.
The retained worker packet already implements that H2 repair and compiles.

Repeated preflight failures arose because this proof dependency was absent from
the authoritative DAG. Stage-2 validation classifies a proof_deps difference as
a statement correction and then rejects it when the statement is unchanged.
Adding statement_change would also be rejected, correctly: no mathematical
statement correction occurred. Launcher deliver2 already preserves additions.

Maintenance records the reviewer-required proof dependency directly on main,
with its citation in proof step 1, so proof_deps remains exactly the union of
proof-step uses. The statement, statement dependencies and Lean interfaces are
unchanged. This is bookkeeping of the reviewer's existing requirement, with no
new proof or theorem implementation. The original node is retained next to it
as .json.maint-Q05-1792571862.bak.

Next worker: retain the repaired definition ownership and both Lean modules.
Rebase the item metadata from main, preserving the sandbox lean record and its
three added statement dependencies. The required proof dependency now comes
from main, so no statement_change or Statement corrected section is needed.
Run deliver2.py --no-push and deliver normally after validation.

Landing tools, launcher code, dispatcher counters and provider settings were
not changed. A general stage-2 dependency-only repair policy would require a
coordinated update to read_delivery, node_fields, graph application and landing;
that broader tooling change is outside this maintenance repair.
