# Q27 log-chart definition ownership maintenance, 2026-10-25

Repeated stage-2 preflight failures on lem-trf-free-log-chart-ordinary-parameters
were caused by scope: H2 requires relocating two definitions out of theorem
modules, while H7 at d88fff709c48 requires removing the unused theorem proof
dependencies. Those two former-owner edits then fall outside the item closure,
and the delivery reader rejects their modules as unowned. Repeating the same
packet cannot satisfy both requirements through the worker ownership rules.

This maintenance applies the already accepted H2 extraction separately on main.
EtalePrelogStructure.etaleRestrict and strictLocalRingStrictHenselizationIso
move unchanged to LogEtaleRestrictionStalkComparison, owned by the definition
node def-trf-log-etale-restriction-stalk-comparison. Both former theorem modules
publicly import it, relinquish the moved declaration in lean.declarations, and
record the new definition prerequisite. All remaining declarations, theorem
signatures, proofs and proof docstrings are unchanged. Mechanical comparisons
verified the exact moved blocks modulo blueprint owner tags and exact consumer
residuals. The new definition record is the accepted worker record from H2.

Validation: incremental DAG validation passed, and tools/land_set.sh compiles
the three modules in import order, separately via tools/lean_file.sh with 60 s
per file, then checks imports and registers an interface landing for normal
global verification. No lake build was invoked by maintenance.

The item itself is not landed here. Its proof_deps, proof and statement remain
unchanged. Q27 should retain its H7 repair, cite the now-landed definition node
and def-trf-log-regular-pair, remove the six now-landed shared module/node copies
from the delivery packet, run deliver2.py --no-push and deliver normally. The
original return remains for independent review. No dispatcher, preflight,
review, admission or landing tool was edited, and no artificial dependency,
concurrency restriction or pause was added.


## Receipt

Ownership extraction commit: e2289db2bb494e7ec081c6325853954b46ec17e3.
Single-file compile times: definition owner 3.9 s; locality consumer 2.0 s;
completed-chart consumer 2.3 s. No warnings or errors. Interface landing
20261024T201547-MAINTQ27-2791271 was registered for normal global verification.
The new definition node carries reviewed/reviewed_lean provenance based on the
independent H2 acceptance and exact mechanical relocation comparison, so it
continues as a stated definition rather than an unreviewed new assignment.

After backing up and removing the six already-landed shared files from the Q27
packet, unchanged deliver2.py --no-push passed server preflight and compilation
at bfe6e82e0b5, staging only the item node, its module and its worker report.
The item remains subject to the original independent repair review.
