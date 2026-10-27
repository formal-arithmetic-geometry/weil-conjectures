# Q126 stack versal-ring ownership maintenance

The returned stage-2 delivery 46e940302212 was required by L to give the
thirteen StackVersal definitions a definition-node owner and remove the
finite-residue-extension theorem from the existence item's statement dependencies.
The retained repair extracted those definitions, but stage2_delivery.py classifies
the sibling theorem as outside the corrected dependency closure, discards its
lean-only node update, and rejects its changed module as having no lean.file owner.
The same packet failed 48 dispatches; compilation was already successful.

Maintenance publishes that shared-library ownership extraction separately. The
thirteen names, signatures, bodies, instance attributes and docstrings are identical
apart from blueprint ownership tags. The finite-residue-extension theorem and its
proof docstring are byte-identical and publicly import the extracted definitions.
Only its lean record changes. The existence node gains the definition edge so the
new definition is reachable immediately; its Lean statement remains for the worker.
Both changed library modules compile separately with tools/lean_file.sh at 60 s.
Compile logs are stored alongside this note (uncommitted validation artifacts).
Adjacent .maint-Q126-1792856008.bak files preserve the three original files; backup
markers for the two new files record that they were absent before maintenance.

Next Q126 worker: retain the sandbox, rebase against current sheaf-dag, and rerun
deliver2.py Q126 lem-sfb-stack-versal-ring-existence --no-push, then deliver normally.
The sibling extraction now matches the base and is no longer part of that packet.
Do not restore the false theorem dependency. Existing downstream imports of
StackVersalFiniteResidueExtension continue to expose all original declarations.
The stage-2 item still requires the normal independent delivery review.

No launcher, review-service, preflight or landing tool was modified.
