# N5 groupoid module descent: H2 ownership repair

The return of immutable head 610be222011a required extracting the restriction and
tensor comparison definitions from lem-sfb-fibred-fppf-space-module-comparisons.
The retained worker packet made that extraction, but batch2/deliver2.py drops a
dependency node's statement and stmt_deps changes. Repeated successful dry runs
therefore omitted the same required repair.

Maintenance has created def-sfb-space-test-module-restriction-comparison from the
retained packet's definition statement, source and search records, and changed the
property theorem's statement to cite it. Only that theorem's statement and
stmt_deps changed; its properties, proof and review metadata are preserved.
The definition node deliberately has no lean record: its module still needs the
normal worker delivery and independent Lean review. No Lean source was landed by
this metadata repair.

Next N5 worker: fetch the current sheaf-dag base, keep the seven retained modules,
and retain the definition node in your sandbox with its lean record. It is now an
existing prerequisite, so lean.note must explain its previously absent binding.
Deliver the original item through deliver2.py after a fresh successful dry run.
Check that the packet preserves the properties-only theorem statement and its
new definition citation, with no NOT delivered messages. Do not recreate the
definition node under another id. The H2 return still applies and is not cleared
by this maintenance commit. This is an ownership correction, not a mathematical
statement correction, and no theorem signature or proof was changed.
