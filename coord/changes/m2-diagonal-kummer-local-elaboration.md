# Diagonal Kummer proof and local elaboration settings

Group: M2. Item: Sheaf.Paper.DiagonalKummerReduction.

The only existing Lean file changed is the assigned item, held by M2.
Its original theorem signature and sole public import stay verbatim. Its proof
now combines the ordinary source quotient, strict Kummer transport, and full
Cartier scalar-adjunct uniqueness. Two genuine lower theorem holes remain.

The item adds only local instance attributes selecting the proved public
kummerModuleHasExt and kummerAbHasExt caches, and local irreducibility attributes
for the large existing Ext, derived-category and coefficient constructions.
These attributes expire at the end of the file. No global instance, priority,
attribute, notation, category structure or public import of an existing module
changes. The new modules and definitions are all under Sheaf.Paper; their complete
interfaces and two remaining proof obligations are listed in report.md and their nodes.

The static interface scanner reports the changed attribute commands conservatively.
No consumer adaptation is required: the existing statement and public imports are
identical, and all changed attributes on existing declarations are explicitly local.
The existing node changes only proof, proof_deps and proof_origin. All twelve
packet modules compiled before removal of the diagnostic profiler options; the
assembly and item kernel checks took 35.3 and 29.3 seconds respectively.

No WeilConjectures source declaration, other existing module, target, definition,
statement, binder or universe is changed. There are no forced adaptations.
