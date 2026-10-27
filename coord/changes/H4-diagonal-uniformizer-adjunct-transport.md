# Diagonal uniformizer adjunct transport

The existing item keeps its public theorem signature and public import. Its proof
now uses the completed first square, the proved two-scalar calculation, and the
finite unit square, composing their arbitrary-arrow versions. The delivery adds
seven modules, with explicit unit-arrow constructions and proved APIs; only the
completed square and finite unit square remain as separate named obligations.
The original mathematical obligation is decomposed rather than completely proved.

Within the item, local irreducibility annotations for shifted-line and quotient
endpoint definitions keep elaboration from expanding large coefficient records.
These annotations are local to the file. No existing public definition, global
attribute, instance or signature is changed. The two private endpoint and assembly
lemmas are proved. The syntactic proof construction for associativity and the last
definitional conversion produces ordinary kernel-checked proof terms.

No existing module besides the assigned item is edited. The delivery tool compiled
its direct importer, `Sheaf.Paper.DiagonalUniformizerChernNormalization`, against
the delivery unchanged (51 seconds). All eight delivered Lean modules compiled
within 60 seconds; the maximum was 56.7 seconds and the item took 32.6 seconds.

The node of the item now records the completed square and generic assembly route.
Seven new nodes record the new modules, their dependencies and complete proof plans.
No target statement changes, source-library changes, withdrawals or global pruning
are claimed.
