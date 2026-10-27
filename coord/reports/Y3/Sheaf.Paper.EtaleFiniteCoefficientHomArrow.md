## What changed

Completed `WeilConjectures.finiteHomEtaleRepresentativeData_existsUnique` in
`Sheaf.Paper.EtaleFiniteCoefficientHomArrow`. Two proved private helpers identify
the normalized closed tensor with the native derived tensor and construct a
representative record with prescribed generators and localization maps. The main
proof specializes this construction using the existing quotient normalization.

After profiling slow kernel comparisons, stored the same cochain category, its
category instance, total tensor and localization in the native tensor record,
and shared their etale specialization before coefficient specialization.
A source wrapper and generic representative abbreviation reuse those actual
projections together, avoiding repeated specialization of each source field.
A generic inclusion API has the native projected tensor object as codomain and
retains exactly the original signed-total summand inclusion.
Existing domains and tensor objects are definitionally equal to the old ones;
the normalization conditions and actual maps are retained. The two conditions
are stored in a generic proof record; the etale normalization abbreviates its
specialization, and dot projections give exactly the same pointwise equalities.
Public imports are unchanged. Updated the node's proof, proof origin and declaration list.
See `coord/changes/Y3-etale-representative-cochain-sharing.md` for exact old/new
text and consumer effects.

The final item compiled cleanly in 50.4 seconds through `lcompile.py`.
The temporary audit also compiled: the new normalization is equivalent to the
original generator predicate together with every original model predicate.
An ordered validation batch compiled all seven direct importers and the three
additional site-interface consumers unchanged, ten consumers in total. Their
sources still match the shared repository. The exact audit is reproduced in the
change record; temporary validation modules are removed from the packet.

## Proved and sorry left

Closed the sole original hole:
`WeilConjectures.finiteHomEtaleRepresentativeData_existsUnique`
(node `def-sf-etale-finite-coefficient-hom-arrow`). No holes added; zero remain
in the item. Both new private helper theorems are fully proved. The extended
native record and the source wrapper, generic specializations and projections contain real
data and no holes.

Transitive axiom inspection still reports `sorryAx` from existing imported
dependencies, alongside `propext`, `Classical.choice` and `Quot.sound`.

## No longer needed

None. No imports removed and no nodes or modules pruned. The existing imports
provide data used by the public definitions. The node has no proof dependencies;
the construction follows its existing representative-data clause without adding
any dependency.

## Where the brief, the DAG or earlier work was wrong

The previous node proof explicitly described representative-data existence and
uniqueness as open. This delivery completes it by tensor-family equality
elimination and dependent field extensionality. No mathematical correction was
needed. The argument imposes no conditions on coefficient levels, complexes,
sections, or the scheme beyond those in the existing statement, so zero objects
and the empty scheme require no special case.

## Second reading by Y3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
