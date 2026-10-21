## What changed

Executed the listed retirement of
Sheaf.Algebra.Homology.LocalizedTensorComparisonDerivedArrow. Its complete
upstream twin proves the same arrow-functor conclusion without the unused
flatness hypothesis. Withdrew the duplicate via deleted.txt, redirected the only
direct consumer LocalizedTensorComparisonClosureRetractCore to upstream, and
adapted its theorem call. A lambda consumes its retained hC hypothesis; its
public signature and other proof steps are identical. Reattached the existing
DAG node to the upstream declaration and recorded its exact signature.
No upstream file or target statement was changed.

Change record: coord/changes/B6-retire-localized-tensor-comparison-derived-arrow.md.

Return repair (reviewer C-997a7, returned head 997a7a91ef): compared the
retained packet with the current sheaf-dag sources. The adapted consumer still
differs only in its proof import and the specialization call; the node differs
only in its Lean attachment. The listed retirement and B6 claim remain current.
The delivery tool constructs the replacement commit on freshly fetched sheaf-dag.

Validation on this repair: lcompile.py --all compiled the adapted direct consumer
successfully (7.7 s); a second run compiled it and the unchanged transitive
consumer in import order (8.6 s total), without warnings. The transitive copy was
removed after verification and is not delivered. The adapted file has zero sorry
tokens and no lines over 100 characters.

## Proved and sorry left

Original item: zero direct holes. Closed zero holes; added zero; left zero in
the retired item and adapted consumer. This is duplicate retirement, not a new
proof or a decomposition. ModuleCat.exists_localizedTensorComparison_derived_arrow
remains completely proved upstream; the consumer's
ModuleCat.localizedTensorComparisonProperty_retract_core keeps its complete proof.
No new nodes or statements are introduced.

## No longer needed

Retired Sheaf.Algebra.Homology.LocalizedTensorComparisonDerivedArrow and removed
its sole proof-only import from
Sheaf.Algebra.Homology.LocalizedTensorComparisonClosureRetractCore. The duplicate
private acyclic_tensor_of_kFlat helper disappears with its module; the upstream
original remains unchanged. No mathematical node or proof dependency is pruned:
lem-pc-localized-tensor-comparison-derived-arrow now points to upstream, and its
unfinished or proved parents retain the same logical dependency. The underlying
K-flat, naturality, scalar-extension and model-independence theory remains needed.
No other module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The generic brief describes an unfinished proof, but the current item already
has a complete proof, and coord/retire-items.tsv explicitly assigns its retirement.
The upstream API drops hC, so changing only the import would misapply the theorem.
Its conclusion and all other binders agree, and specialization preserves the
consumer's exact public statement. No false mathematical statement was found.
The unit route is preserved, and logical parents use the reattached node.

The previous landing failed while opening KunnethMapAgrees.lean, not while
checking this proof. Its current coord/rework.tsv row points to the preserved
quarantine/Sheaf/AlgebraicGeometry/KunnethMapAgrees.lean archive. That module is
not an importer of the retired item; its archive, Lean attachment and dependency
records are preserved. It is neither restored nor withdrawn by this delivery.
The current live and quarantined source searches confirm the same sole direct
importer of the item. The mathematical parent continues to cite the same node,
now attached to the upstream theorem; the unit route remains unchanged.

## Forced adaptations

LocalizedTensorComparisonClosureRetractCore is the only direct importer
(unclaimed in the inspected snapshot). Its import must migrate because its
former module is explicitly withdrawn in this packet. The old call passes hC
where upstream expects hQ, so the argument would have the wrong type after import
migration. Changed import line 6 and the obtain call at line 84 to use upstream's
argument list through the displayed specialization lambda. No other lines,
signatures or visibility change. LocalizedTensorComparisonClosureRetract is a
transitive consumer and needs no source adaptation.

## Second reading by B6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
