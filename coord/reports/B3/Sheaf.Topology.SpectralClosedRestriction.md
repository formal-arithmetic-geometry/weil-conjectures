## What changed

The original theorem `TopCat.spectral_closed_restriction` is now proved from a
complete injectivity argument and one strictly smaller surjectivity statement.
The target signature is unchanged. A private, fully proved helper
`TopCat.restriction_eq_implies_germ_eq` identifies equality of restricted
sections with equality of original germs at points of the subset. It uses the
presheaf pullback stalk isomorphism, the sheafification stalk isomorphism, and
`Adjunction.unit_leftAdjointUniq_hom_app` to connect the abstract sheaf pullback
unit to the constructed unit. The injectivity argument then uses nonemptiness
from connectedness, `specializes_iff_mem_closure`, `germ_eq`, and `section_ext`.

All files compile locally through `lcompile.py --all`. The one new module
contains the surjectivity argument of Stacks Tag 09ZG as a named statement and
complete proof in words, so that it can be proved as the next item.

## Proved and sorry left

The sole original sorry of `TopCat.spectral_closed_restriction` is replaced by
a complete Lean proof from a smaller named statement. Its injectivity half and
the private germ-comparison helper are proved directly from Mathlib without
any sorry dependency. The only sorry added by this delivery is
`TopCat.spectral_closed_restriction_surjective`, with node
`lem-weil-pbc-h0-spectral-closed-restriction-surjective`.

## No longer needed

Removed direct imports from the original module:
`Sheaf.Topology.ClosedPushforwardConstantRestriction`,
`Sheaf.Topology.SheavesDirectedColimitSections`,
`Sheaf.Topology.SpectralClosedClopenDecompositionLift`,
`Sheaf.Topology.SpectralClosedSubspace`, and
`Sheaf.Topology.SpectralSheafColimitConstantEmbeddings`.

These remain imports of the new surjectivity module, whose unresolved proof
uses them; none of their nodes is pruned from the overall target closure.
The filtered-colimit elementwise node is not needed for the proved injectivity
half, because Mathlib `germ_eq` and `section_ext` already supply the required
neighbourhood and sheaf separation arguments. It remains part of the
surjectivity plan. No unit statement or unit proof step was bypassed.

## Where the brief, the DAG or earlier work was wrong

No mathematical error was found. The direct Mathlib proof of injectivity is
shorter than following the planned stalk and separation nodes as new lemmas.
The surjectivity argument still needs the finite-constant, subsheaf-gluing,
and filtered-colimit steps recorded in the original DAG.

The dry-run preflight currently requires `## Earlier second reading (a previous round; superseded)`, although
the worker brief explicitly assigns that section to a second reader and says
not to write it. This worker does not impersonate that reader.

## New nodes

`lem-weil-pbc-h0-spectral-closed-restriction-surjective`, in
`dag/nodes/sec-proper-base-change/`, isolates exactly the surjectivity half of
Stacks Tag 09ZG. It carries the original proof steps for finite constants,
products of closed direct images, subsheaf gluing, and directed colimits. Its
Lean module is `Sheaf.Topology.SpectralClosedRestrictionSurjective`. For empty
ambient spaces the claim is the unique-section assertion on the empty open;
for nonempty ambient spaces connectedness includes nonemptiness of each
intersection with a point closure. No new definition or statement change is
made, and there is no change record.

## Second reading by B3

1. I compared `lean/Sheaf/Topology/SpectralClosedRestriction.lean` with the repository version. The public target declaration has the same signature, including all hypotheses and its conclusion. The added surjectivity module is the explicitly split statement recorded by its new DAG node; no existing definition or target statement was changed.

2. I compiled both delivered modules with `lcompile.py --all`. They compile without errors. The injectivity proof has no `sorry`, `axiom`, `unsafe`, `opaque`, `extern`, or `implemented_by`; the only remaining `sorry` is the named public theorem `TopCat.spectral_closed_restriction_surjective`, whose source, proof plan, and node are recorded above. The private helper is a proved stalk comparison, and its use of Mathlib is kernel-checked.

3. I checked the new surjectivity statement against the original Stacks Tag 09ZG argument and the target's hypotheses. It is exactly the surjectivity component of the original restriction map, with no added hypothesis or weakened conclusion. The node is new, has its source, proof steps, searches, Lean declaration, and split status, and is not a restatement used to fake the target: the target's injectivity is proved independently and invokes this strictly smaller conclusion only for the missing half.

4. I checked the proof route and imports. The injectivity route uses the Mathlib stalk pullback and sheafification isomorphisms, `germ_eq`, `specializes_iff_mem_closure`, and `section_ext`; it does not need the finite constant, subsheaf, or filtered-colimit modules. Those imports were removed from the target module and remain only in the unresolved surjectivity module, where the DAG route still requires them. The unit's statement and route are retained, with the surjectivity steps isolated in the new node.

5. I checked that the DAG proof and dependencies match the Lean proof: the target node records the two Mathlib/library dependencies for injectivity and the new surjectivity node for the second conjunct; the new node records the five original surjectivity steps and their dependencies. No additional statement or definition was needed, and no existing declaration was found by the recorded Mathlib/library searches.

I added this second-reading record and made no proof changes after the clean local compilation.
