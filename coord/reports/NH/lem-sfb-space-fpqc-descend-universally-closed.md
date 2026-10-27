## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-space-fpqc-descend-universally-closed.json`: statement, split into five proof steps; no Mathlib match for the algebraic-space statement.
- `citations.json`: one verbatim statement quotation for each citation in each proof step.

No new DAG nodes or new Mathlib leaves. The statement, statement dependencies, source, and existing blueprint provenance are unchanged. Existing searches were retained; the current item's relevant logged searches were appended. Exploratory searches for possible supporting nodes remain in `searches.jsonl`; none resulted in an unnecessary node.

## Attachments

None. Searching `lean/WeilConjectures/` by the item id, `AlgebraicSpace`, and `algebraic space` found no declaration for this item. The scheme-only universal-closedness declarations do not cover its algebraic-space source or algebraic-space base changes.

## WANTED

None. All mathematical sources used were available locally.

## Findings and changes

The live item had a correct statement and no proof. I read Stacks `spaces-descent.tex`, Tag 041O, `lemma-descending-property-universally-closed`, and followed its point-lifting / quotient-topology argument. I also read `spaces-properties.tex`, Tags 03H4 (`lemma-points-cartesian`) and 03BX (`lemma-topology-points`), `spaces-morphisms.tex`, Tag 03IT (`lemma-universally-closed-local`), and `topologies.tex`, Tag 022D (`lemma-fpqc`), part (3). No statement correction or dispute is needed.

The source reduces through a general fpqc locality criterion to a single affine flat surjection. Here the finite family refinement can be avoided by using the existing arbitrary-target continuous-map sheaf Mathlib leaf. Applying it to the explicit two-point topology gives exactly the quotient-topology implication the source needs, for the full covering family. This is a supporting topological tool below the node, preserving the descent argument. It assumes no quasi-compactness of any individual covering map. No SGA source is used.

The latest blueprint chapter and unit, and `sk-thm-sf-ctf-stability-direct-images.proof.md` (whose `of` is `det-thm-sf-ctf-stability-direct-images`), were read. The current direct-image proof uses compactification. This item remains the historical supporting descent input of its existing `blueprint.from` chain; it replaces no unit step. The ancestor command reports `None`, matching the inherited provenance. I did not invent an ancestor or alter the fixed unit/chapter records.

## Searches and reused nodes

I searched the whole DAG by statements, key words, and the source tags, and ran `blueprint_refs.py search` for `submersive`, `universally closed`, `closed scheme`, `fpqc`, `quotient topology`, and `quotient map`. I read the candidate nodes, not merely their search hits. In particular:

- `lem-a1-space-fibre-product-point` has two scheme sources. The proof respects that restriction: the algebraic-space point is first represented by a map from `Spec K`; the lemma is then applied to `Spec K` and the scheme chart.
- `lem-trf-space-fibre-products-etale-covers` supplies the categorical fibre-product universal property. Reassociation in step 3 is its elementary universal-property consequence.
- `lem-weil-pbc-fpqc-covering-axioms`, part (3), is exactly scheme-base-change stability. I did not apply it to an algebraic-space base.
- `lem-weil-pbc-flat-qc-surjective-quotient-map` applies to a single scheme map, and `lem-weil-pbc-standard-fpqc-quotient-topology` assumes a finite affine family with a faithfully flat product map. Neither was falsely applied to the original arbitrary covering family.
- `lem-sfb-set-continuous-functions-fpqc-sheaf` allows **any** topological target, with no separation assumption. I read its exact Mathlib declaration `AlgebraicGeometry.isSheaf_fpqcTopology_continuousMapPresheaf`, `Mathlib/AlgebraicGeometry/Sites/ConstantSheaf.lean:68-85`, and the presheaf definition at lines 44-46. There is no `T2Space` or total disconnectedness hypothesis. This existing leaf eliminates the proposed new covering-topology node.

Actual `msearch.py` calls include semantic searches in two phrasings, Loogle, and source grep. `UniversallyClosed.lean:35-41` and `FlatDescent.lean:48-62` were read: their candidates concern schemes. The qualified Loogle query `AlgebraicGeometry.Flat, Topology.IsQuotientMap` finds the already-existing single-map leaf in `Flat.lean:124-126`; the earlier unqualified query returned an unknown-identifier diagnostic, retained as such in the log. The family-topology searches found the fpqc precoverage definitions, not an exact family closed-subset theorem. I then reused the stronger existing sheaf leaf rather than creating a node for its elementary Sierpinski consequence.

## Not duplicates

No new nodes. The image identity is a short application of the existing point-lifting lemma and the universal property, so it is a proof step. The Sierpinski specialization is a short use of the existing continuous-map sheaf theorem and the covering definition, so it too is a proof step. Neither is introduced as a new lemma node.

## Review by NH

I checked the statement against Tag 041O: the source allows arbitrary algebraic spaces and arbitrary fpqc families, and in particular the scheme target and scheme cover of this item. Its proof does not require finiteness or separation hypotheses on the map being descended. I kept the item's full algebraic-space-base-change meaning of universally closed, rather than silently testing only scheme base changes.

In step 1, I checked the last sentence of `lem-a1-space-affine-etale-cover`: it asserts continuity for *every* map from a scheme into an algebraic space, not just etale maps. Composing each etale test map into the source with the given morphism therefore gives continuity into its target. `def-a1-space-point-topology` supplies precisely the final topology needed to conclude continuity of the arbitrary space morphism. The only inference here is the definition of a final topology and the inverse-image rule for closed sets.

In step 2, I checked both cited statements against every object: `lem-trf-space-fibre-products-etale-covers` gives the algebraic-space fibre product and its universal property, while `lem-a1-space-fibre-product-point` applies with target Z and **scheme** sources `Spec K` and U. The selected representative maps to the original point e under field extension, so the resulting point in the space fibre product lies over both e and u. This proves the reverse inclusion in the displayed image identity; the other inclusion is commutativity. No bijection between point sets of fibre products and fibre products of point sets is asserted.

In step 3, the only base to which the scheme covering axiom is applied is U, with the scheme morphism U to T. Thus each U_i is a scheme and the family is fpqc, exactly part (3) of the cited statement. I checked the universal-closedness clause of `def-sfb-space-morphism-properties` against the morphism U_i to T_i: it gives closedness of the base change of the assumed universally closed f_i. Reassociation with `X times_T U_i` is the fibre-product universal property, not an unstated representability theorem. Step 1 gives closedness of the pulled-back C_i. Step 2 gives the exact inverse-image/image equality used to obtain closed inverse images of A_U.

In step 4, I explicitly checked the topology on D and the direction of the characteristic function: D has opens empty, {0}, and D; chi is 1 on A_U. Therefore continuity is equivalent to the complement of A_U being open. The cited sheaf statement provides a continuous global function from the matching continuous local functions. They match because both pull back the same set function on U. The cited covering definition asserts joint surjectivity, so the glued function equals chi at every point. This is why the non-Hausdorff target is essential, and why a theorem limited to Hausdorff or totally disconnected targets would not suffice. The existing Mathlib leaf explicitly permits this target.

In step 5, the image identity is applied to every etale scheme test of Z. Closed inverse images give a closed subset by taking complements in the exact topology definition; no image of a closed subset along a merely continuous map is assumed closed. Finally Z was an arbitrary algebraic-space base change and C an arbitrary closed subset, so the conclusion is exactly the universal-closedness definition.

I tested the empty space X, empty closed C, empty chart U, and empty index family. An empty fpqc family forces T empty by joint surjectivity, so the argument remains valid; a scheme over empty T and every algebraic space mapping to it have empty point sets. The sheaf matching family can then be empty. Non-quasi-compact covering maps and non-quasi-separated algebraic spaces cause no change: only schemes U_i, field representatives, and atlas final topologies enter the argument. All steps are below 2000 characters. All sources and used statement clauses are open/read and recorded in `citations.json`. B--E checks found no hollow construction, statement-only-node violation, unrecorded claim, hidden large lemma, off-route replacement, or strengthened hypothesis. The initial concern about using a two-scheme-source point lemma for a space source was repaired by the explicit `Spec K` specialization; the possible unnecessary new quotient-topology node was removed before creation.

Off-unit uses are declared in `split_report.tool_uses`: the shared topology, point-lifting, fibre-product, and scheme-covering facts are general foundational tools. The continuous-map sheaf result is already a Mathlib leaf in this unit.

## Unfinished work

None at the stage-1 split level. No Lean code was written and no compiler, Lake, or build was run. Delivery checks and the push are performed by the required delivery tool.
