# Stage-1 report: lem-sfb-profinite-action-finite-cover-site

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-profinite-action-finite-cover-site.json — statement, split. Seven proof steps; no whole-item Mathlib match. Existing searches are retained and the seven searches actually run for Q94 are appended with their actual logged results.
- citations.json — one verbatim statement excerpt for every node used in every proof step.
- report.md — this report. searches.jsonl is the required search command's own log.

No new nodes; no new Mathlib leaves. No Lean source or repository file was written, no compiler/build command was run, and no agent was started.

## Attachments

None. Searches of lean/WeilConjectures for the exact blueprint tag, profinite actions, and finite covering sites found no declaration stating the item. The discrete continuous-action orbit decomposition is about discrete spaces and does not supply this result. Mathlib's ContAction defines the relevant kind of action; it does not prove this entire action-site statement.

## WANTED

WANTED: a non-SGA reference giving the finite-cover profinite continuous-action site and its subcanonicity, for lem-sfb-profinite-action-finite-cover-site. The imported source explicitly says that the auxiliary result is agent-formulated, and paragraph (3) of the current direct-images proof contains no such theorem. Accordingly proof_origin.by is agent. The elementary topological inputs have existing cited nodes and local Stacks/Mathlib sources, so the missing external exposition does not leave a proof gap.

## What changed and what was wrong

The imported node had a statement and searches but no proof. I supplied the actual construction of an action on any underlying finite limit, the individual covering axioms, and finite-family continuous descent followed by equivariance. I retained every statement clause and hypothesis. I corrected doubled TeX backslashes in the statement; this is a rendering repair, with no mathematical change and no STATEMENT-DISPUTED issue.

The node has an inherited null blueprint ancestor and a long via chain ending in the auxiliary direct-image infrastructure. The required ancestor command itself prints None. I retained that provenance instead of inventing an ancestor. I read the fixed chapter and unit records and the current main-20261015 paragraph (3). This split supplies only the topological infrastructure already requested by that route; it does not replace the unit's direct-image argument or introduce any coefficient-category identification.

## Not duplicates

No node was created. Whole-DAG searches by profinite limits, subcanonical topology, quotient maps, and compact Hausdorff surjections, together with whole-blueprint searches for profinite action, finite jointly surjective, finite-cover, profinite limits and subcanonical, led to reuse of the existing topology nodes. In particular I did not create another compact-surjection quotient lemma, profinite fibre-product lemma, or finite-limit criterion. The only blueprint subcanonical hit concerns scheme pro-etale sites, not profinite action spaces.

## Repair review

The returned landing failure was a live-DAG promotion mismatch, so I rebased the split against the current live node and reread all cited statements: `def-weil-size-convention`, `lem-sfb-finite-quotient-fiber-product`, `lem-weil-pbc-finite-limits-from-terminal-pullbacks`, `lem-sfb-profinite-topological-limits`, `def-weil-pbc-sites-and-cohomology`, `lem-sfb-compact-hausdorff-surjection-quotient`, and `def-sfb-profinite-action-parameters`. Their quoted statements are unchanged and still say exactly what the proof takes from them. The repaired proof now writes the unit and multiplication equations separately via limit uniqueness and explicitly checks closure under bijective reindexing, which the live site convention requires. The item statement, hypotheses, objects, statement dependencies, and proof route remain unchanged.

## Review by Q94

I read the item's imported statement and its source file, literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability-direct-images.proof.md, especially paragraph (3). It asserts the direct-image route, not this auxiliary theorem; I therefore take responsibility for the action-site proof as an agent proof. There are no new nodes whose sources need separate review.

For step 1 I opened def-weil-size-convention, lem-sfb-finite-quotient-fiber-product, and lem-weil-pbc-finite-limits-from-terminal-pullbacks. The first permits larger-universe small skeletons. The fibre-product node explicitly states that the set of pairs over the base, with its subspace topology, is compact Hausdorff totally disconnected; I use only that assertion, not its finite-partition proof. The maps in our spans are continuous between profinite spaces in the stipulated smaller universe. The criterion states both existence from terminal objects and pullbacks, and preservation by functors preserving them. I read Stacks categories.tex, Tag 002O, lemma-finite-limits-exist, and topology.tex Tags 08ZY and 0A2P; the pair-map universal property is written in the step. The off-unit fibre-product theorem is a generic topological tool, and is declared in split_report.tool_uses. The criterion itself is a Mathlib leaf.

For step 2 I opened lem-sfb-profinite-topological-limits. Its statement, unlike a mere underlying-set preservation result, expressly permits every topological test space W and requires no compactness or separation of W. This licenses W = J times L to construct a jointly continuous action, rather than only a separately continuous one. Each coordinate action is continuous, and equivariance of the diagram gives compatibility. Projection uniqueness proves the action axioms and equivariance of every mediating map; it also proves uniqueness of the lifted action, which is needed for creation rather than just preservation. I read the recorded Mathlib source Profinite/Basic.lean at the limit construction and lines 214–218. This is a Mathlib leaf, so it is a tool regardless of its unit.

Step 3 is an elementary unpacking of the constructed limits. I checked the equalizer uses the pullback of (f,h) and the diagonal into Y times Y, with explicit continuous inverse maps to the equalizer subspace. Invariance of that subspace is the displayed equation using equivariance of f and h. No closed-subspace theorem is being silently added here: profiniteness comes from the already established pullback.

Step 4 uses exactly the covering axioms written in def-weil-pbc-sites-and-cohomology(1), not an unrelated definition of a scheme site. It verifies each by lifting individual points, and checks finiteness of indexed composition and the empty family. These are elementary set calculations with the pullbacks constructed in earlier steps; there is no unproved stability theorem in the step.

Step 5 uses the statement of lem-sfb-compact-hausdorff-surjection-quotient, applied with whole-space subsets. I read topology.tex Tags 08YD (lemma-closed-map) and 0AAU (lemma-closed-morphism-quotient-topology), and the exact recorded Mathlib theorem at Topology/Separation/Hausdorff.lean:682–684. The finite disjoint union is compact by the explicit finite-subcover argument; the base T is Hausdorff; q is continuous and surjective by its component maps and the covering hypothesis. Thus every hypothesis of the quotient criterion holds. The proof writes out independence of lifts, continuity via inverse images of open sets, and uniqueness. No claim that covers admit sections or are open is used.

Step 6 adds equivariance by evaluating the descended map at g times a chosen lift, not by assuming underlying descent automatically respects actions. The sheaf equalizer criterion is exactly the clause in def-weil-pbc-sites-and-cohomology(1) quoted in citations.json. Therefore the obtained bijection proves representables are sheaves. The step also checks the empty-family equalizer explicitly. Step 7 uses the actual trivial-action functor in def-sfb-profinite-action-parameters and clause (2) of the finite-limit criterion: terminal objects and pullbacks have trivial induced actions. Cover preservation is the unchanged underlying family.

I tested the proof on the trivial group (it reduces to the ordinary profinite site), singleton spaces, empty spaces, disjoint images in a pullback (empty pullback), parallel maps with empty equalizer, identity covers, empty cover of the empty object, and nonempty finite families of empty sources over the empty object. For a nonempty target a family of empty sources is not a cover, so it never enters the descent assertion. An empty target U causes no false existence assertion: matching families to U can only occur when every covering source is empty, hence when T is empty. No nonemptiness or surjectivity hypothesis has been added to a general span or to a diagram.

I checked delivery-errors B–E against the node and the sources: there are no new statement-only nodes, duplicate nodes, invented searches, or clauses moved into replacement nodes; every non-elementary input has an actual cited statement. All seven local searches were read, including the ordinary Profinite effective-epi-family hit and the ContAction definition. Neither is the whole equivariant site theorem, and no service failure was presented as absence. Every proof dependency is the union of the step uses; every citation quote is copied verbatim from the cited statement. I checked that none of the four substantive theorem dependencies reaches this item, avoiding a cycle. All proof steps are below 2000 characters and contain their stated elementary calculations rather than a concealed lemma. No SGA source is cited.

## Unfinished work

None in the split. Server dry run and delivery are recorded below when completed.
